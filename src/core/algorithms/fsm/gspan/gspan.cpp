
#include "gspan.h"

#include <algorithm>

#include <boost/functional/hash.hpp>
#include <boost/range/iterator_range.hpp>

#include "core/config/option_using.h"
#include "core/util/logger.h"
#include "graph_parser.h"
#include "sparse_triangular_matrix.h"
#include "subgraph_miner.h"
#include "utils.h"
using namespace gspan;

namespace algos {

GSpan::GSpan() : Algorithm() {
    RegisterOptions();
    MakeOptionsAvailable({config::names::kGraphDatabase, config::names::kGSpanMinimumSupport,
                          config::names::kOutputSingleVertices, config::names::kMaxNumberOfEdges,
                          config::names::kGSpanOutputPath});
}

void GSpan::MakeExecuteOptsAvailable() {
    using namespace config::names;
    MakeOptionsAvailable(
            {kGSpanMinimumSupport, kOutputSingleVertices, kMaxNumberOfEdges, kGSpanOutputPath});
}

void GSpan::RegisterOptions() {
    DESBORDANTE_OPTION_USING;

    auto check_minsup = [](double val) {
        if (val <= 0 || val > 1) {
            throw config::ConfigurationError(
                    "Minimum support must be a value between 0 (exclusive) and 1 (inclusive).");
        }
    };

    auto check_max_edges = [](int val) {
        if (val <= 0) {
            throw config::ConfigurationError("Maximum number of edges must be a positive integer.");
        }
    };

    RegisterOption(config::Option{&graph_database_path_, kGraphDatabase, kDGraphDatabase});
    RegisterOption(config::Option{&min_frequency_, kGSpanMinimumSupport, kDGSpanMinimumSupport}
                           .SetValueCheck(check_minsup));

    RegisterOption(config::Option{&output_single_vertices_, kOutputSingleVertices,
                                  kDOutputSingleVertices, true});
    RegisterOption(
            config::Option{&max_number_of_edges_, kMaxNumberOfEdges, kDMaxNumberOfEdges, INT_MAX}
                    .SetValueCheck(check_max_edges));

    RegisterOption(config::Option{&output_path_, kGSpanOutputPath, kDGSpanOutputPath,
                                  std::filesystem::path{}});
}

void GSpan::LoadDataInternal() {
    std::ifstream f(graph_database_path_);
    raw_dataset_ = gspan::parser::ReadGraphs(f);
    pruned_graphs_ = raw_dataset_;
}

void GSpan::ResetState() {
    pruned_graphs_ = raw_dataset_;
    pruned_csr_graphs_.clear();
    frequent_subgraphs_.clear();
    frequent_vertex_labels_.clear();
}

void GSpan::ExecuteInternal() {
    min_sup_ = static_cast<int>(std::ceil(min_frequency_ * raw_dataset_.size()));

    Launch();
    LOG_DEBUG("Mining complete: {} frequent subgraphs found", frequent_subgraphs_.size());

    if (!output_path_.empty()) {
        gspan::parser::WriteGraphs(output_path_, frequent_subgraphs_);
        LOG_INFO("Wrote {} frequent subgraphs to {}", frequent_subgraphs_.size(),
                 output_path_.string());
    }
}

void GSpan::Launch() {
    LOG_INFO("Starting GSpan algorithm: {} graphs, min_sup_={}", raw_dataset_.size(), min_sup_);

    LOG_DEBUG("Searching for frequent vertex labels");
    FindAllOnlyOneVertex();
    LOG_DEBUG("Found {} frequent vertex labels", frequent_vertex_labels_.size());

    LOG_DEBUG("Pruning infrequent vertex pairs and edge labels");
    RemoveInfrequentVertexPairs();
    LOG_DEBUG("Pruning complete");
    CompactIds();

    pruned_csr_graphs_.reserve(pruned_graphs_.size());
    for (auto const& graph : pruned_graphs_) {
        pruned_csr_graphs_.push_back(ConvertToCSR(graph));
    }

    ProjectionMap embeddings = GetInitialEdges();
    for (auto const& [ee, proj] : embeddings) {
        SubgraphMiner miner(pruned_csr_graphs_, min_sup_, max_number_of_edges_);
        miner.MineFromSeed(proj, ee);
        auto& results = miner.GetFrequentSubgraphs();
        frequent_subgraphs_.insert(frequent_subgraphs_.end(), results.begin(), results.end());
    }

    LOG_INFO("GSpan complete: {} frequent subgraphs found", frequent_subgraphs_.size());
}

void GSpan::CompactIds() {
    for (auto& graph : pruned_graphs_) {
        int vertex_id = 0;
        for (auto vertex : boost::make_iterator_range(boost::vertices(graph))) {
            graph[vertex].id = vertex_id;
            vertex_id++;
        }

        int edge_id = 0;
        boost::unordered_flat_set<int> processed;

        for (auto edge : boost::make_iterator_range(boost::edges(graph))) {
            int orig_id = graph[edge].id;
            if (processed.contains(orig_id)) {
                continue;
            }

            processed.insert(orig_id);

            vertex_t source = boost::source(edge, graph);
            vertex_t target = boost::target(edge, graph);

            graph[edge].id = edge_id;

            auto [twin, _] = boost::edge(target, source, graph);
            graph[twin].id = edge_id;
            edge_id++;
        }
    }
}

ProjectionMap GSpan::GetInitialEdges() {
    ProjectionMap result;
    for (size_t i = 0; i < pruned_csr_graphs_.size(); i++) {
        auto const& graph = pruned_csr_graphs_[i];
        for (auto v1 : boost::make_iterator_range(boost::vertices(graph))) {
            for (auto edge : boost::make_iterator_range(boost::out_edges(v1, graph))) {
                vertex_t v2 = boost::target(edge, graph);
                int source_label = graph[v1].label;
                int target_label = graph[v2].label;
                // Partial pruning: if the first label is greater than the
                // second label, then there must be another graph whose second
                // label is greater than the first label.
                if (source_label <= target_label) {
                    ExtendedEdge ee = ExtendedEdge(Vertex(0, source_label), Vertex(1, target_label),
                                                   graph[edge].label);
                    result[ee].emplace_back(i, edge, nullptr);
                }
            }
        }
    }
    return result;
}

void GSpan::RemoveInfrequentLabel(gspan::graph_t& graph, int label) {
    std::vector<vertex_t> vertices_to_remove;
    for (auto vertex : boost::make_iterator_range(boost::vertices(graph))) {
        if (graph[vertex].label == label) {
            vertices_to_remove.push_back(vertex);
        }
    }
    // Sort in descending order to prevent invalidating descriptors (indices) of subsequent vertices
    std::sort(vertices_to_remove.rbegin(), vertices_to_remove.rend());
    for (auto vertex : vertices_to_remove) {
        boost::clear_vertex(vertex, graph);
        boost::remove_vertex(vertex, graph);
    }
}

void GSpan::RemoveInfrequentVertexPairs() {
    boost::unordered_flat_set<std::pair<int, int>, boost::hash<std::pair<int, int>>>
            already_seen_pair;
    SparseTriangularMatrix matrix;
    boost::unordered_flat_set<int> already_seen_edge_label;
    boost::unordered_flat_map<int, int> edge_label_to_support;

    // Calculate the support of each entry
    for (graph_t& graph : pruned_graphs_) {
        for (auto v1 : boost::make_iterator_range(boost::vertices(graph))) {
            int v1_label = graph[v1].label;
            for (auto edge : boost::make_iterator_range(boost::out_edges(v1, graph))) {
                vertex_t v2 = boost::target(edge, graph);
                int v2_label = graph[v2].label;

                // Update vertex pair count
                auto pair = std::minmax(v1_label, v2_label);
                bool seen = already_seen_pair.contains(pair);
                if (!seen) {
                    matrix.IncrementCount(v1_label, v2_label);
                    already_seen_pair.insert(pair);
                }

                // Update edge label count
                int edge_label = graph[edge].label;
                if (!already_seen_edge_label.contains(edge_label)) {
                    already_seen_edge_label.insert(edge_label);
                    edge_label_to_support[edge_label]++;
                }
            }
        }
        already_seen_pair.clear();

        already_seen_edge_label.clear();
    }

    LOG_TRACE("Removing infrequent vertex pairs from support matrix");
    matrix.RemoveInfrequent(min_sup_);

    // Remove infrequent edges
    for (gspan::graph_t& graph : pruned_graphs_) {
        boost::remove_edge_if(
                [&](gspan::edge_t e) {
                    auto v1 = boost::source(e, graph);
                    auto v2 = boost::target(e, graph);
                    int label1 = graph[v1].label;
                    int label2 = graph[v2].label;
                    int count = matrix.GetSupport(label1, label2);

                    if (count < min_sup_) {
                        return true;
                    }
                    if (edge_label_to_support[graph[e].label] < min_sup_) {
                        return true;
                    }
                    return false;
                },
                graph);

        // Remove isolated vertices
        std::vector<vertex_t> isolated;
        for (auto vertex : boost::make_iterator_range(boost::vertices(graph))) {
            if (boost::out_degree(vertex, graph) == 0) {
                isolated.push_back(vertex);
            }
        }
        std::sort(isolated.rbegin(), isolated.rend());
        for (auto vertex : isolated) {
            boost::clear_vertex(vertex, graph);
            boost::remove_vertex(vertex, graph);
        }
    }
}

// This method finds all frequent vertex labels from a graph database.
void GSpan::FindAllOnlyOneVertex() {
    LOG_DEBUG("Collecting vertex label statistics");

    // Create a map (key = vertex label, value = graph ids)
    // to count the support of each vertex
    boost::unordered_flat_map<int, boost::unordered_flat_set<int>> label_map;

    for (size_t i = 0; i < pruned_graphs_.size(); i++) {
        auto const& graph = pruned_graphs_[i];
        for (auto vertex : boost::make_iterator_range(boost::vertices(graph))) {
            if (boost::out_degree(vertex, graph) != 0) {
                int label = graph[vertex].label;
                label_map[label].insert(i);
            }
        }
    }
    LOG_DEBUG("Found {} distinct vertex labels", label_map.size());

    for (auto [label, temp_sup_g] : label_map) {
        int sup = temp_sup_g.size();
        if (sup >= min_sup_) {
            frequent_vertex_labels_.push_back(label);
            LOG_TRACE("Vertex label {} is frequent (support={})", label, sup);

            if (output_single_vertices_) {
                DFSCode temp;
                temp.Add(ExtendedEdge(Vertex(0, label), Vertex(0, label), -1));
                frequent_subgraphs_.emplace_back(frequent_subgraphs_.size(), temp,
                                                 TranslateToOriginalIds(temp_sup_g, pruned_graphs_),
                                                 sup);
            }
        } else {
            LOG_TRACE("Removing infrequent vertex label {} (support={})", label, sup);
            for (int graph_id : temp_sup_g) {
                gspan::graph_t& graph = pruned_graphs_[graph_id];
                RemoveInfrequentLabel(graph, label);
            }
        }
    }

    LOG_DEBUG("Vertex label analysis complete: {} frequent labels", frequent_vertex_labels_.size());
}

}  // namespace algos
