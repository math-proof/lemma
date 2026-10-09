#include "chu_liu_edmonds.h"
#include "../matrix.h"

bool _find_cycle(VectorI &parents, int length, vector<bool> &current_nodes,
		VectorI &ret) {
//	Timer timer(__PRETTY_FUNCTION__);
	vector<bool> added(length);

	added[0] = true;
//	print(added);

	std::set<int> cycle;
	auto has_cycle = false;
	for (int i = 1; i < length; ++i) {
		if (has_cycle)
			break;
//        # don't redo nodes we've already
//        # visited or aren't considering.
		if (added[i] or !current_nodes[i])
			continue;
//        # Initialize a new possible cycle.
		std::set<int> this_cycle = { i };
		added[i] = true;
		has_cycle = true;
		auto next_node = i;

		while (!this_cycle.count(parents[next_node])) {
			next_node = parents[next_node];
//            # If we see a node we've already processed,
//            # we can stop, because the node we are
//            # processing would have been in that cycle.
			if (added[next_node]) {
				has_cycle = false;
				break;
			}
			added[next_node] = true;
			this_cycle.insert(next_node);
		}

		if (has_cycle) {
			auto original = next_node;
			cycle.insert(original);
			next_node = parents[original];
			while (next_node != original) {
				cycle.insert(next_node);
				next_node = parents[next_node];
			}
			break;
		}
	}

	ret = list(cycle);
	return has_cycle;
}

void chu_liu_edmonds(int length, Matrix &score_matrix,
		vector<bool> &current_nodes, dict<int, int> &final_edges,
		MatrixI &old_input, MatrixI &old_output,
		vector<std::set<int>> &representatives) {
//	Timer timer(__PRETTY_FUNCTION__);
	/*
	 Applies the chu-liu-edmonds algorithm recursively
	 to a graph with edge weights defined by score_matrix.

	 Note that this function operates in place, so variables
	 will be modified.

	 Parameters
	 ----------
	 length : ``int``, required.
	 The number of nodes.
	 score_matrix : ``numpy.ndarray``, required.
	 The score matrix representing the scores for pairs
	 of nodes.
	 current_nodes : ``List[bool]``, required.
	 The nodes which are representatives in the graph.
	 A representative at it's most basic represents a node,
	 but as the algorithm progresses, individual nodes will
	 represent collapsed cycles in the graph.
	 final_edges: ``Dict[int, int]``, required.
	 An empty dictionary which will be populated with the
	 nodes which are connected in the maximum spanning tree.
	 old_input: ``numpy.ndarray``, required.
	 old_output: ``numpy.ndarray``, required.
	 representatives : ``List[Set[int]]``, required.
	 A list containing the nodes that a particular node
	 is representing at this iteration in the graph.

	 Returns
	 -------
	 Nothing - all variables are modified in place.

	 */
	VectorI parents = { -1 };
	for (int node1 = 1; node1 < length; ++node1) {
		parents.push_back(0);
		if (current_nodes[node1]) {
			auto max_score = score_matrix(0, node1);
			for (int node2 = 1; node2 < length; ++node2) {
				if (node2 == node1 or !current_nodes[node2])
					continue;

				auto new_score = score_matrix(node2, node1);
				if (new_score > max_score) {
					max_score = new_score;
					parents[node1] = node2;
				}
			}
		}
	}

//# Check if this solution has a cycle.
	VectorI cycle;
//	print(parents);
//	print(current_nodes);
	auto has_cycle = _find_cycle(parents, length, current_nodes, cycle);
//    # If there are no cycles, find all edges and return.
//	print(cycle);
	if (!has_cycle) {
		final_edges[0] = -1;
		for (int node = 1; node < length; ++node) {
			if (!current_nodes[node])
				continue;

			auto parent = old_input[parents[node]][node];
			auto child = old_output[parents[node]][node];
			final_edges[child] = parent;
		}
		return;
	}

	//# Otherwise, we have a cycle so we need to remove an edge.
	//# From here until the recursive call is the contraction stage of the algorithm.
	auto cycle_weight = 0.0;
	//# Find the weight of the cycle.
	auto index = 0;
	for (auto node : cycle) {
		index += 1;
		cycle_weight += score_matrix(parents[node], node);
	}

//# For each node in the graph, find the maximum weight incoming
//# and outgoing edge into the cycle.
	auto cycle_representative = cycle[0];

	for (int node = 0; node < length; ++node) {
		if (!current_nodes[node] or contains(cycle, node))
			continue;

		auto in_edge_weight = -oo;
		auto in_edge = -1;
		auto out_edge_weight = -oo;
		auto out_edge = -1;

		for (auto node_in_cycle : cycle) {
			auto _in_edge_weight = score_matrix(node_in_cycle, node);
			if (_in_edge_weight > in_edge_weight) {
				in_edge_weight = _in_edge_weight;
				in_edge = node_in_cycle;
			}
//        # Add the new edge score to the cycle weight
//        # and subtract the edge we're considering removing.
			auto score = (cycle_weight + score_matrix(node, node_in_cycle)
					- score_matrix(parents[node_in_cycle], node_in_cycle));

			if (score > out_edge_weight) {
				out_edge_weight = score;
				out_edge = node_in_cycle;
			}
		}

		score_matrix(cycle_representative, node) = in_edge_weight;
		old_input[cycle_representative][node] = old_input[in_edge][node];
		old_output[cycle_representative][node] = old_output[in_edge][node];

		score_matrix(node, cycle_representative) = out_edge_weight;
		old_output[node][cycle_representative] = old_output[node][out_edge];
		old_input[node][cycle_representative] = old_input[node][out_edge];
	}
//# For the next recursive iteration, we want to consider the cycle as a
//    # single node. Here we collapse the cycle into the first node in the
//    # cycle (first node is arbitrary), set all the other nodes not be
//    # considered in the next iteration. We also keep track of which
//    # representatives we are considering this iteration because we need
//    # them below to check if we're done.

	vector<std::set<int>> considered_representatives;
	for (int i = 0, size = cycle.size(); i < size; ++i) {
		auto node_in_cycle = cycle[i];
		considered_representatives.push_back(std::set<int>());
		if (i > 0) {
//            # We need to consider at least one
//            # node in the cycle, arbitrarily choose
//            # the first.
			current_nodes[node_in_cycle] = false;
		}

		for (auto node : representatives[node_in_cycle]) {
			considered_representatives[i].insert(node);
			if (i > 0)
				representatives[cycle_representative].insert(node);
		}
	}

//	print(length);
//	print(score_matrix);
//	print(current_nodes);
//	print(final_edges);
//	print(old_input);
//	print(old_output);
//	print(representatives);
	chu_liu_edmonds(length, score_matrix, current_nodes, final_edges, old_input,
			old_output, representatives);

//# Expansion stage.
//# check each node in cycle, if one of its representatives
//# is a key in the final_edges, it is the one we need.
	auto found = false;
	auto key_node = -1;
	for (int i = 0, size = cycle.size(); i < size; ++i) {
		auto node = cycle[i];
		for (auto cycle_rep : considered_representatives[i]) {
			if (final_edges.count(cycle_rep)) {
				key_node = node;
				found = true;
				break;
			}
		}
		if (found)
			break;
	}

	auto previous = parents[key_node];
	while (previous != key_node) {
		auto child = old_output[parents[previous]][previous];
		auto parent = old_input[parents[previous]][previous];
		final_edges[child] = parent;
		previous = parents[previous];
	}
}


int intersection_count(vector<int> &heads, int child) {
    int head = heads[child];
    int bad_count = 0;
    if (head <= 0)
        return bad_count;

    if (head < child) {
        for (int node : range(head)) {
            if (head < heads[node] and heads[node] < child)
                ++bad_count;
        }
//                     excluding head
        for (int node : range(head + 1, child)) {
            if (heads[node] < head or heads[node] > child)
                ++bad_count;
//                     excluding child
        }
        for (int node : range(child + 1, heads.size())) {
            if (head < heads[node] and heads[node] < child)
                ++bad_count;
        }
    }
    else if (head > child) {
        for (int node : range(child)) {
            if (child < heads[node] and heads[node] < head)
                ++bad_count;
//                     excluding child
        }

        for (int node : range(child + 1, head)) {
            if (heads[node] < child or heads[node] > head)
                ++bad_count;
//                     excluding head
        }

        for (int node : range(head + 1, heads.size())) {
            if (child < heads[node] and heads[node] < head)
                ++bad_count;
        }
    }

    return bad_count;
}

vector<int> number_of_children(vector<int> &heads) {
    vector<int> number(heads.size() + 1);
    for (int head : heads) {
    	if (head < 0)
    		++number[heads.size()];
    	else
    		++number[head];
    }

    return number;
}

std::set<int> legitimate_range(const vector<int> &heads, int child) {
    auto ranges = range(heads.size()).set();
    for (int node : range(heads.size())) {
        int head = heads[node];
        if (head <= 0)
            continue;

        if (head < node) {
            if (head > child or child > node)
                ranges -= range(head + 1, node).set();
        }
        else if (node < head) {
            if (head < child or child < node)
                ranges -= range(node + 1, head).set();
        }
    }

    return ranges;
}

void adjust_score_matrix(Matrix &score_matrix, vector<int> &heads, std::set<int> &ranges, int child) {
    double loss = 0;
    for (int head : range(heads.size())) {
        if (ranges.count(head)) {
        }
        else {
            loss += score_matrix(head, child);
            score_matrix(head, child) = 0;
        }
    }

    loss /= ranges.size();
    for (int head : ranges) {
        score_matrix(head, child) += loss;
    }
}

vector<bool> one_hot_bool(int index, int length) {
    vector<bool> s(length);
    s[index] = true;
    return s;
}

bool _find_cycle_heads(const vector<int> &parents, vector<int> &ret) {
    int length = parents.size();
    auto added = one_hot_bool(0, length);

    auto cycle = std::set<int>();
    auto has_cycle = false;
    for (int i : range(1, length)) {
        if (has_cycle)
            break;

//        # don't redo nodes we've already
//        # visited or aren't considering.
        if (added[i])
            continue;

//        # Initialize a new possible cycle.
        std::set<int> this_cycle = {i};
        added[i] = true;
        has_cycle = true;
        int next_node = i;
        while (not this_cycle.count(parents[next_node])) {
            next_node = parents[next_node];
//            # If we see a node we've already processed,
//            # we can stop, because the node we are
//            # processing would have been in that cycle.
            if (added[next_node]) {
                has_cycle = false;
                break;
            }
            added[next_node] = true;
            this_cycle.insert(next_node);
        }

        if (has_cycle){
            auto original = next_node;
            cycle.insert(original);
            next_node = parents[original];
            while (next_node != original){
                cycle.insert(next_node);
                next_node = parents[next_node];
            }
            break;
        }
    }

    ret = list(cycle);
    return has_cycle;
}

bool sort_criterion(const std::pair<int, double> &lhs, const std::pair<int, double> &rhs) {
	return lhs.second > rhs.second;
}

//inputs: scores = [child, parent]scores[parent, child]
VectorI& decode_mst(Matrix &score_matrix, VectorI &heads, bool projective) {
//	Timer timer(__PRETTY_FUNCTION__);
	int length = score_matrix.rows();

	MatrixI old_input = int_zeros(length, length);
	MatrixI old_output = int_zeros(length, length);
	vector<bool> current_nodes(length, true);
	vector<std::set<int>> representatives(length);

	for (int node1 = 0; node1 < length; ++node1) {
		representatives[node1] = as_set( { node1 });

		for (int node2 = node1 + 1; node2 < length; ++node2) {
			old_input[node1][node2] = node1;
			old_output[node1][node2] = node2;

			old_input[node2][node1] = node2;
			old_output[node2][node1] = node1;
		}
	}

	dict<int, int> final_edges;
// The main algorithm operates inplace.
	chu_liu_edmonds(length, score_matrix, current_nodes, final_edges, old_input,
			old_output, representatives);

//	heads.resize(length); needless ??

	for (auto &p : final_edges) {
		auto [child, parent] = p;
		heads[child] = parent;
	}

	if (projective) {
#pragma GCC diagnostic ignored "-Wunused-variable"
        for (int _ : range(length * length)) {
        	auto cross_count = range(heads.size()).list([&](int child){
        		return intersection_count(heads, child);
        	});

//        	print("cross_count =", cross_count);
            auto childs_num = number_of_children(heads);
//            print("childs_num =", childs_num);
            int worst_child = -1;
            int worst_score = 0;
            for (auto [child, badness]: enumerate(cross_count)) {
                if (badness > worst_score) {
                    worst_score = badness;
                    worst_child = child;
                }
                else if (badness < worst_score) {

                }
                else if (worst_child >= 0){

                	int thisNumOfChildren = heads[child] < 0? childs_num.back(): childs_num[heads[child]];
					int worstNumOfChildren = heads[worst_child] < 0? childs_num.back(): childs_num[heads[worst_child]];
                    if (badness and thisNumOfChildren < worstNumOfChildren) {
                    	worst_child = child;
                    }
                }
            }

//            print("worst_score =", worst_score);
            if (!worst_score)
            	break;

			auto legal_range = legitimate_range(heads, worst_child) - as_set({worst_child});

			if (heads[worst_child] > 0)
				legal_range -= {heads[worst_child]};
//			print("legal_range =", legal_range);
			adjust_score_matrix(score_matrix, heads, legal_range, worst_child);

			auto head_with_good_scores = list(
				[&](int head) -> std::pair<int, double>{
					return {head, score_matrix(head, worst_child)};
				},
				legal_range);

			sort(head_with_good_scores, sort_criterion);

			for (auto [head, _] : head_with_good_scores) {
				heads[worst_child] = head;

				vector<int> ret;
				auto has_cycle = _find_cycle_heads(heads, ret);
//				print("has_cycle =", has_cycle);
				if (!has_cycle)
					break;
			}
        }
	}

    for (int _ : range(length)) {
        vector<int> roots;
        for (auto [child, head] : enumerate(heads)) {
            if (head)
                continue;
            roots.push_back(child);
        }

        if (roots.size() <= 1)
        	break;
//#             print("multiple roots detected, iteration =", i)

		auto root_with_score = list(
			[&](int root)->std::pair<int, double> {
				return {root, score_matrix(0, root)};
			},
			roots);

		sort(root_with_score, sort_criterion);

		root_with_score.erase(root_with_score.begin());

		auto roots_set = as_set(roots);

		for (auto [node, _] : root_with_score) {
			auto other_roots = roots_set - as_set({node});
			auto other_roots_list = list(other_roots);

			auto head_with_good_scores = list(
				[&](int head)->std::pair<int, double> {
					return {head, score_matrix(head, node)};
				},
				other_roots);

			sort(head_with_good_scores, sort_criterion);

			for (auto [head, _] : head_with_good_scores) {
				heads[node] = head;

				auto cross_count = range(heads.size()).list(
					[&](int child) {
						return intersection_count(heads, child);
				});

				auto error_count = sum(cross_count, [](int e){return e? 1: 0;});

				vector<int> ret;
				auto has_cycle = _find_cycle_heads(heads, ret);
				if (not has_cycle and not error_count){
					score_matrix(head, node) += score_matrix(0, node);
					score_matrix(0, node) = 0;
					break;
				}
			}
		}
    }
	return heads;
}

VectorI& _run_mst_decoding(Matrix &scores, VectorI &head_indices) {
//	Timer timer(__PRETTY_FUNCTION__);
	int seq_length = scores.rows();
	for (int j = 0; j < seq_length; ++j) {
		//    # Although we need to include the root node so that the MST includes it,
		//    # we do not want any word to be the parent of the root node.
		//    # Here, we enforce this by setting the scores for all word -> ROOT edges
		//    # edges to be 0.
		scores(0, j) = 0;
		scores(j, j) = 0.0;
	}

//	print(scores);
//	print(tag_ids);
//    # Decode the heads. Because we modify the scores to prevent
//    # adding in word -> ROOT edges, we need to find the labels ourselves.
	decode_mst(scores, head_indices);

//    # We don't care what the head or tag is for the root token, but by default it's
//    # not necesarily the same in the batched vs unbatched case, which is annoying.
//    # Here we'll just set them to zero.
	head_indices[0] = 0;
//	print(instance_head_tags);
	return head_indices;
}

bool is_projective(const VectorI &head_indices) {
	int n = head_indices.size() - 1;
	for (int i = 1; i <= n; ++i) {
		int parent_i = head_indices[i];
		for (int j = parent_i + 1; j < i; ++j) {
			int parent_j = head_indices[j];
			if (parent_j < parent_i or parent_j > i)
				return true;
		}

	}
	return false;
}

void nonprojective_adjustment(VectorI &head_indices) {
	int n = head_indices.size() - 1;
	for (int i = 2; i <= n; ++i) {
		int &parent_i = head_indices[i];
		for (int j = parent_i + 1; j < i; ++j) {
			int parent_j = head_indices[j];
			if (parent_j < parent_i) {
				// projective head-link is detected, parent_i is not an appropriate index!
				// now make adjustment for parent_i;
				parent_i = parent_j;
			}
		}
	}
}

extern "C" {

vector<int> keras_parsers_chu_liu_edmonds(MatrixD &scores) {
//	Timer timer(__PRETTY_FUNCTION__);
	int seq_length = scores.size();
	vector<int> head_indices(seq_length);

//	print(scores);
	auto scores_ = to_matrix(scores);
	return decode_mst(scores_, head_indices);
}

vector<int> keras_parsers_chu_liu_edmonds_with_chunking(MatrixD &scores, VectorI &chunking) {
//	Timer timer(__PRETTY_FUNCTION__);
//	print(__PRETTY_FUNCTION__);

	int seq_length = scores.size();
	vector<int> head_indices(seq_length);
//	print(chunking);

	vector<std::pair<int, int>> chunks;
	int size = chunking.size();
	int start = -1;
	int end = -1;
	for (int i = 0; i < size; ++i) {
		if (chunking[i]) {
			if (start >= 0)
				continue;
			start = i;
		}
		else {
			if (start >= 0) {
				end = i;
				chunks.push_back({start, end});
				start = -1;
			}
		}
	}

	if (start >= 0) {
		chunks.push_back({start, size});
	}

//	print(chunks);
	for (auto &chunk: chunks) {
		auto [start, end] = chunk;

		double maxProbability = -1;
		double optimalLocalRoot = -1;
		for (int child : range(start, end)) {
			double possibilityOfBeingALocalRoot = 0;
			double possibilityOfBeingAnInnerChild = 0;

			for (int parent : range(start)) {
				possibilityOfBeingALocalRoot += scores[parent][child];
			}

			for (int parent : range(start, end)) {
				possibilityOfBeingAnInnerChild += scores[parent][child];
			}

			for (int parent : range(end, size)) {
				possibilityOfBeingALocalRoot += scores[parent][child];
			}

			double prob = possibilityOfBeingALocalRoot - possibilityOfBeingAnInnerChild;
			if (prob > maxProbability) {
				maxProbability = prob;
				optimalLocalRoot = child;
			}
		}

//		print("optimalLocalRoot = ", optimalLocalRoot - 1);
//		print("in the entity chunking: [", start - 1, end - 1, "]");

		for (int child : range(start, end)) {
			if (child == optimalLocalRoot)
				continue;
//clear the score pointing outside the entity, since there must be only one local root within the entity;
			for (int parent : range(start)) {
				scores[parent][child] = 0;
//				print("setting scores[", parent - 1, "][", child - 1, "] = 0");
			}

			for (int parent : range(end, size)) {
				scores[parent][child] = 0;
//				print("setting scores[", parent - 1, "][", child - 1, "] = 0");
			}
		}
	}

	auto scores_ = to_matrix(scores);
	return decode_mst(scores_, head_indices);
}

}

