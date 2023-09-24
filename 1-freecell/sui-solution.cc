// SUI Project 1
// Authors: xpysik00, xziska03

#include "search-strategies.h"

#include "memusage.h"

#include <queue>
#include <algorithm>
#include <numeric>


typedef struct bfs_node {
	std::shared_ptr<SearchState> parent_state;
	std::shared_ptr<SearchAction> action;
} Bfs_node;

std::vector<SearchAction> BreadthFirstSearch::solve(const SearchState &init_state) {
	std::vector<SearchAction> solution, actions;
	std::shared_ptr<SearchState> working_state = std::make_shared<SearchState>(init_state);
	std::shared_ptr<SearchState> tmp_state;

	// queue for storing nodes to expand
	std::queue<std::shared_ptr<SearchState>> open;
	open.push(working_state);

	// map to keep track of expanded states, their parent states and last action leading to them
	std::map<SearchState, Bfs_node> closed;

	closed[*working_state].parent_state = nullptr;
	
	while(!open.empty()) {
		// check whether 1KiB close to memory limit
		if (getCurrentRSS() + 1048576 > mem_limit_)
			break;

		working_state = open.front();
		open.pop();

		// check the moves available from the current state
		actions = working_state->actions();

		// if the current node can be expanded...
		if (actions.size() > 0) {
			// ...then do so and insert all possible moves into queue and create a new solution
			for (auto action : actions) {
				tmp_state = std::make_shared<SearchState>(action.execute(*working_state));

				// expanded node leads to some already visited state
				if (closed.count(*tmp_state))
					continue;

				closed[*tmp_state].parent_state = working_state;
				closed[*tmp_state].action = std::make_shared<SearchAction>(action);

				// correct solution found
				if (tmp_state->isFinal()) {
					// create reversed solution and then reverse it into chronological order
					while(closed[*tmp_state].parent_state != nullptr) {
						solution.push_back(*closed[*tmp_state].action);
						tmp_state = closed[*tmp_state].parent_state;
					}
					std::reverse(solution.begin(), solution.end());

					return solution;
				}

				open.push(tmp_state);
			}
		}
	}
	
	return {};
}


typedef struct dfs_node {
	std::shared_ptr<SearchState> parent_state;
	std::shared_ptr<SearchAction> action;
	int depth;
} Dfs_node;

std::vector<SearchAction> DepthFirstSearch::solve(const SearchState &init_state) {
	std::vector<SearchAction> solution, actions;
	std::shared_ptr<SearchState> working_state = std::make_shared<SearchState>(init_state);
	std::shared_ptr<SearchState> tmp_state;
	int depth;

	// stack for storing nodes to expand
	std::vector<std::shared_ptr<SearchState>> open;
	open.push_back(working_state);

	// map to keep track of expanded states, their parent states, last action leading to them and their depth
	std::map<SearchState, Dfs_node> closed;

	closed[*working_state].parent_state = nullptr;
	closed[*working_state].depth = 0;

	while(!open.empty()) {
		if (getCurrentRSS() + 1048576 > mem_limit_)
			break;

		working_state = open.back();
		open.pop_back();

		// check the moves available from the current state
		actions = working_state->actions();

		// if the current node can be expanded...
		if (actions.size() > 0) {
			// ...then do so and insert all possible moves into queue and create a new solution
			for (auto action : actions) {
				tmp_state = std::make_shared<SearchState>(action.execute(*working_state));

				// expanded node leads to some already visited state
				if (closed.count(*tmp_state))
					continue;

				closed[*tmp_state].parent_state = working_state;
				closed[*tmp_state].action = std::make_shared<SearchAction>(action);
				closed[*tmp_state].depth = depth = closed[*working_state].depth + 1;

				if (tmp_state->isFinal()) {
					// create reversed solution and then reverse it into chronological order
					while(closed[*tmp_state].parent_state != nullptr) {
						solution.push_back(*closed[*tmp_state].action);
						tmp_state = closed[*tmp_state].parent_state;
					}
					std::reverse(solution.begin(), solution.end());

					return solution;
				}

				if (depth < depth_limit_)
					open.push_back(tmp_state);
			}
		}
	}
	
	return {};
}

double my_abs (double a, double b) {
	if (a > b)
		return a - b;
	else
		return b - a;
}

// find the index of a given card
int get_index(WorkStack workstack, int value, Color color)
{
	auto v = workstack.storage();
    auto it = find_if(v.begin(), v.end(), [&value, &color](Card p) { return p.color == color && p.value == value; });
    // if element was found
    if (it != v.end()) 
    {
        // calculate index of a card
        int index = it - v.begin();
        return index + 1;
    }
    else {
        // in case the card is not in given container
        return 0;
    }
}

double StudentHeuristic::distanceLowerBound(const GameState &state) const {
	int index = 0;
	int sum = 0;
	// matrice representing the card storages
	std::vector<std::vector<int>> ones_stacks;
	std::vector<Color> colors{Color::Heart, Color::Diamond, Color::Club, Color::Spade};

	// create 2d representation of game state cards dimensions in stacks, filled with ones
	for(auto &stack : state.stacks){
		ones_stacks.push_back(std::vector<int>(stack.storage().size(), 1));
	}
	// value of currently evaluated card
	int value = 1;
	// stack column
	int column = 0;
	bool found_in_homes = false;
	bool found_in_fc = false;

	// evaluate positions of all cards
	while(value<=king_value){
		// for each color
		for(auto color : colors){
			// if free cells contain current card, add 1 to sum
			for(auto &free_cell: state.free_cells){
				auto fc_card = free_cell.topCard();
				if(fc_card){
					if (fc_card.value().value == value){
						if(fc_card.value().color == color){
							sum += 1;
							found_in_fc = true;
							break;
						}
					}
				}
				found_in_fc = false;
			}
			if(found_in_fc)
				continue;
			// if home cells contain current card, do nothing
			for (auto &home : state.homes) {
				auto top_card = home.topCard();
				if(top_card){
					if(color == top_card.value().color && value <= top_card.value().value){
						found_in_homes = true;
						break;
					}
				}
				found_in_homes = false;
			}
			// if card was found in one of the homes, skip search in stacks
			if(found_in_homes)
				continue;
			// search for index of given card
			for (auto &stack : state.stacks) {
				index = get_index(stack, value, color);
				if(index){
					// sum all values stored in the from found index
					sum += std::accumulate(ones_stacks[column].begin() + index - 1, ones_stacks[column].end(), 0);
					ones_stacks[column][index - 1] = 0;
					break;
				}
				column++;
			}
			column = 0;
		}
		value++;
	}
    return (double)sum;
}

typedef struct a_star_node {
	std::shared_ptr<SearchState> parent_state;
	std::shared_ptr<SearchAction> action;
	double rank;
} A_star_node;

typedef struct a_star_open_node {
	std::shared_ptr<SearchState> state;
	double rank;
	int distance;
} A_star_open_node;

auto a_star_compare = [](A_star_open_node a, A_star_open_node b) {
	return a.rank > b.rank;
};

std::vector<SearchAction> AStarSearch::solve(const SearchState &init_state) {
	std::vector<SearchAction> solution, actions;
	A_star_open_node working_node;
	A_star_open_node tmp_node;

	working_node.state = std::make_shared<SearchState>(init_state);
	working_node.distance = 0;
	double heuristic_value = working_node.rank = compute_heuristic(*working_node.state, *heuristic_);

	// priority queue for storing nodes to expand with their rank
	std::priority_queue<A_star_open_node, std::vector<A_star_open_node>, decltype(a_star_compare)> open(a_star_compare);

	// map to keep track of expanded states, their parent states, last action leading to them and their rank
	std::map<SearchState, A_star_node> closed;

	A_star_node init_node;
	init_node.parent_state = nullptr;
	init_node.rank = heuristic_value;
	closed[*working_node.state] = init_node;

	open.push(working_node);
	closed[*working_node.state].parent_state = nullptr;
	closed[*working_node.state].rank = heuristic_value;
	
	while(!open.empty()) {
		// check whether 1KiB close to memory limit
		if (getCurrentRSS() + 1048576 > mem_limit_)
			break;

		working_node = open.top();
		open.pop();

		// check the moves available from the current state
		actions = working_node.state->actions();

		// if the current node can be expanded...
		if (actions.size() > 0) {
			// ...then do so and insert all possible moves into queue and create a new solution
			for (auto action : actions) {
				tmp_node.state = std::make_shared<SearchState>(action.execute(*working_node.state));

				// correct solution found
				if (tmp_node.state->isFinal()) {
					A_star_node tmp;
					tmp.parent_state = working_node.state;
					tmp.action = std::make_shared<SearchAction>(action);

					// create reversed solution and then reverse it into chronological order
					while(tmp.parent_state != nullptr) {
						solution.push_back(*tmp.action);
						tmp = closed[*tmp.parent_state];
					}
					std::reverse(solution.begin(), solution.end());

					return solution;
				}

				tmp_node.distance = working_node.distance + 1;
				tmp_node.rank = tmp_node.distance + compute_heuristic(*tmp_node.state, *heuristic_);

				// expanded node leads to some already visited state
				if (closed.count(*tmp_node.state))
					if (closed[*tmp_node.state].rank <= tmp_node.rank)
						continue;

				closed[*tmp_node.state].parent_state = working_node.state;
				closed[*tmp_node.state].action = std::make_shared<SearchAction>(action);
				closed[*tmp_node.state].rank = tmp_node.rank;

				open.push(tmp_node);
			}
		}
	}
	
	return {};
}
