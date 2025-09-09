#include <iostream>
#include <list>
#include <algorithm>
#include <ranges>
#include <vector>
#include <map>
#include <set>
#include <numeric>
#include <functional> // For std::function, if needed, though not directly by DSU usually

struct Mane;
using namespace std;

// DSU Data Structures
map<string, string> parent;

// DSU Find operation
string find_set(string s) {
    if (parent[s] == s)
        return s;
    return parent[s] = find_set(parent[s]);
}

// DSU Unite operation
void unite_sets(string a, string b) {
    a = find_set(a);
    b = find_set(b);
    if (a != b)
        parent[b] = a;
}

struct State {
    string statename;

    bool startState = false;
    bool finalState = false;

    list<Mane> *exit_Manes_To_Other_states;
};

struct Mane {
    string name;
    State *enteredstate;
    State *exitstate;
};

list<State> stateList;
list<string> maneList;

bool State_Deleter(State *state, list<State *> &visited);

void DFA_Delete_Trap_UnuseableState();

void DFA_SHow_Stucture();

void DFA_SHow_Stucture(State *state, list<State *> visited = list<State *>());

void Connect_State_Mane();

void Choosing_Mane_And_NextState(State &state);

void InputGetter_State_Mane();

void cleanup();

void DFA_TO_ReducedDFA();

void Create_Minimized_DFA(const list<pair<string, string>>& equivalent_pairs);

int main() {

    InputGetter_State_Mane();

    Connect_State_Mane();

    DFA_Delete_Trap_UnuseableState();

    DFA_SHow_Stucture();

    DFA_TO_ReducedDFA();

    list<pair<string, string>> equivalent_pairs_from_reduction;

    cout << "\n\n=== DFA Structure After Minimization ===\n";
    State *new_start_state = nullptr;
    for (State &state_ref : stateList) {
        if (state_ref.startState) {
            new_start_state = &state_ref;
            DFA_SHow_Stucture();
            break;
        }
    }
    if (!new_start_state && !stateList.empty()) {
         cout << "Minimized DFA has no designated start state. Showing all states:" << endl;
         DFA_SHow_Stucture();
    } else if (stateList.empty()) {
        cout << "DFA is empty after minimization." << endl;
    }
    cleanup();
    return 0;
}

void Create_Minimized_DFA(const list<pair<string, string>>& equivalent_pairs) {

    parent.clear();
    for (const auto& state_obj : stateList) {
        parent[state_obj.statename] = state_obj.statename;
    }

    for (const auto& eq_pair : equivalent_pairs) {
        unite_sets(eq_pair.first, eq_pair.second);
    }

    map<string, list<State*>> representative_to_original_members;
    list<State*> original_state_pointers;

    for (State& original_state_ref : stateList) {
        original_state_pointers.push_back(&original_state_ref);
    }
    for (State* original_state_ptr : original_state_pointers) {
        string rep = find_set(original_state_ptr->statename);
        representative_to_original_members[rep].push_back(original_state_ptr);
    }
    list<State> temp_new_states;
    map<string, string> rep_to_new_name_map;

    for (auto const& [original_rep_name, members_list_of_original_ptrs] : representative_to_original_members) {
        State new_state_obj;
        string generated_name;

        bool is_single_true_unmerged = false;
        if (members_list_of_original_ptrs.size() == 1) {
            if (members_list_of_original_ptrs.front()->statename == original_rep_name) {
                is_single_true_unmerged = true;
            }
        }

        if (is_single_true_unmerged) {
            generated_name = original_rep_name;
        } else {
            list<string> member_names_for_new_name;
            for (State* member_state_ptr : members_list_of_original_ptrs) {
                member_names_for_new_name.push_back(member_state_ptr->statename);
            }
            member_names_for_new_name.sort();
            generated_name = accumulate(member_names_for_new_name.begin(), member_names_for_new_name.end(), string(""),
                                        [](const string& a, const string& b) {
                                            return a.empty() ? b : a + "_" + b;
                                        });
        }
        new_state_obj.statename = generated_name;
        rep_to_new_name_map[original_rep_name] = generated_name;

        new_state_obj.startState = false;
        new_state_obj.finalState = false;
        for (State* member_state_ptr : members_list_of_original_ptrs) {
            if (member_state_ptr->startState) {
                new_state_obj.startState = true;
            }
            if (member_state_ptr->finalState) {
                new_state_obj.finalState = true;
            }
        }
        new_state_obj.exit_Manes_To_Other_states = new list<Mane>();
        temp_new_states.push_back(new_state_obj);
    }
    auto find_state_in_given_list = [&](const string& name, list<State>& states_to_search) -> State* {
        for (State& s_ref : states_to_search) {
            if (s_ref.statename == name) {
                return &s_ref;
            }
        }
        return nullptr;
    };
    for (auto const& [original_rep_name, original_members_list_ptrs] : representative_to_original_members) {
        if (original_members_list_ptrs.empty()) continue;

        string new_source_state_name = rep_to_new_name_map[original_rep_name];
        State* new_source_state_in_temp = find_state_in_given_list(new_source_state_name, temp_new_states);

        if (!new_source_state_in_temp) {
            cerr << "Critical Error during transition gen: Newly created source state '" << new_source_state_name << "' not found in temp_new_states list." << endl;
            continue;
        }
        if (!new_source_state_in_temp->exit_Manes_To_Other_states) {
            cerr << "Critical Error during transition gen: exit_Manes_To_Other_states is null for temp state '" << new_source_state_name << "'." << endl;
            continue;
        }

        for (const string& current_mane_name : ::maneList) {
            State* first_original_target_state_ptr = nullptr; // This will point to an ORIGINAL state object

            for (State* original_member_state_ptr : original_members_list_ptrs) {
                if (!original_member_state_ptr || !original_member_state_ptr->exit_Manes_To_Other_states) continue;

                for (const Mane& old_mane_transition : *(original_member_state_ptr->exit_Manes_To_Other_states)) {
                    if (old_mane_transition.name == current_mane_name) {
                        if (old_mane_transition.exitstate) { // This exitstate points to an ORIGINAL state
                            first_original_target_state_ptr = old_mane_transition.exitstate;
                            break; // Found a transition for current_mane_name from one of the original members
                        }
                    }
                }
                if (first_original_target_state_ptr) break; // Move to next mane_name
            }

            if (first_original_target_state_ptr) {
                string original_target_name = first_original_target_state_ptr->statename;
                string target_original_rep_name = find_set(original_target_name);
                string new_target_state_name = rep_to_new_name_map[target_original_rep_name];

                State* new_target_state_in_temp = find_state_in_given_list(new_target_state_name, temp_new_states);

                if (!new_target_state_in_temp) {
                    cerr << "Error during transition gen: New target state '" << new_target_state_name
                         << "' not found in temp_new_states for mane '" << current_mane_name
                         << "' from new source state '" << new_source_state_name << "'." << endl;
                    continue;
                }
                bool transition_exists = false;
                for (const Mane& existing_mane : *(new_source_state_in_temp->exit_Manes_To_Other_states)) {
                    if (existing_mane.name == current_mane_name && existing_mane.exitstate == new_target_state_in_temp) {
                        transition_exists = true;
                        break;
                    }
                }

                if (!transition_exists) {
                    Mane new_mane_obj;
                    new_mane_obj.name = current_mane_name;
                    new_mane_obj.enteredstate = new_source_state_in_temp;
                    new_mane_obj.exitstate = new_target_state_in_temp;
                    new_source_state_in_temp->exit_Manes_To_Other_states->push_back(new_mane_obj);
                }
            }
        }
    }
    // The previous stateList is now obsolete. We will replace it with temp_new_states.
    // To avoid invalidating pointers inside Mane objects, we swap the lists.
    // This is efficient and preserves the memory locations of the State objects.
    stateList.swap(temp_new_states);

    // temp_new_states now holds the old states. We must clean up their resources.
    for (State& old_state : temp_new_states) {
        if (old_state.exit_Manes_To_Other_states != nullptr) {
            delete old_state.exit_Manes_To_Other_states;
            old_state.exit_Manes_To_Other_states = nullptr;
        }
    }
    // The old State objects themselves will be destroyed when temp_new_states goes out of scope.
    // No pointer rewiring is needed because the addresses of the new states in stateList are the same
    // as they were in temp_new_states.
}
void DFA_TO_ReducedDFA() {
    list<pair<string, string>> allTople;
    list<pair<string, string>> deletedTople;

    // First create all possible pairs
    for (auto it1 = stateList.begin(); it1 != stateList.end(); ++it1) {
        auto it2 = it1;
        ++it2;
        while (it2 != stateList.end()) {
            allTople.push_back({it1->statename, it2->statename});
            ++it2;
        }
    }

    // Show initial pairs
    cout << "\nInitial all pairs: ";
    for (const auto &pair: allTople) {
        cout << pair.first << pair.second << " ";
    }
    cout << endl;

    // Now filter based on final states
    list<pair<string, string>> newAllTople;
    for (const auto &pair: allTople) {
        // Find the actual states to check their final status
        auto state1 = find_if(stateList.begin(), stateList.end(),
            [&pair](const State &s) { return s.statename == pair.first; });
        auto state2 = find_if(stateList.begin(), stateList.end(),
            [&pair](const State &s) { return s.statename == pair.second; });

        if (state1->finalState != state2->finalState) {
            deletedTople.push_back(pair);
        } else {
            newAllTople.push_back(pair);
        }
    }
    allTople = newAllTople;

    // Show results after final state filtering
    cout << "\nAfter checking final states:" << endl;
    cout << "Remaining pairs: ";
    for (const auto &pair: allTople) {
        cout << pair.first << pair.second << " ";
    }
    cout << endl;

    cout << "Deleted pairs: ";
    for (const auto &pair: deletedTople) {
        cout << pair.first << pair.second << " ";
    }
    cout << endl;

    // New section: Check mane transitions and their destinations
    bool changesMade;
    do {
        changesMade = false;
    auto it = allTople.begin();
    while (it != allTople.end()) {
        // Find the actual states for this pair
        auto state1 = find_if(stateList.begin(), stateList.end(),
            [&it](const State &s) { return s.statename == it->first; });
        auto state2 = find_if(stateList.begin(), stateList.end(),
            [&it](const State &s) { return s.statename == it->second; });

        bool shouldDelete = false;

            // Check if both states have the same mane transitions
        for (const string &mane : maneList) {
            State* nextState1 = nullptr;
            State* nextState2 = nullptr;
            bool hasTransition1 = false;
            bool hasTransition2 = false;

            // Find where state1 goes with this mane
            for (const Mane &transition : *(state1->exit_Manes_To_Other_states)) {
                if (transition.name == mane) {
                    nextState1 = transition.exitstate;
                    hasTransition1 = true;
                    break;
                }
            }

            for (const Mane &transition : *(state2->exit_Manes_To_Other_states)) {
                if (transition.name == mane) {
                    nextState2 = transition.exitstate;
                    hasTransition2 = true;
                    break;
                }
            }

            if (hasTransition1 && hasTransition2) {
                    pair<string, string> destPair;
                    if (nextState1->statename < nextState2->statename) {
                        destPair = {nextState1->statename, nextState2->statename};
                    } else {
                        destPair = {nextState2->statename, nextState1->statename};
                    }

                    if (find(deletedTople.begin(), deletedTople.end(), destPair) != deletedTople.end()) {
                        shouldDelete = true;
                        cout << "\nPair " << it->first << it->second << " leads to deleted pair "
                             << destPair.first << destPair.second << " with mane " << mane << endl;
                        break;
                }
            }
        }

        if (shouldDelete) {
            deletedTople.push_back(*it);
            it = allTople.erase(it);
                changesMade = true;
        } else {
            ++it;
        }
    }
    } while (changesMade);

    cout << "\nAfter checking mane transitions:" << endl;
    cout << "Remaining pairs (these are the equivalent pairs): ";
    for (const auto &pair: allTople) {
        cout << "(" << pair.first << ", " << pair.second << ") ";
    }
    cout << endl;

    cout << "Deleted pairs (these are distinguishable): ";
    for (const auto &pair: deletedTople) {
        cout << "(" << pair.first << ", " << pair.second << ") ";
    }
    cout << endl;

    Create_Minimized_DFA(allTople);
}

bool State_Deleter(State *state, list<State *> &visited) {
    if (find(visited.begin(), visited.end(), state) != visited.end()) {
        return false;
    }
    visited.push_back(state);

    if (state->finalState) {
        return true;
    }

    if (state->exit_Manes_To_Other_states->empty()) {
        return false;
    }

    for (const Mane &mane: *(state->exit_Manes_To_Other_states)) {
        if (mane.exitstate != state) {
            list<State *> newVisited = visited;
            if (State_Deleter(mane.exitstate, newVisited)) {
                return true;
            }
        }
    }

    return false;
}

void DFA_Delete_Trap_UnuseableState() {
    State *startState = nullptr;
    for (State &state: stateList) {
        if (state.startState) {
            startState = &state;
            break;
        }
    }

    if (!startState) {
        cout << "Error: No start state found!" << endl;
        return;
    }

    if (startState->exit_Manes_To_Other_states->empty()) {
        cout << endl << "DFA is incorrect: Start state has no transitions" << endl << endl;
        return;
    }

    list<State *> trapStates;
    cout << "\n=== Analyzing States for Trap Detection ===\n";

    list<State *> allStates;
    for (State &state: stateList) {
        allStates.push_back(&state);
    }

    for (State *state: allStates) {
        cout << "\nChecking state: " << state->statename;
        if (state->startState) cout << " (Start State)";
        if (state->finalState) cout << " (Final State)";
        cout << endl;

        list<State *> visited;
        if (!State_Deleter(state, visited)) {
            trapStates.push_back(state);
            cout << " State " << state->statename << " identified as trap state" << endl;
            cout << "  Transitions from this state:" << endl;
            if (state->exit_Manes_To_Other_states->empty()) {
                cout << "  - No transitions (Dead end)" << endl;
            } else {
                for (const Mane &mane: *(state->exit_Manes_To_Other_states)) {
                    cout << "  - " << state->statename << " --[" << mane.name << "]--> "
                            << mane.exitstate->statename << endl;
                }
            }
        } else {
            cout << " State " << state->statename << " is valid" << endl;
        }
    }

    cout << "\n=== Removing Transitions to Trap States ===\n";

    for (State *state: allStates) {
        cout << "\nProcessing state: " << state->statename << endl;

        list<Mane> validTransitions;

        for (const Mane &mane: *(state->exit_Manes_To_Other_states)) {
            if (find(trapStates.begin(), trapStates.end(), mane.exitstate) == trapStates.end()) {
                cout << " Keeping transition: " << state->statename << " --[" << mane.name << "]--> "
                        << mane.exitstate->statename << endl;
                validTransitions.push_back(mane);
            } else {
                cout << " Removing transition: " << state->statename << " --[" << mane.name << "]--> "
                        << mane.exitstate->statename << endl;
            }
        }

        *(state->exit_Manes_To_Other_states) = validTransitions;
    }

    cout << "\n=== Summary of Trap State Removal ===\n";
    if (!trapStates.empty()) {
        cout << "Found " << trapStates.size() << " trap state(s):" << endl;
        for (State *trapState_ptr : trapStates) { // trapStates contains State* pointers
            cout << "- " << trapState_ptr->statename;
            if (trapState_ptr->finalState) cout << " (Was Final State)";
            if (trapState_ptr->startState) cout << " (Was Start State)";
            cout << endl;

            if (trapState_ptr->exit_Manes_To_Other_states != nullptr) {
                delete trapState_ptr->exit_Manes_To_Other_states;
                trapState_ptr->exit_Manes_To_Other_states = nullptr; // Good practice
            }
        }
        stateList.remove_if([&trapStates](const State& s_in_list) {
            return std::any_of(trapStates.begin(), trapStates.end(),
                               [&s_in_list](const State* trap_ptr) {
                                   if (trap_ptr) {
                                       return trap_ptr->statename == s_in_list.statename;
                                   }
                                   return false;
                               });
        });

        cout << "\nTrap states have been removed from the DFA and their resources deallocated." << endl;
    } else {
        cout << "No trap states found in the DFA." << endl;
    }
    cout << "\n=== Trap State Removal Complete ===\n" << endl;
}

void DFA_SHow_Stucture() {
    cout << endl << "DFA Structure" << endl;

    for (const State &state: stateList) {

        cout << endl << "State: " << state.statename;
        if (state.finalState) cout << " (Final State)";
        else cout << " (Not Final State)";
        cout << endl;

        cout << "Mane :" << endl;
        if (state.exit_Manes_To_Other_states != nullptr) {
            for (const Mane &mane: *state.exit_Manes_To_Other_states) {
                cout << "  " << state.statename << "[" << mane.name << "]> "
                        << mane.exitstate->statename << endl;
            }

            if (state.exit_Manes_To_Other_states->empty()) {
                cout << "  (No Mane)" << endl;
            }
        } else {
            cout << "  (No Mane List)" << endl;
        }
        cout << endl << endl;
    }
}

void InputGetter_State_Mane() {
    cout << "Hello DFA to redused DFA Project ( Hamed Mohammadi )" << endl << endl <<
            "Please Enter the number of your State :";

    int numberOfState;
    cin >> numberOfState;

    for (int i = 0; i < numberOfState; i++) {
        string stateinput;

        if (i == 0) {

            cout << "Enter startState name :" << endl;
            cin >> stateinput;
            State state;
            state.statename = stateinput;
            state.startState = true;
            state.exit_Manes_To_Other_states = new list<Mane>();

            stateList.push_back(state);
        } else {

            cout << "Enter Other state name :" << endl;
            cin >> stateinput;

            State state;
            cout << "Is this state finialState ? ((yes/1)(no/0))   ";
            int finialStateChecked;
            while (true) {
                cin >> finialStateChecked;
                if (finialStateChecked == 1) {

                    State state;
                    state.statename = stateinput;
                    state.finalState = true;
                    state.exit_Manes_To_Other_states = new list<Mane>();

                    stateList.push_back(state);
                    cout << "final state is added" << endl;
                    break;
                }
                if (finialStateChecked == 0) {

                    State state;
                    state.statename = stateinput;
                    state.exit_Manes_To_Other_states = new list<Mane>();

                    stateList.push_back(state);
                    cout << "non final state is added" << endl;
                    break;
                }
                cout << "invalid number please enter ((yes/1)(no/0))" << endl;
            }
        }
    }

    cout << endl << endl << "Please Enter the number of your Mane :";

    int numberOfMane;
    cin >> numberOfMane;
    cout << endl << endl;

    for (int i = 0; i < numberOfMane; i++) {
        cout << endl << "Enter " << (i + 1) << " Mane name :";
        string maneinput;
        cin >> maneinput;
        maneList.push_back(maneinput);
        cout << endl << "Mane are added " << endl << endl;
    }
}

void Connect_State_Mane() {
    cout << endl << endl;

    for (State &state: stateList) {
        if (state.startState) {
            cout << "startState is : " << state.statename << endl << endl;
            Choosing_Mane_And_NextState(state);
        }
    }

    for (State &state: stateList) {
        if (!state.startState) {
            cout << "this state is : " << state.statename << endl << endl;
            Choosing_Mane_And_NextState(state);
        }
    }
}

void Choosing_Mane_And_NextState(State &state) {
    list<string> maneList_for_thisState = maneList;

    bool isStartStateCheckedforFirstTime = state.startState;
    while (true) {
        if (maneList_for_thisState.empty()) {
            return;
        }

        string maneinput;
        cout << "Which Mane do you choose?(for stoping and go for next state (//)\\in start state u should choose one )"
                << endl << endl;

        for (const string &mane: maneList_for_thisState) {
            cout << mane << endl;
        }
        cout << endl;

        cin >> maneinput;
        if (maneinput == "//" && !isStartStateCheckedforFirstTime) {
            return;
        }

        auto maneIt = find(maneList_for_thisState.begin(), maneList_for_thisState.end(), maneinput);
        if (maneIt == maneList_for_thisState.end()) {
            cout << "Invalid Mane selection!" << endl;
            continue;
        }

        Mane this_mane;
        this_mane.name = maneinput;

        cout << "Mane is selected: " << maneinput << endl;
        cout << "Which State should we select by this Mane " << maneinput << " ?" << endl;

        for (const State &this_state: stateList) {
            cout << this_state.statename << endl;
        }

        string stateinput;
        cin >> stateinput;

        auto stateIt = ranges::find_if(stateList, [&stateinput](const State &this_state) {
            return this_state.statename == stateinput;
        });

        if (stateIt == stateList.end()) {
            cout << "Invalid State selection!" << endl;
            continue;
        }

        this_mane.enteredstate = &state;
        this_mane.exitstate = &(*stateIt);
        state.exit_Manes_To_Other_states->push_back(this_mane);
        maneList_for_thisState.erase(maneIt);

        if (state.startState) {
            isStartStateCheckedforFirstTime = false;
        }
    }
}

void cleanup() {
    for (State &state: stateList) {
        if (state.exit_Manes_To_Other_states != nullptr) {
            delete state.exit_Manes_To_Other_states;
            state.exit_Manes_To_Other_states = nullptr;
        }
    }
    stateList.clear();
}
