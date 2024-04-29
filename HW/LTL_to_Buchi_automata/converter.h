/*
 * Author: Leonid Tsirunov
 */

#include <iostream>
#include <algorithm>
#include <vector>
#include <string>
#include <cmath>
#include "ltl.h"
#include "fsm.h"

using namespace model::ltl;
using namespace model::fsm;

#define TRUE "true"
#define FALSE "false"

namespace model::converter {

const Formula& simplify_ltl(const Formula& f) {
    switch (f.kind()) {
        case Formula::ATOM:
            return f;
        case Formula::NOT: {
            Formula arg = simplify_ltl(f.arg());
            if (arg.kind() == Formula::ATOM && arg.prop() == TRUE)
                return P(FALSE);
            else if (arg.kind() == Formula::ATOM && arg.prop() == FALSE)
                return P(TRUE);
            else
                return !(simplify_ltl(f.arg()));
        }
        case Formula::AND: {
            Formula lhs = simplify_ltl(f.lhs());
            Formula rhs = simplify_ltl(f.rhs());
            if ((lhs.kind() == Formula::ATOM && lhs.prop() == FALSE) || (rhs.kind() == Formula::ATOM && rhs.prop() == FALSE))
                return P(FALSE);
            else
                return (simplify_ltl(f.lhs()) && simplify_ltl(f.rhs()));
        }
        case Formula::OR: {
            Formula lhs = simplify_ltl(f.lhs());
            Formula rhs = simplify_ltl(f.rhs());
            if ((lhs.kind() == Formula::ATOM && lhs.prop() == TRUE) || (rhs.kind() == Formula::ATOM && rhs.prop() == TRUE))
                return P(TRUE);
            else
                return (simplify_ltl(f.lhs()) || simplify_ltl(f.rhs()));
        }
        case Formula::IMPL:
            return simplify_ltl(!(f.lhs()) || (f.rhs()));
        case Formula::X: {
            Formula arg = simplify_ltl(f.arg());
            switch (arg.kind()) {
                case Formula::ATOM:
                    if (arg.prop() == TRUE)
                        return P(TRUE);
                    else if (arg.prop() == FALSE)
                        return P(FALSE);
                    else
                        return X(simplify_ltl(f.arg()));
                case Formula::OR:
                    return simplify_ltl(X(arg.lhs()) || X(arg.rhs()));
                case Formula::AND:
                    return simplify_ltl(X(arg.lhs()) && X(arg.rhs()));
                case Formula::NOT:
                    return simplify_ltl(!(X(arg.arg())));
                case Formula::U:
                    return U(simplify_ltl(X(arg.lhs())), simplify_ltl(X(arg.rhs())));
                default:
                    return X(simplify_ltl(f.arg()));
            }
        }
        case Formula::G:
            return !(U(P(TRUE), !(simplify_ltl(f.arg()))));
        case Formula::F:
            return U(P(TRUE), simplify_ltl(f.arg()));
        case Formula::U:
            return U(simplify_ltl(f.lhs()), simplify_ltl(f.rhs()));
        case Formula::R:
            return  !(U(!simplify_ltl(f.lhs()), !simplify_ltl(f.rhs())));
    }
    
    return f;
}

bool is_equal_formula(const Formula& f_1, const Formula& f_2) {
    if (f_1.kind() != f_2.kind())
        return false;
    else {
        switch (f_1.kind()) {
            case Formula::ATOM:
                return f_1.prop() == f_2.prop();
            case Formula::NOT:
                return is_equal_formula(f_1.arg(), f_2.arg());
            case Formula::AND:
                return (is_equal_formula(f_1.lhs(), f_2.lhs()) && is_equal_formula(f_1.rhs(), f_2.rhs())) || (is_equal_formula(f_1.rhs(), f_2.lhs()) && is_equal_formula(f_1.lhs(), f_2.rhs()));
            case Formula::OR:
                return (is_equal_formula(f_1.lhs(), f_2.lhs()) && is_equal_formula(f_1.rhs(), f_2.rhs())) || (is_equal_formula(f_1.rhs(), f_2.lhs()) && is_equal_formula(f_1.lhs(), f_2.rhs()));
            case Formula::IMPL:
                return is_equal_formula(f_1.lhs(), f_2.lhs()) && is_equal_formula(f_1.rhs(), f_2.rhs());
            case Formula::X:
                return is_equal_formula(f_1.arg(), f_2.arg());
            case Formula::G:
                return is_equal_formula(f_1.arg(), f_2.arg());
            case Formula::F:
                return is_equal_formula(f_1.arg(), f_2.arg());
            case Formula::U:
                return is_equal_formula(f_1.lhs(), f_2.lhs()) && is_equal_formula(f_1.rhs(), f_2.rhs());
            case Formula::R:
                return is_equal_formula(f_1.lhs(), f_2.lhs()) && is_equal_formula(f_1.rhs(), f_2.rhs());
            default:
                return false;
        }
    }
}

bool find_formula(std::vector<Formula> vec, const Formula& f_1) {
    for (const auto& f_2 : vec) {
        if (is_equal_formula(f_1, f_2))
            return true;
    }

    return false;
}

std::vector<Formula> collect_positive_closure(const Formula &f) {
    std::vector<Formula> pos_clos;
    switch (f.kind()) {
        case Formula::ATOM: {
            pos_clos.push_back(f);
            return pos_clos;
        }
        case Formula::NOT:
            return collect_positive_closure(f.lhs());
        case Formula::AND: {
            pos_clos = collect_positive_closure(f.lhs());
            std::vector<Formula> r_pos_clos = collect_positive_closure(f.rhs());
            for (auto &f : r_pos_clos) {
                pos_clos.push_back(f);
            }
            pos_clos.push_back(f);
            return pos_clos;
        }
        case Formula::OR: {
            pos_clos = collect_positive_closure(f.lhs());
            std::vector<Formula> r_pos_clos = collect_positive_closure(f.rhs());
            for (auto &f : r_pos_clos) {
                pos_clos.push_back(f);
            }
            pos_clos.push_back(f);
            return pos_clos;
        }
        case Formula::X: {
            pos_clos = collect_positive_closure(f.lhs());
            pos_clos.push_back(f);
            return pos_clos;
        }
        case Formula::U: {
            pos_clos = collect_positive_closure(f.lhs());
            std::vector<Formula> r_pos_clos = collect_positive_closure(f.rhs());
            for (auto &f : r_pos_clos) {
                pos_clos.push_back(f);
            }
            pos_clos.push_back(f);
            return pos_clos;
        }
        default:
            return pos_clos;
    }
}

std::vector<Formula> remove_duplicates(const std::vector<Formula> vec) {
    std::vector<Formula> uniq_vec;
    for (auto &f : vec) {
        if (!find_formula(uniq_vec, f))
            uniq_vec.push_back(f);
    }

    return uniq_vec;
}

std::vector<Formula> get_full_closure (std::vector<Formula> pos_clos) {
    std::vector<Formula> closure = pos_clos;
    for (auto &f : pos_clos) {
        if (f.kind() == Formula::ATOM && f.prop() == TRUE)
            closure.push_back(P(FALSE));
        else if (f.kind() == Formula::ATOM && f.prop() == FALSE)
            closure.push_back(P(TRUE));
        else if (f.kind() == Formula::ATOM)
            closure.push_back(!(P(f.prop())));
        else
            closure.push_back(!f);
    }

    return closure;
}

std::vector<Formula> get_atoms (const std::vector<Formula> closure) {
    std::vector<Formula> atoms;
    for (auto &f : closure) {
        if ((f.kind() == Formula::X) || (f.kind() == Formula::ATOM && f.prop() != TRUE && f.prop() != FALSE))
            atoms.push_back(f);
    }

    return atoms;
}

void print_vector(const std::vector<Formula> vec, const std::string delimiter) {
    auto it = vec.begin();
    while (it != vec.end()) {
        std::cout << *it;
        if (std::next(it) != vec.end())
            std::cout << delimiter;

        ++it;
    }
    std::cout << std::endl;
}

std::vector<std::string> generateBinaryStrings(int n) {
    std::vector<std::string> binaryStringsArray;
    std::string binaryString = "";

    for(int i = 0; i < n; i++)
        binaryString += "0";
    binaryStringsArray.push_back(binaryString);

    for(int i = 1; i < pow(2, n); i++) {
        binaryString = "";

        int temp = i;
        for(int j = 0; j < n; j++) {
            binaryString.insert(0, std::to_string(temp % 2));
            temp = temp / 2;
        }

        binaryStringsArray.push_back(binaryString);
    }

    return binaryStringsArray;
}

std::map<std::string, std::vector<std::vector<Formula>>> init_formula_table(const std::vector<Formula> atoms, const std::vector<Formula> pos_clos) {
    std::vector<std::string> binaryStringsArray = generateBinaryStrings(atoms.size());
    std::map<std::string, std::vector<std::vector<Formula>>> initial_state_table;

    for (int i = 0; i < static_cast<int>(binaryStringsArray.size()); i++) {
        std::vector<Formula> true_atoms;
        initial_state_table.emplace(binaryStringsArray[i], std::vector<std::vector<Formula>>());

        for (int j = 0; j < static_cast<int>(binaryStringsArray[i].size()); j++) {
            if (binaryStringsArray[i][j] == '1')
                true_atoms.push_back(atoms[j]);
        }

        if (find_formula(pos_clos, P(TRUE)))
            true_atoms.push_back(P(TRUE));

        initial_state_table[binaryStringsArray[i]].push_back(true_atoms);
    }

    return initial_state_table;
}

bool calculates_formula_val(const std::vector<Formula> true_formulas, const Formula& f) {
    switch (f.kind()) {
        case Formula::ATOM: {
            if (f.prop() == TRUE || find_formula(true_formulas, f))
                return true;
            else
                return false;
        }
        case Formula::NOT: {
            Formula arg = f.arg();
            if (arg.kind() == Formula::ATOM && arg.prop() == TRUE)
                return false;
            else if (arg.kind() == Formula::ATOM && arg.prop() == FALSE)
                return true;
            else {
                if (calculates_formula_val(true_formulas, arg))
                    return false;
                else
                    return true;
            }
        }
        case Formula::AND: {
            Formula lhs = f.lhs();
            Formula rhs = f.rhs();
            if ((lhs.kind() == Formula::ATOM && lhs.prop() == FALSE) || (rhs.kind() == Formula::ATOM && rhs.prop() == FALSE))
                return false;
            else {
                if (!calculates_formula_val(true_formulas, lhs) || !calculates_formula_val(true_formulas, rhs))
                    return false;
                else
                    return true;
            }
        }
        case Formula::OR: {
            Formula lhs = f.lhs();
            Formula rhs = f.rhs();
            if ((lhs.kind() == Formula::ATOM && lhs.prop() == TRUE) || (rhs.kind() == Formula::ATOM && rhs.prop() == TRUE))
                return true;
            else {
                if (calculates_formula_val(true_formulas, lhs) || calculates_formula_val(true_formulas, rhs))
                    return true;
                else
                    return false;
            }
        }
        case Formula::X: {
            if (find_formula(true_formulas, f))
                return true;
            else
                return false;
        }
        case Formula::U: {
            if (find_formula(true_formulas, f))
                return true;
            else
                return false;
        }
        default:
            return false;
    }
}

std::map<std::string, std::vector<std::vector<Formula>>> extend_formula_table(std::map<std::string, std::vector<std::vector<Formula>>> state_table, const std::vector<Formula> pos_clos) {
    for (auto it = state_table.begin(); it != state_table.end(); it++) {
        for (auto &f : pos_clos) {
            if (f.kind() != Formula::ATOM && f.kind() != Formula::X) {
                if (f.kind() != Formula::U) {
                    for(int i = 0; i < static_cast<int>(it->second.size()); i++) {
                        if (calculates_formula_val(it->second[i], f)) {
                            it->second[i].push_back(f);
                        }
                    }
                } else {
                    std::vector<std::vector<Formula>> tmp_value;
                    for (auto &f_arr : it->second)
                        tmp_value.push_back(f_arr);

                    for(int i = 0; i < static_cast<int>(it->second.size()); i++) {
                        if (calculates_formula_val(it->second[i], f.rhs())) {
                            tmp_value[i].push_back(f);
                        } else if (calculates_formula_val(it->second[i], f.lhs())) {
                            tmp_value.push_back(it->second[i]);
                            int ind = static_cast<int>(tmp_value.size()) - 1;
                            tmp_value[ind].push_back(f);
                        }
                    }

                    it->second.clear();
                    for (auto &f_arr : tmp_value) 
                        it->second.push_back(f_arr);
                    tmp_value.clear();
                }
            }
        }
    }

    return state_table;
}

std::vector<std::vector<Formula>> get_states_formulas(const std::map<std::string, std::vector<std::vector<Formula>>> state_table) {
    std::vector<std::vector<Formula>> formulas_array;
    for (auto it = state_table.begin(); it != state_table.end(); it++) {
        for (auto &f_arr : it->second)
            formulas_array.push_back(f_arr);
    }

    return formulas_array;
}

std::map<std::string, std::vector<Formula>> get_all_states(const std::vector<Formula> pos_clos, const std::vector<Formula> atoms) {
    std::map<std::string, std::vector<std::vector<Formula>>> state_table = init_formula_table(atoms, pos_clos);
    state_table = extend_formula_table(state_table, pos_clos);

    std::map<std::string, std::vector<Formula>> states_info;
    std::vector<std::vector<Formula>> formulas_array = get_states_formulas(state_table);

    for (int i = 0; i < static_cast<int>(formulas_array.size()); i++) {
        std::string label_prefix = "s";
        if (i < 10)
            label_prefix += "0";
        std::string label = label_prefix + std::to_string(i);

        states_info.emplace(label, std::vector<Formula>());
        for (auto &f : formulas_array[i])
            states_info[label].push_back(f);
    }

    return states_info;
}

void automaton_add_states(Automaton& automaton, std::map<std::string, std::vector<Formula>> states) {
    for (auto it = states.begin(); it != states.end(); it++) {
        automaton.add_state(it->first);
    }
}

void automaton_set_initial_states(Automaton& automaton, std::map<std::string, std::vector<Formula>> states, const Formula& f) {
    for (auto it = states.begin(); it != states.end(); it++) {
        if ((f.kind() == Formula::NOT && !find_formula(it->second, f.arg())) || (find_formula(it->second, f)))
            automaton.set_initial(it->first);
    }
}

std::vector<Formula> get_until_formulas (const std::vector<Formula> closure) {
    std::vector<Formula> untils;
    for (auto const &f : closure) {
        if (f.kind() == Formula::U)
            untils.push_back(f);
    }
    
    return untils;
}

void automaton_set_final_states(Automaton& automaton, std::map<std::string, std::vector<Formula>> states, std::vector<Formula> pos_clos) {
    int i = 0;
    for (auto &until_f : get_until_formulas(pos_clos)) {
        for (auto it = states.begin(); it != states.end(); it++) {
            if (!find_formula(it->second, until_f) || 
                (find_formula(it->second, until_f) && (find_formula(it->second, until_f.rhs()) || (until_f.rhs().kind() == Formula::NOT && !find_formula(it->second, until_f.rhs().arg())))))
                    automaton.set_final(it->first, i);
        }
        i += 1;
    }
}

std::vector<Formula> get_next_formulas (const std::vector<Formula> closure) {
    std::vector<Formula> nexts;
    for (auto const &f : closure) {
        if (f.kind() == Formula::X)
            nexts.push_back(f);
    }
    
    return nexts;
}

bool check_next_trans_conditions(std::vector<Formula> next_formulas, std::vector<Formula> source, std::vector<Formula> target) {
    for (auto const &f : next_formulas) {
        if ((find_formula(source, f) && !find_formula(target, f.arg())) || 
            (!find_formula(source, f) && find_formula(target, f.arg())))
                return false;
    }

    return true;
}

bool check_until_trans_conditions(std::vector<Formula> until_formulas, std::vector<Formula> source, std::vector<Formula> target) {
    for (auto const &f : until_formulas) {
        bool left_condition = find_formula(source, f);
        bool right_condition = ((find_formula(source, f.rhs()) || (f.rhs().kind() == Formula::NOT && !find_formula(source, f.rhs().arg()))) || (find_formula(target, f) && (find_formula(source, f.lhs()) || (f.lhs().kind() == Formula::NOT && !find_formula(source, f.lhs().arg())))));
        
        if (left_condition != right_condition)
            return false;
    }

    return true;
}

std::map<std::string, std::set<std::string>> get_all_transitions(std::map<std::string, std::vector<Formula>> states, std::vector<Formula> pos_clos) {
    std::map<std::string, std::set<std::string>> transitions;
    for (auto it_source = states.begin(); it_source != states.end(); it_source++) {
        std::set<std::string> trans_for_state;
        std::vector<Formula> next_formulas = get_next_formulas(pos_clos);
        std::vector<Formula> until_formulas = get_until_formulas(pos_clos);
        if (next_formulas.size() || until_formulas.size()) {
            for (auto it_target = states.begin(); it_target != states.end(); it_target++) {
                if (check_next_trans_conditions(next_formulas, it_source->second, it_target->second) && check_until_trans_conditions(until_formulas, it_source->second, it_target->second))
                    trans_for_state.insert(it_target->first);
            }
        } else {
            for (auto it_target = states.begin(); it_target != states.end(); it_target++) {
                trans_for_state.insert(it_target->first);
            }
        }
        transitions[it_source->first] = trans_for_state;
    }

    return transitions;
}

std::set<std::string> get_transition_marks(std::vector<Formula> vec) {
    std::set<std::string> marks;
    for (auto const &f : vec) {
        if (f.kind() == Formula::ATOM && f.prop() != TRUE)
            marks.insert(f.prop());
    }
    
    return marks;
}

void automaton_add_transitions(Automaton& automaton, std::map<std::string, std::set<std::string>> transitions, std::map<std::string, std::vector<Formula>> states) {
    for (auto it = transitions.begin(); it != transitions.end(); it++) {
        std::set<std::string> marks = get_transition_marks(states[it->first]);
        for (auto const &target : it->second)
            automaton.add_trans(it->first, marks, target);
    }
}

Automaton construct_automaton(std::vector<Formula> pos_clos, std::vector<Formula> atoms, const Formula& f) {
    Automaton automaton;

    std::map<std::string, std::vector<Formula>> states = get_all_states(pos_clos, atoms);
    std::cout << "States: \n";
    for (auto it = states.begin(); it != states.end(); it++) {
        std::cout << "     " << it->first << ": ";
        print_vector(it->second, ", ");
    }

    std::map<std::string, std::set<std::string>> transitions = get_all_transitions(states, pos_clos);

    automaton_add_states(automaton, states);
    automaton_set_initial_states(automaton, states, f);
    automaton_set_final_states(automaton, states, pos_clos);
    automaton_add_transitions(automaton, transitions, states);

    return automaton;
}

void convert(const Formula& f) {
    std::cout << "------------------------------------------------------------------------------------------------------------------------------" << std::endl;
    std::cout << "Source formula: " << f << std::endl;
    
    const Formula& simpf = simplify_ltl(f);
    std::cout << "Simplified formula: " << simpf << std::endl;
    
    std::vector<Formula> pos_clos = remove_duplicates(collect_positive_closure(simpf));
    std::vector<Formula> closure = get_full_closure(pos_clos);
    std::cout << "Closure: \n     ";
    print_vector(closure, "\n     ");
    
    std::vector<Formula> atoms = get_atoms(closure);
    std::cout << "Atoms: \n     ";
    print_vector(atoms, "\n     ");

    const Automaton automaton = construct_automaton(pos_clos, atoms, simpf);
    std::cout << "Automaton: " << std::endl;
    std::cout << automaton << std::endl;
}

} // namespace model::converter
