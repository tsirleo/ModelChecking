#include <algorithm>
#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <cmath>
#include <stack>

enum Bool {
    FALSE,
    TRUE,
    UNDEF,
};

typedef std::vector<int> VINT;
typedef std::vector<VINT> CNF;
typedef std::vector<Bool> VBOOL;

bool is_in_vector(int var, const VINT& vec) {
    return std::find(vec.begin(), vec.end(), var) != vec.end();
}

bool vector_exists(const CNF& cnf, const VINT& vec) {
    return std::find(cnf.begin(), cnf.end(), vec) != cnf.end();
}

void read_cnf(std::string& inputFile, CNF& cnf, VBOOL& variables, VBOOL& clauses, bool& unsat_flag, bool& read_err) {
    std::ifstream file(inputFile);
    if (!file.is_open()) {
        read_err = true;
        return;
    }

    std::string line;
    while (getline(file, line)) {
        if (line == "" || line[0] == 'c' || line[0] == '%' || line == "0")
            continue;
        else
            break;
    }
    int numVars, numClauses;
    if (line.substr(0, 5) != "p cnf") {
        std::cerr << "Invalid input format" << std::endl;
        return;
    }
    sscanf(line.c_str(), "p cnf %d %d", &numVars, &numClauses);
    std::cout << "Number of variables = " << numVars << std::endl;
    std::cout << "Number of clauses = " << numClauses << std::endl;

    variables = VBOOL(numVars, UNDEF);
    clauses = VBOOL(numClauses, UNDEF);

    cnf = CNF(numClauses);
    int ind = 0;
    for (int i = 0; i < numClauses; ++i) {
        getline(file, line);
        int literal;
        std::istringstream iss(line);
        VINT disjuncts;
        while (iss >> literal && literal != 0) {
            disjuncts.push_back(literal);
        }

        if (vector_exists(cnf, disjuncts))
            continue;
        else {
            if (static_cast<int>(disjuncts.size()) == 1) {
                int jnd = disjuncts[0];
                if (variables[abs(jnd) - 1] == UNDEF) {
                    if (jnd > 0) { 
                        variables[jnd - 1] = TRUE;
                    } else {
                        variables[abs(jnd) - 1] = FALSE;
                    }
                    clauses[ind] = TRUE;
                } else {
                    unsat_flag = true;
                    return;
                }
            }

            cnf[ind] = disjuncts;
            ind += 1;
        }
        disjuncts.clear();
    }
    cnf.resize(ind);
    clauses.resize(ind);

    file.close();
}

void get_defined_vars_indeces(const VBOOL& variables, VINT& vec) {
    for (int i = 0; i < static_cast<int>(variables.size()); ++i) {
        if (variables[i] != UNDEF)
            vec.push_back(i + 1);
    }
}

void get_undefined_clauses_indeces(const VBOOL& clauses, VINT& vec) {
    for (int i = 0; i < static_cast<int>(clauses.size()); ++i) {
        if (clauses[i] == UNDEF)
            vec.push_back(i);
    }
}

int get_undefined_clauses_num(const VBOOL& clauses) {
    int count = 0;
    for (int i = 0; i < static_cast<int>(clauses.size()); ++i) {
        if (clauses[i] == UNDEF)
            count += 1;
    }

    return count;
}

int get_undefined_vars_num(const VBOOL& variables, const VINT& clause) {
    int count = 0;
    for (int i = 0; i < static_cast<int>(clause.size()); ++i) {
        if (variables[abs(clause[i]) - 1] == UNDEF)
            count += 1;
    }

    return count;
}

int get_undefined_var_position(const VBOOL& variables, const VINT& clause) {
    for (int i = 0; i < static_cast<int>(clause.size()); ++i) {
        if (variables[abs(clause[i]) - 1] == UNDEF)
            return i;
    }

    return 0;
}

void init_propagate_units(CNF& cnf, VBOOL& variables, VBOOL& clauses, bool& unsat_flag) {
    VINT defined_vars_vec; 
    int n_disjuncts = static_cast<int>(cnf.size());
    get_defined_vars_indeces(variables, defined_vars_vec);

    int ind = 0;
    int var;
    int size = static_cast<int>(defined_vars_vec.size());

    while (ind < size) {
        var = defined_vars_vec[ind];
        for (int i = 0; i < n_disjuncts; ++i) {
            if (static_cast<int>(cnf[i].size()) > 1) {
                if (clauses[i] == UNDEF && ((variables[var - 1] == TRUE && is_in_vector(var, cnf[i])) || (variables[var - 1] == FALSE && is_in_vector(-var, cnf[i]))))
                    clauses[i] = TRUE;
                else if (variables[var - 1] == TRUE && is_in_vector(-var, cnf[i])) { 
                    cnf[i].erase(std::remove(cnf[i].begin(), cnf[i].end(), -var), cnf[i].end());
                    if (static_cast<int>(cnf[i].size()) == 1) {
                        if (cnf[i][0] > 0 && variables[cnf[i][0] - 1] != FALSE) {
                            variables[cnf[i][0] - 1] = TRUE;
                            clauses[i] = TRUE;
                        }
                        else if (cnf[i][0] < 0 && variables[abs(cnf[i][0]) - 1] != TRUE) {
                            variables[abs(cnf[i][0]) - 1] = FALSE;
                            clauses[i] = TRUE;
                        }
                        else {
                            unsat_flag = true;
                            return;
                        }

                        if (!is_in_vector(abs(cnf[i][0]), defined_vars_vec)) {
                            defined_vars_vec.push_back(abs(cnf[i][0]));
                            size += 1;
                        }
                    }
                } else if (variables[var - 1] == FALSE && is_in_vector(var, cnf[i])) {
                    cnf[i].erase(std::remove(cnf[i].begin(), cnf[i].end(), var), cnf[i].end());
                    if (static_cast<int>(cnf[i].size()) == 1) {
                        if (cnf[i][0] > 0 && variables[cnf[i][0] - 1] != FALSE) {
                            variables[cnf[i][0] - 1] = TRUE;
                            clauses[i] = TRUE;
                        }
                        else if (cnf[i][0] < 0 && variables[abs(cnf[i][0]) - 1] != TRUE) {
                            variables[abs(cnf[i][0]) - 1] = FALSE;
                            clauses[i] = TRUE;
                        }
                        else {
                            unsat_flag = true;
                            return;
                        }

                        if (!is_in_vector(abs(cnf[i][0]), defined_vars_vec)) {
                            defined_vars_vec.push_back(abs(cnf[i][0]));
                            size += 1;
                        }
                    }
                }
            }
        }
        ind += 1;
    }
}

bool check_clause(const VINT& clause, const VBOOL& variables) {
    for (auto& var : clause) {
        if (variables[abs(var) - 1] == UNDEF) 
            continue;
        else if (var > 0 && variables[var - 1] == TRUE)
            return true;
        else if (var < 0 && variables[abs(var) - 1] == FALSE)
            return true;
    }

    return false;
}

int get_var_to_propagate(VBOOL& variables) {
    for (int i = 0; i < static_cast<int>(variables.size()); ++i) {
        if (variables[i] == UNDEF) {
            return i + 1;
        }
    }
    
    return 0;
}

void propagate_unit(const CNF& cnf, VBOOL& variables, std::stack<VINT>& variables_st, VBOOL& clauses, std::stack<VINT>& clauses_st, int& prop_var, Bool& prop_var_val, bool& unsat_flag) {
    VINT defined_vars_vec, undefined_clauses_vec, changed_clauses, changed_vars; 
    int var, pos, undef_vars_num;
    int ind = 0;
    unsat_flag = false;

    variables[prop_var - 1] = prop_var_val;
    defined_vars_vec.push_back(prop_var);
    int size = 1;

    while (ind < size) {
        var = defined_vars_vec[ind];
        get_undefined_clauses_indeces(clauses, undefined_clauses_vec);
        for (int i : undefined_clauses_vec) {
            if ((variables[var - 1] == TRUE && is_in_vector(var, cnf[i])) || (variables[var - 1] == FALSE && is_in_vector(-var, cnf[i]))) {
                clauses[i] = TRUE;
                changed_clauses.push_back(i);
            }
            else if ((variables[var - 1] == TRUE && is_in_vector(-var, cnf[i])) || (variables[var - 1] == FALSE && is_in_vector(var, cnf[i]))) { 
                undef_vars_num = get_undefined_vars_num(variables, cnf[i]);
                if (undef_vars_num == 1 && !check_clause(cnf[i], variables)) {
                    pos = get_undefined_var_position(variables, cnf[i]);
                    if (cnf[i][pos] > 0) {
                        variables[cnf[i][pos] - 1] = TRUE;
                        clauses[i] = TRUE;
                        changed_clauses.push_back(i);
                        changed_vars.push_back(cnf[i][pos]);
                    }
                    else if (cnf[i][pos] < 0) {
                        variables[abs(cnf[i][pos]) - 1] = FALSE;
                        clauses[i] = TRUE;
                        changed_clauses.push_back(i);
                        changed_vars.push_back(abs(cnf[i][pos]));
                    }

                    defined_vars_vec.push_back(abs(cnf[i][pos]));
                    size += 1;
                } else if (undef_vars_num == 0) {
                    if (check_clause(cnf[i], variables)) {
                        clauses[i] = TRUE;
                        changed_clauses.push_back(i);
                    }
                    else {
                        clauses_st.push(changed_clauses);
                        variables_st.push(changed_vars);
                        unsat_flag = true;
                        return;
                    }
                } else {
                    continue;
                }
            }
        }
        undefined_clauses_vec.clear();
        ind += 1;
    }

    clauses_st.push(changed_clauses);
    variables_st.push(changed_vars);
}

void rollback_min(VBOOL& variables, std::stack<VINT>& variables_st, VBOOL& clauses, std::stack<VINT>& clauses_st) {
    if (!variables_st.empty()) {
        for (auto& var : variables_st.top()) {
            variables[var - 1] = UNDEF;
        }

        variables_st.pop();
    }

    if (!clauses_st.empty()) {
        for (auto& ind : clauses_st.top()) {
            clauses[ind] = UNDEF;
        }

        clauses_st.pop();
    }
}

bool rollback_max(std::stack<std::pair<int, Bool>>& propageted_vars_st, VBOOL& variables, std::stack<VINT>& variables_st, VBOOL& clauses, std::stack<VINT>& clauses_st) {
    std::pair<int, Bool> prop_var;
    std::pair<int, Bool> pre_var;

    while (!propageted_vars_st.empty()) {
        rollback_min(variables, variables_st, clauses, clauses_st);
        prop_var = propageted_vars_st.top();
        propageted_vars_st.pop();

        if (propageted_vars_st.empty() && prop_var.second == FALSE)
            return false;

        variables[prop_var.first - 1] = UNDEF;
        pre_var = propageted_vars_st.top();

        if (pre_var.second == TRUE) {
            rollback_min(variables, variables_st, clauses, clauses_st);
            pre_var.second = FALSE;
            propageted_vars_st.pop();
            propageted_vars_st.push(pre_var);
            return true;
        }
    }

    return true;
}

bool dpll(CNF& cnf, VBOOL& variables, VBOOL& clauses, bool& unsat_flag) {
    init_propagate_units(cnf, variables, clauses, unsat_flag);
    if (unsat_flag)
        return false;

    int var;
    std::stack<VINT> clauses_st;
    std::stack<VINT> variables_st;
    std::pair<int, Bool> prop_var;
    std::stack<std::pair<int, Bool>> propageted_vars_st;

    while(true) {
        if (!get_undefined_clauses_num(clauses)) {
            break;
        } else {
            var = get_var_to_propagate(variables);
            prop_var = std::make_pair(var, TRUE);
            propagate_unit(cnf, variables, variables_st, clauses, clauses_st, prop_var.first, prop_var.second, unsat_flag);
            if (unsat_flag) {
                rollback_min(variables, variables_st, clauses, clauses_st);
                prop_var.second = FALSE;
                propageted_vars_st.push(prop_var);
                propagate_unit(cnf, variables, variables_st, clauses, clauses_st, prop_var.first, prop_var.second, unsat_flag);
                if (unsat_flag) {
                    while (true) {
                        if (rollback_max(propageted_vars_st, variables, variables_st, clauses, clauses_st)) {
                            prop_var = propageted_vars_st.top();
                            propagate_unit(cnf, variables, variables_st, clauses, clauses_st, prop_var.first, prop_var.second, unsat_flag);
                            if (!unsat_flag)
                                break;
                        } else {
                            return false;
                        }
                    }
                }
            } else {
                propageted_vars_st.push(prop_var);
            }
        }  
    }

    return true;
}

std::string extract_filename(const std::string& path) {
    size_t separatorPos = path.find_last_of("/\\");
    size_t extensionPos = path.find_last_of(".");
    
    if (extensionPos != std::string::npos && (separatorPos == std::string::npos || extensionPos > separatorPos)) {
        return path.substr(separatorPos + 1, extensionPos - separatorPos - 1);
    }
    
    return path.substr(separatorPos + 1);
}

int main(int argc, char* argv[]) {
    if (argc < 2) {
        std::cerr << "Invalid number of arguments. You must specify the path to the test input file." << std::endl;
        return 1;
    }

    std::string inputFile;
    if (argv[1][0] == '/')
        inputFile = std::string(&argv[1][1]);
    else
        inputFile = std::string(argv[1]);

    CNF cnf;
    VBOOL variables;
    VBOOL clauses;
    bool unsat_flag = false;
    bool read_err = false;

    read_cnf(inputFile, cnf, variables, clauses, unsat_flag, read_err);
    if (read_err) {
        std::cerr << "Error opening file " << inputFile << std::endl;
    } else if (unsat_flag) {
        std::cout << "Result = UNSAT" << std::endl;
    } else {
        clock_t t_start = clock();
        if (dpll(cnf, variables, clauses, unsat_flag)) {
            std::cout << "Result = SAT" << std::endl;
        }
        else
            std::cout << "Result = UNSAT" << std::endl;
        clock_t t_end = clock();

        double time = double(t_end - t_start) / CLOCKS_PER_SEC;
        std::cout << "Working time of the '" << extract_filename(inputFile) << "' test = " << time << " sec" << std::endl;
    }
    
    return 0;
}