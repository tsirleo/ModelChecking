#include <algorithm>
#include <iostream>
#include <fstream>
#include <sstream>
#include <vector>
#include <cmath>
#include <map>

enum Status {
    SAT,
    UNSAT,
    UNRES,
};

typedef std::vector<int> VINT;
typedef std::vector<VINT> CNF;

class DPLL {
    private:
        int root_level = 1, numVars = 0, numClauses = 0, not_propageted_var = 0; 
        Status status = Status::UNRES;

        VINT defined_vars, undefined_vars, level_assigned_vars;
        CNF cnf;

        std::map<int, int> vars_scheme, var_set_at_level, var_assign_cause_clause;
        std::map<int, VINT> var_watch_clauses;
        std::map<int, bool> vars_analyze_queue;

        Status set_status(Status st) {
            status = st;
            return status;
        }

        void add_var(const int &var, const int &clause_ind = 0) {
            defined_vars.push_back(var);
            vars_scheme[abs(var)] = var;
            var_set_at_level[abs(var)] = level_assigned_vars.size();
            var_assign_cause_clause[abs(var)] = clause_ind;
        }

        int add_clause(const VINT &clause) {
            if (clause.size() == 1) {
                add_var(clause[0]);
                return 0;
            } else {
                cnf.push_back(clause);
                var_watch_clauses[clause[0]].push_back(cnf.size());
                var_watch_clauses[clause[1]].push_back(cnf.size());
                return cnf.size();
            }
        }

        int select_var() {
            int var = 0;
            do {
                if (undefined_vars.empty())
                    return 0;
                
                var = undefined_vars.back();
                undefined_vars.pop_back();

                if (!var)
                    break;
            } while (vars_scheme[var]);

            return var;
        }

        int propagate_unit(const int &var) {
            int conflict = 0;
            bool continue_flag;
            auto &watch_cl = var_watch_clauses[-var];
            auto watch_cl_end = watch_cl.end();
            for (auto it = watch_cl.begin(); it != watch_cl_end; ++it) {
                auto &clause = cnf[*it - 1];
                if (var == -clause[0])
                    std::swap(clause[0], clause[1]);

                if (vars_scheme[abs(clause[0])] == clause[0])
                    continue;

                continue_flag = false;
                for (size_t i = 2; i < clause.size(); ++i) {
                    if (vars_scheme[abs(clause[i])] != -clause[i]) {
                        std::swap(clause[1], clause[i]);
                        var_watch_clauses[clause[1]].push_back(*it);
                        std::swap(*it--, *--watch_cl_end);
                        continue_flag = true;
                        break;
                    }
                }
                if (continue_flag)
                    continue;

                if (vars_scheme[abs(clause[0])] == -clause[0]) {
                    not_propageted_var = defined_vars.size();
                    conflict = *it;
                    break;
                } else {
                    if (vars_scheme[abs(clause[0])] != clause[0])
                        add_var(clause[0], *it);
                }
            }

            watch_cl.resize(watch_cl_end - watch_cl.begin());
            return conflict;
        }

        int propagate() {
            int conflict = 0;
            if (!defined_vars.empty()) {
                do {
                    auto x = defined_vars[not_propageted_var++];
                    conflict = propagate_unit(x);
                } while (not_propageted_var < static_cast<int>(defined_vars.size()) && !conflict);
            }
            return conflict;
        }

        void conflict_analysis(int &conflict, VINT &learnt_clauses, int &rb_level) {
            int size = 0, uip = 0, i = defined_vars.size() - 1;
            learnt_clauses.emplace_back();

            do {
                for (auto &disjunct : cnf[conflict - 1]) {
                    if (uip == disjunct)
                        continue;
                
                    if (!vars_analyze_queue[abs(disjunct)] && var_set_at_level[abs(disjunct)] > root_level) {
                        vars_analyze_queue[abs(disjunct)] = true;
                        if (var_set_at_level[abs(disjunct)] >= static_cast<int>(level_assigned_vars.size()))
                            size += 1;
                        else
                            learnt_clauses.push_back(disjunct);
                    }
                }

                while (!vars_analyze_queue[abs(defined_vars[i])]) {
                    i -= 1;
                }

                uip = defined_vars[i];
                i -= 1;
                conflict = var_assign_cause_clause[abs(uip)];
                vars_analyze_queue[abs(uip)] = false;
                size -= 1;
            } while (size > 0);
            learnt_clauses[0] = -uip;

            for (auto &disjunct : learnt_clauses) {
                vars_analyze_queue[abs(disjunct)] = false;
            }

            if (learnt_clauses.size() == 1) {
                rb_level = root_level;
            } else {
                int max = 1;
                rb_level = var_set_at_level[abs(learnt_clauses[max])];
                for (size_t i = 2; i < learnt_clauses.size(); ++i) {
                    if (rb_level < var_set_at_level[abs(learnt_clauses[i])]) {
                        rb_level = var_set_at_level[abs(learnt_clauses[i])];
                        max = i;
                    }
                }
                std::swap(learnt_clauses[1], learnt_clauses[max]);
            }
        }

        void rollback(const int &to_level) {
            for (auto it = defined_vars.cbegin() + level_assigned_vars[to_level]; it != defined_vars.cend(); ++it) {
                if (std::find(undefined_vars.begin(), undefined_vars.end(), abs(*it)) == undefined_vars.end())
                    undefined_vars.emplace_back(abs(*it));

                vars_scheme[abs(*it)] = 0;
            }
            defined_vars.resize(level_assigned_vars[to_level]);
            not_propageted_var = defined_vars.size();
            level_assigned_vars.resize(to_level);
        }

    public:
        void read_cnf(std::string& inputFile) {
            std::ifstream file(inputFile);
            if (!file.is_open())
                throw("Error opening file '" + inputFile + "'");

            std::string line;
            while (getline(file, line)) {
                if (line == "" || line[0] == 'c' || line[0] == '%' || line == "0")
                    continue;
                else
                    break;
            }
            if (line.substr(0, 5) != "p cnf")
                throw("Invalid input format");

            sscanf(line.c_str(), "p cnf %d %d", &numVars, &numClauses);
            std::cout << "Number of variables = " << numVars << std::endl;
            std::cout << "Number of clauses = " << numClauses << std::endl;

            level_assigned_vars.push_back(0);
            for (int i = 1; i <= numVars; ++i) {
                undefined_vars.emplace_back(abs(i));
            }

            VINT disjuncts;
            int literal;
            for (int i = 0; i < numClauses; ++i) {
                getline(file, line);
                std::istringstream iss(line);
                while (iss >> literal && literal != 0) {
                    disjuncts.push_back(literal);
                }

                if (!disjuncts.empty())
                    add_clause(disjuncts);

                disjuncts.clear();
            }

            file.close();
        }

        Status solve() {
            while(true) {
                auto conflict = propagate();
                if (conflict) {
                    if (static_cast<int>(level_assigned_vars.size()) == root_level)
                        return set_status(Status::UNSAT);

                    VINT learnt_clauses;
                    int rb_level;
                    conflict_analysis(conflict, learnt_clauses, rb_level);
                    rollback(rb_level);

                    if (learnt_clauses.size() == 1)
                        add_var(learnt_clauses[0]);
                    else
                        add_var(learnt_clauses[0], add_clause(learnt_clauses));
                } else {
                    int var = select_var();
                    if (!var) 
                        return set_status(Status::SAT);

                    level_assigned_vars.push_back(defined_vars.size()); 
                    add_var(-var);
                }
            }
        }

        void print_solution() {
            if (status == Status::SAT) {
                int var;
                for (int i = 1; i <= numVars; ++i) {
                    var = vars_scheme[abs(i)];
                    if (var > 0)
                        std::cout << var << " == 1" << std::endl;
                    else
                        std::cout << abs(var) << " == 0" << std::endl;
                }
                std::cout << "end" << std::endl;
            }
        }
};

std::string extract_filename(const std::string& path) {
    size_t separatorPos = path.find_last_of("/\\");
    size_t extensionPos = path.find_last_of(".");
    
    if (extensionPos != std::string::npos && (separatorPos == std::string::npos || extensionPos > separatorPos))
        return path.substr(separatorPos + 1, extensionPos - separatorPos - 1);
    
    return path.substr(separatorPos + 1);
}

int main(int argc, char *argv[]) {
    if (argc < 2) {
        std::cerr << "Invalid number of arguments. You must specify the path to the test input file." << std::endl;
        return 1;
    } else {
        std::cout << "---------------------------------------------------------------------" << std::endl;
    }

    DPLL solver;
    Status status;
    std::string inputFile;
    if (argv[1][0] == '/')
        inputFile = std::string(&argv[1][1]);
    else
        inputFile = std::string(argv[1]);

    try {
        solver.read_cnf(inputFile);
        clock_t t_start = clock();
        while(true) {
            status = solver.solve();
            if (status == Status::SAT) {
                std::cout << "Result = SAT" << std::endl;
                // solver.print_solution();
                break;
            } else if (status == Status::UNSAT) {
                std::cout << "Result = UNSAT" << std::endl;
                break;
            } else {
                continue;
            }
        }
        clock_t t_end = clock();

        double time = double(t_end - t_start) / CLOCKS_PER_SEC;
        std::cout << "Working time of the '" << extract_filename(inputFile) << "' test = " << time << " sec" << std::endl;
    }
    catch (std::string err) {
        std::cerr << err << std::endl;
    }

    std::cout << "---------------------------------------------------------------------" << std::endl;
    return 0;
}