/*
 * Copyright 2021 ISP RAS (http://www.ispras.ru)
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
 * in compliance with the License. You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software distributed under the License
 * is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express
 * or implied. See the License for the specific language governing permissions and limitations under
 * the License.
 */

#include "converter.h"

using namespace model::converter;

// int main() {
//     const Formula &formula = G(P("p") >> F(P("q")));

//     std::cout << "Formula: " << std::endl;
//     std::cout << formula << std::endl << std::endl;

//     Automaton automaton;
//     automaton.add_state("s0");
//     automaton.add_state("s1");
//     automaton.add_state("s2");
//     automaton.set_initial("s0");
//     automaton.set_final("s1", 0);
//     automaton.set_final("s2", 1);
//     automaton.add_trans("s0", {"p"}, "s1");
//     automaton.add_trans("s0", {"q"}, "s2");
//     automaton.add_trans("s1", {}, "s0");
//     automaton.add_trans("s1", {"p", "q"}, "s2");
//     automaton.add_trans("s2", {}, "s2");

//     std::cout << "Automaton: " << std::endl;
//     std::cout << automaton << std::endl;

//     return 0;
// }

int main() {
    convert(P(TRUE));
    convert(P(FALSE));
    convert(P("p"));
    convert(X(P("p")));
    convert(F(P("p"))); 
    convert(G(F(X(P("p")))));
    convert(F(P("p")) || P("q"));
    convert(U(P(TRUE), P(FALSE)));
    convert(U(P("p"), X(P("q"))));
    convert(G(P("p") >> X(P("q"))));
    convert(G(P("p") >> F(P("q"))));
    convert(F(P("p") >> X(!(P("q")))));
    convert(P("x") || !U(P("y"), P("z")));
    convert((P("p") && P("p")) || P("d"));
    convert(U(P("x"), U(P("y"), P("z"))));
    convert(U(P("true"), P("p")) || P("q"));
    convert(!U(P("true"), P("p")) || P("q"));
    convert(U((P("p") || P("q")), (P("p") && P("q"))));
    convert(X((P("false") && P("false")) || P("true")));
    convert(G(P("p") >> (!P("q") && (U(X(!P("p")), P("q"))))));
    convert(F(P("p") >> (!P("q") && (X(U(!P("p"), P("q")))))));
    convert(G(P("p") >> (!P("q") && (U(X(!P("p")), X(P("q")))))));
    return 0;
}
