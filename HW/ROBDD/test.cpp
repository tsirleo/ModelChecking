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

#include <cassert>
#include <iostream>

#include "bdd.h"
#include "formula.h"

using namespace model::bdd;
using namespace model::logic;

// int main() {
//   const Formula &formula1 =  x(0) >>  x(1);
//   const Formula &formula2 = !x(1) >> !x(0);
//   const Formula &formula3 = formula1 == formula2;
//   const Formula &formula4 = T;

//   std::cout << "Formulae: " << std::endl;
//   std::cout << formula1 << std::endl;
//   std::cout << formula2 << std::endl;
//   std::cout << formula3 << std::endl;
//   std::cout << formula4 << std::endl;
 
//   Bdd bdd;
 
//   const Node& root1 = bdd.create(formula1);
//   const Node& root2 = bdd.create(formula2);
//   assert(&root1 == &root2);

//   const Node& root3 = bdd.create(formula3);
//   const Node& root4 = bdd.create(formula4);
//   assert(&root3 == &root4);

//   return 0;
// }

enum PrintStyle {
    VERTICAL, // Constant false
    HORISONTAL,  // Constant true
};

const Node& create_and_print_bdd(const Formula&  f, PrintStyle style) {
    Bdd bdd;
    std::cout << "------------------------------------------------------------------------------------------------------------------------------" << std::endl;
    std::cout << "Source formula: " << f << std::endl;
    const Node& root_node = bdd.create(f);
    std::cout << "BDD tree: " << std::endl;
    switch (style) {
        case VERTICAL:
            bdd_print_vertical(&root_node);
            break;
        case HORISONTAL:
            bdd_print_horizontal(&root_node);
            break;
        default:
            break;
    }
    std::cout << std::endl;

    return root_node;
}

int main() {
    PrintStyle style = VERTICAL;
    create_and_print_bdd(T, style);
    create_and_print_bdd(F, style);
    create_and_print_bdd(x(1), style);
    create_and_print_bdd(!x(1), style);
    create_and_print_bdd(x(1) ||  x(2), style);
    create_and_print_bdd(x(1) &&  x(2), style);
    create_and_print_bdd(x(1) == x(2), style);
    create_and_print_bdd(x(1) != x(2), style);
    create_and_print_bdd(x(1) >>  x(2), style);
    create_and_print_bdd(!x(2) >> !x(1), style);
    create_and_print_bdd((x(1) >>  x(2)) == (!x(2) >> !x(1)), style);
    create_and_print_bdd((x(1) && x(2)) || (x(3) && x(4)) || (x(5) && x(6)), style);
    create_and_print_bdd((x(1) && x(4)) || (x(2) && x(5)) || (x(3) && x(5)), style);
    create_and_print_bdd((x(1) || x(2)) && (x(3) || x(4)) && (x(5) || x(6)), style);
    create_and_print_bdd((x(1) || x(4)) && (x(2) || x(5)) && (x(3) || x(5)), style);
    create_and_print_bdd((x(3) != x(6)) != ((x(2) && x(5)) || (x(2) && x(4) && x(1)) || (x(5) && x(4) && x(1))), HORISONTAL);
    create_and_print_bdd(x(7) >> (x(3) != x(6)) != ((x(2) && x(5)) || (x(2) && x(4) && x(1)) || (x(5) && x(4) && x(1))), HORISONTAL);

    return 0;
}
