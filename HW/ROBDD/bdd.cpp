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

#include "bdd.h"

namespace model::bdd {

const Node Bdd::zero(INT_MIN, nullptr, nullptr);
const Node Bdd::one (INT_MAX, nullptr, nullptr);

const Formula& apply(const Formula &f, int var, bool val) {
    switch (f.kind()) {
        case Formula::FALSE:
            return F;
        case Formula::TRUE:
            return T;
        case Formula::VAR: {
            if (f.var() == var)
              return val ? T : F;
            else
                return f;
        }
        case Formula::NOT: {
            Formula arg = apply(f.arg(), var, val);
            if (arg.kind() == Formula::TRUE)
                return F;
            else if (arg.kind() == Formula::FALSE)
                return T;
            else
              return !apply(f.arg(), var, val);
        }
        case Formula::AND: {
            Formula lhs = apply(f.lhs(), var, val);
            Formula rhs = apply(f.rhs(), var, val);
            if ((lhs.kind() == Formula::FALSE) || (rhs.kind() == Formula::FALSE))
                return F;
            else if (lhs.kind() == Formula::TRUE)
                return apply(f.rhs(), var, val);
            else if (rhs.kind() == Formula::TRUE)
                return apply(f.lhs(), var, val);
            else
                return apply(f.lhs(), var, val) && apply(f.rhs(), var, val);
        }
        case Formula::OR: {
            Formula lhs = apply(f.lhs(), var, val);
            Formula rhs = apply(f.rhs(), var, val);
            if ((lhs.kind() == Formula::TRUE) || (rhs.kind() == Formula::TRUE))
                return T;
            else if (lhs.kind() == Formula::FALSE)
                return apply(f.rhs(), var, val);
            else if (rhs.kind() == Formula::FALSE)
                return apply(f.lhs(), var, val);
            else
                return apply(f.lhs(), var, val) || apply(f.rhs(), var, val);
        }
        case Formula::XOR: {
            Formula lhs = apply(f.lhs(), var, val);
            Formula rhs = apply(f.rhs(), var, val);
            if ((lhs.kind() == Formula::FALSE && rhs.kind() == Formula::TRUE) || (lhs.kind() == Formula::TRUE && rhs.kind() == Formula::FALSE))
                return T;
            else if ((lhs.kind() == Formula::FALSE && rhs.kind() == Formula::FALSE) || (lhs.kind() == Formula::TRUE && rhs.kind() == Formula::TRUE))
                return F;
            else
                return apply(f.lhs(), var, val) != apply(f.rhs(), var, val);
        }
        case Formula::IMPL: {
            Formula lhs = apply(f.lhs(), var, val);
            Formula rhs = apply(f.rhs(), var, val);
            if ((lhs.kind() == Formula::FALSE) || (rhs.kind() == Formula::TRUE))
                return T;
            else if ((lhs.kind() == Formula::TRUE) && (rhs.kind() == Formula::FALSE))
                return F;
            else
                return apply(f.lhs(), var, val) >> apply(f.rhs(), var, val);
        }
        case Formula::EQ: {
            Formula lhs = apply(f.lhs(), var, val);
            Formula rhs = apply(f.rhs(), var, val);
            if ((lhs.kind() == Formula::FALSE && rhs.kind() == Formula::FALSE) || (lhs.kind() == Formula::TRUE && rhs.kind() == Formula::TRUE))
                return T;
            else if ((lhs.kind() == Formula::FALSE && rhs.kind() == Formula::TRUE) || (lhs.kind() == Formula::TRUE && rhs.kind() == Formula::FALSE))
                return F;
            else
                return apply(f.lhs(), var, val) == apply(f.rhs(), var, val);
        }
        default:
            return F;
    }
}

int get_var(const Formula &f) {
    switch (f.kind()) {
        case Formula::TRUE:
            return INT_MAX;
        case Formula::FALSE:
            return INT_MIN;
        case Formula::VAR:
            return f.var();
        case Formula::NOT:
            return get_var(f.arg());
        case Formula::AND: {
            int lhs = get_var(f.lhs());
            int rhs = get_var(f.rhs());
            if (lhs == INT_MAX || lhs == INT_MIN)
                return rhs;
            else if (rhs == INT_MAX || rhs == INT_MIN)
                return lhs;
            else
                return lhs < rhs ? lhs : rhs;
        }
        case Formula::OR: {
            int lhs = get_var(f.lhs());
            int rhs = get_var(f.rhs());
            if (lhs == INT_MAX || lhs == INT_MIN)
                return rhs;
            else if (rhs == INT_MAX || rhs == INT_MIN)
                return lhs;
            else
                return lhs < rhs ? lhs : rhs;
        }
        case Formula::XOR: {
            int lhs = get_var(f.lhs());
            int rhs = get_var(f.rhs());
            if (lhs == INT_MAX || lhs == INT_MIN)
                return rhs;
            else if (rhs == INT_MAX || rhs == INT_MIN)
                return lhs;
            else
                return lhs < rhs ? lhs : rhs;
        }
        case Formula::IMPL: {
            int lhs = get_var(f.lhs());
            int rhs = get_var(f.rhs());
            if (lhs == INT_MAX || lhs == INT_MIN)
                return rhs;
            else if (rhs == INT_MAX || rhs == INT_MIN)
                return lhs;
            else
                return lhs < rhs ? lhs : rhs;
        }
        case Formula::EQ: {
            int lhs = get_var(f.lhs());
            int rhs = get_var(f.rhs());
            if (lhs == INT_MAX || lhs == INT_MIN)
                return rhs;
            else if (rhs == INT_MAX || rhs == INT_MIN)
                return lhs;
            else
                return lhs < rhs ? lhs : rhs;
        }
        default:
            return INT_MIN; 
    }
}

const Node& Bdd::reduce_and_compose(int var, const Node * high, const Node * low) {
    std::tuple<int, const Node *, const Node *> _new = {var, low, high};
    auto _old = nodepool.find(_new);
    if (_old != nodepool.end()){
        return _old->second;
    } else {
        nodepool.insert({_new, Node(var, low, high)});
        return nodepool[_new];
    }
}

const Node& Bdd::create(const Formula &f) {
    if (f.kind() == Formula::FALSE)
        return Bdd::zero;
    else if (f.kind() == Formula::TRUE)
        return Bdd::one;
    else if (f.kind() == Formula::VAR)
        return reduce_and_compose(f.var(), &one, &zero);
    else {
      int var = get_var(f);

      if (var == INT_MAX)
          return one;
      else if (var == INT_MIN)
          return zero;

      const Node &low = create(apply(f, var, false));
      const Node &high = create(apply(f, var, true));

      if (&low == &high)
          return high;

      return reduce_and_compose(var, &high, &low);
    }
}

static std::string ch_hor_high = "\u2500" /*─*/, 
ch_ver_high = "\u2502" /*│*/,
ch_ddia_high = "\u250C" /*┌*/, 
ch_rddia_high = "\u2510" /*┐*/,

ch_hor_low = "\u254C" /*╌*/, 
ch_ver_low = "\u2506" /*┆*/, 
ch_ddia_low = "\u250C" /*┌*/,
ch_rddia_low = "\u2510" /*┐*/,

ch_udia_hor_high = "\u2514\u2500\u2500\u2500" /*└───*/, 
ch_ddia_hor_high = "\u250C\u2500\u2500\u2500" /*┌───*/, 
ch_ver_spa_high = "\u2502    " /*│ */,

ch_udia_hor_low = "\u2514\u254C\u254C\u254C" /*└╌╌╌*/, 
ch_ddia_hor_low = "\u250C\u254C\u254C\u254C" /*┌╌╌╌*/, 
ch_ver_spa_low = "\u2506    " /*┆*/;

void bdd_print_horizontal(const Node * node, std::string const & rpref, std::string const & cpref, std::string const & lpref) {
    if (!node) 
        return;
    else {
        std::string sval;
        if (node == &Bdd::zero)
            sval = std::string("[0]");
        else if (node == &Bdd::one)
            sval = std::string("[1]");
        else
            sval = "x" + std::to_string(node->var);

        if (node->high)
            bdd_print_horizontal(node->high, rpref + "     ", rpref + ch_ddia_hor_high, rpref + ch_ver_spa_high);
        std::cout << cpref << sval << std::endl;
        if (node->low)
            bdd_print_horizontal(node->low, lpref + ch_ver_spa_low, lpref + ch_udia_hor_low, lpref + "     ");
    }
}   

void bdd_print_vertical(const Node *node, std::vector<std::string> const & lpref, std::vector<std::string> const & cpref, std::vector<std::string> const & rpref, bool root, bool left, std::shared_ptr<std::vector<std::vector<std::string>>> lines) {
    if (!node) return;
    typedef std::vector<std::string> VS;
    auto VSCat = [](VS const & a, VS const & b){ auto r = a; r.insert(r.end(), b.begin(), b.end()); return r; };
    if (root) lines = std::make_shared<std::vector<VS>>();
    if (node->low)
        bdd_print_vertical(node->low, VSCat(lpref, VS({" ", " "})), VSCat(lpref, VS({ch_ddia_low, ch_ver_low})), VSCat(lpref, VS({ch_hor_low, " "})), false, true, lines);

    std::string sval;
    if (node == &Bdd::zero)
        sval = std::string("[0]");
    else if (node == &Bdd::one)
        sval = std::string("[1]");
    else
        sval = "x" + std::to_string(node->var);

    size_t sm = left || sval.empty() ? sval.size() / 2 : ((sval.size() + 1) / 2 - 1);
    for (size_t i = 0; i < sval.size(); ++i)
        lines->push_back(VSCat(i < sm ? lpref : i == sm ? cpref : rpref, {std::string(1, sval[i])}));
    if (node->high)
        bdd_print_vertical(node->high, VSCat(rpref, VS({ch_hor_high, " "})), VSCat(rpref, VS({ch_rddia_high, ch_ver_high})), VSCat(rpref, VS({" ", " "})), false, false, lines);
    if (root) {
        VS out;
        for (size_t l = 0;;++l) {
            bool last = true;
            std::string line;
            for (size_t i = 0; i < lines->size(); ++i) {
                if (l < (*lines).at(i).size()) {
                    line += lines->at(i)[l];
                    last = false;
                } 
                else 
                    line += " ";
            }
            if (last) break;
            out.push_back(line);
        }
        for (size_t i = 0; i < out.size(); ++i)
            std::cout << out[i] << std::endl;
    }
}

} // namespace model::bdd
