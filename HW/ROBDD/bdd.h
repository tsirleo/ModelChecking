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

#pragma once

#include <iostream>
#include <memory>
#include <vector>
#include <string>
#include <climits>
#include <map>

#include "formula.h"

using namespace model::logic;

namespace model::bdd {

struct Node final {
  int var;

  const Node *low;
  const Node *high;

  Node(): var(), low(nullptr), high(nullptr) {}

  Node(int var, const Node *low, const Node *high):
    var(var), low(low), high(high) {}
};

class Bdd final {
public:
  static const Node zero;
  static const Node one;

  // TODO: To be implemented in 'bdd.cpp'.
  const Node& reduce_and_compose(int var, const Node * low, const Node * high);
  const Node& create(const Formula &formula);

private:
  // Pool of nodes organized so as to effeciently
  // search for a given (var, low, high).
  std::map<std::tuple<int, const Node *, const Node *>, const Node> nodepool;
};

void bdd_print_horizontal(const Node * node, std::string const & rpref = "", std::string const & cpref = "", std::string const & lpref = "");
void bdd_print_vertical(const Node *node, std::vector<std::string> const & lpref = std::vector<std::string>(), std::vector<std::string> const & cpref = std::vector<std::string>(), std::vector<std::string> const & rpref = std::vector<std::string>(), bool root = true, bool left = true, std::shared_ptr<std::vector<std::vector<std::string>>> lines = nullptr);

} // namespace model::bdd
