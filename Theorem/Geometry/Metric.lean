/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Metric.lean -/

/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Theorem.Data.Sym.Sym2
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Sym.Card
import Mathlib.Order.Lattice.Nat
import Mathlib.Topology.MetricSpace.Defs
import Def.Geometry.Metric
open scoped Finset

variable {X : Type*} [MetricSpace X]


@[simp] theorem unitDistNum_eq_distanceMultiplicity (s : Finset X) :
    unitDistNum s = distanceMultiplicity s 1 := rfl

