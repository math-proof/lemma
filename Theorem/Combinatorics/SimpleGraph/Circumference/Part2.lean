/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Circumference.lean -/

/-
Copyright 2026 The Formal Conjectures Authors.

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

import Mathlib.Algebra.Ring.Parity
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Order.Lattice.Nat
import Def.Combinatorics.SimpleGraph.Circumference.Part2
/-!
# Cycle lengths and circumference

Ported from `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Circumference.lean`
in google-deepmind/formal-conjectures (cycle-length fragment only).
-/


namespace SimpleGraph

@[simp] theorem mem_oddCycleLengths {α : Type*} {G : SimpleGraph α} {m : ℕ} :
    m ∈ G.oddCycleLengths ↔ m ∈ G.cycleLengths ∧ Odd m :=
  Iff.rfl

end SimpleGraph
