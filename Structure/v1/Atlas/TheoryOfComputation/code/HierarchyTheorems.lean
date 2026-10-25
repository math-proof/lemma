/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/HierarchyTheorems.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Computability.DFA
import Def.v1.Atlas.TheoryOfComputation.code.Complexity.Part2
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.Complexity
import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.SpaceComplexity
import Def.v1.Atlas.TheoryOfComputation.code.SpaceComplexity.Part7
import Def.v1.Atlas.TheoryOfComputation.code.HierarchyTheorems


namespace HierarchyTheorems

open TuringMachine

/--
A **TM description** packages a Turing machine over alphabet `Γ` together with
its number of states. The state type `Fin (numStates + 3)` reserves three states
(start, accept, reject) on top of the working states, providing a uniform shape
for enumeration in the diagonalization construction.
-/
structure TMDesc (Γ : Type) where
  numStates : ℕ
  machine : TM (Fin (numStates + 3)) Γ

end HierarchyTheorems
