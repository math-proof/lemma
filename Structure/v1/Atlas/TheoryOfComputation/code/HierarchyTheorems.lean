/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/HierarchyTheorems.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Computability.DFA
public import Def.v1.Atlas.TheoryOfComputation.code.Complexity.Part2
public import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.Complexity
public import Lemma.Nat.Atlas.v1.TheoryOfComputation.code.SpaceComplexity
public import Def.v1.Atlas.TheoryOfComputation.code.SpaceComplexity.Part7
public import Def.v1.Atlas.TheoryOfComputation.code.HierarchyTheorems


public section

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
