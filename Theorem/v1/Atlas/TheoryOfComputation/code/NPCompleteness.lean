/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/NPCompleteness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.List.Nodup
public import Def.v1.Atlas.TheoryOfComputation.code.Complexity.Part2
public import Theorem.Nat.Atlas.v1.TheoryOfComputation.code.Complexity
public import Structure.v1.Atlas.TheoryOfComputation.code.Tableau
public import Def.v1.Atlas.TheoryOfComputation.code.NPCompleteness

public section

namespace NPCompleteness

/-- Membership in `ThreeSAT` from the conjunction of being 3CNF and being satisfiable. -/
theorem ThreeSAT.mk {φ : BoolFormula} (h3 : φ.Is3CNF) (hsat : φ.Satisfiable) :
    φ ∈ ThreeSAT :=
  ⟨h3, hsat⟩

example : (BoolFormula.or (.var 0) (.or (.var 1) (.var 2))).Is3Clause := by
  constructor
  · exact ⟨trivial, ⟨trivial, trivial⟩⟩
  · rfl

example : (BoolFormula.or (.var 0) (.or (.var 1) (.var 2))).Is3CNF := by
  constructor
  · exact ⟨trivial, ⟨trivial, trivial⟩⟩
  · rfl

example : (BoolFormula.or (.var 0) (.or (.var 1) (.var 2))) ∈ ThreeSAT := by
  refine ⟨?_, ?_⟩
  · exact ⟨⟨trivial, ⟨trivial, trivial⟩⟩, rfl⟩
  · exact ⟨fun _ => true, rfl⟩

end NPCompleteness
