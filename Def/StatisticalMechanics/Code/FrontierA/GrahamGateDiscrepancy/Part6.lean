/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamGateDiscrepancy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Max
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamGateDiscrepancy.Part6


namespace StatMech.FrontierA

noncomputable def RelationPartialMatching.reassign
    {A B : Type*} {r : A -> B -> Prop}
    (matching : RelationPartialMatching r) (new old : A) (b : B)
    (hne : new ≠ old) (hold : matching.toFun old = some b)
    (hnew : r new b) : RelationPartialMatching r := by
  classical
  let reassignedFun : A -> Option B := fun x =>
    if x = new then some b else if x = old then none else matching.toFun x
  refine ⟨reassignedFun, ?_, ?_⟩
  · intro x y hxy
    by_cases hxNew : x = new
    · subst x
      simp only [reassignedFun, if_pos, Option.some.injEq] at hxy
      exact hxy ▸ hnew
    · by_cases hxOld : x = old
      · subst x
        simp only [reassignedFun, if_neg hne.symm, if_pos] at hxy
        contradiction
      · simp only [reassignedFun, if_neg hxNew, if_neg hxOld] at hxy
        exact matching.related hxy
  · intro x y z hx hy
    by_cases hxNew : x = new
    · subst x
      by_cases hyNew : y = new
      · exact hyNew.symm
      · by_cases hyOld : y = old
        · subst y
          simp only [reassignedFun, if_neg hne.symm, if_pos] at hy
          contradiction
        · simp only [reassignedFun, if_pos, Option.some.injEq] at hx
          simp only [reassignedFun, if_neg hyNew, if_neg hyOld] at hy
          have hyEqOld := matching.injective_some
            (hy.trans (congrArg some hx.symm)) hold
          exact False.elim (hyOld hyEqOld)
    · by_cases hxOld : x = old
      · subst x
        simp only [reassignedFun, if_neg hne.symm, if_pos] at hx
        contradiction
      · by_cases hyNew : y = new
        · subst y
          simp only [reassignedFun, if_neg hxNew, if_neg hxOld] at hx
          simp only [reassignedFun, if_pos, Option.some.injEq] at hy
          have hxEqOld := matching.injective_some
            (hx.trans (congrArg some hy.symm)) hold
          exact False.elim (hxOld hxEqOld)
        · by_cases hyOld : y = old
          · subst y
            simp only [reassignedFun, if_neg hne.symm, if_pos] at hy
            contradiction
          · simp only [reassignedFun, if_neg hxNew, if_neg hxOld] at hx
            simp only [reassignedFun, if_neg hyNew, if_neg hyOld] at hy
            exact matching.injective_some hx hy

end StatMech.FrontierA
