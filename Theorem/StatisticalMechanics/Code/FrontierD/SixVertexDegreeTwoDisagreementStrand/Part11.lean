/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDisagreementComponentCType.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTopology.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusMedial.Part5
import Mathlib.Algebra.Group.End
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Cycle.Factors
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part12
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sum_map_permOrderedCycleFactor
    {D : Type*} [Fintype D] [DecidableEq D]
    (sigma cycle : Equiv.Perm D)
    (hcycle : cycle ∈ sigma.cycleFactorsFinset) (f : D → Int) :
    ((permOrderedCycleFactor sigma cycle hcycle).map f).sum =
      ∑ d ∈ cycle.support, f d := by
  let hc : cycle.IsCycle :=
    (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hcycle).1
  let hs : cycle.support.Nonempty := hc.nonempty_support
  let seed : cycle.support :=
    ⟨Classical.choose hs, Classical.choose_spec hs⟩
  let enumerate := permCycleFinEquivSupport cycle hc seed
  rw [show permOrderedCycleFactor sigma cycle hcycle =
      List.ofFn (fun k => (enumerate k).1) by rfl]
  rw [List.map_ofFn, List.sum_ofFn]
  change (∑ k, f (enumerate k).1) = _
  rw [enumerate.sum_comp (fun d => f d.1)]
  exact Finset.sum_coe_sort cycle.support f

theorem sum_map_list_flatMap
    {A B : Type*} (items : List A) (pieces : A → List B)
    (f : B → Int) :
    ((items.flatMap pieces).map f).sum =
      (items.map fun a => ((pieces a).map f).sum).sum := by
  induction items with
  | nil => simp
  | cons a items ih => simp [ih]

theorem sum_map_finset_toList
    {A : Type*} (items : Finset A) (f : A → Int) :
    (items.toList.map f).sum = ∑ a ∈ items, f a := by
  classical
  induction items using Finset.induction with
  | empty => simp
  | @insert a items ha ih => simp [ha]


end
end StatMech.FrontierD
