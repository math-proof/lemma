/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/SubdivisionSmall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section11
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section11
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section6
import Structure.v1.Atlas.AlgebraicTopologyI.code.Section6
import Mathlib.Algebra.FreeAbelianGroup.Finsupp
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Topology.UniformSpace.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Algebra.Order.Archimedean.Basic


noncomputable section

open Classical in
/-- The image of a `Finsupp` under `Finsupp.toFreeAbelianGroup` is the finite sum of the
generators weighted by the corresponding integer coefficients. -/
lemma toFreeAbelianGroup_eq_sum {Y : Type*} (f : Y →₀ ℤ) :
    Finsupp.toFreeAbelianGroup f = f.sum (fun x n => n • FreeAbelianGroup.of x) := by
  simp only [Finsupp.toFreeAbelianGroup, Finsupp.liftAddHom_apply]; congr 1

open Classical in
/-- Any element of a free abelian group can be written as the finite sum of its generators
weighted by the integer coefficients given by its associated `Finsupp`. -/
lemma freeAbelianGroup_eq_sum {Y : Type*} (c : FreeAbelianGroup Y) :
    c = (FreeAbelianGroup.toFinsupp c).sum (fun x n => n • FreeAbelianGroup.of x) := by
  rw [← toFreeAbelianGroup_eq_sum, Finsupp.toFreeAbelianGroup_toFinsupp]

open Classical in
/-- The lift of `f : Y → Z` along `FreeAbelianGroup.lift` evaluated at `c` equals the
finite sum, over the support of `c`, of `f` applied to each generator scaled by its
integer coefficient. -/
lemma lift_eq_finsupp_sum {Y Z : Type*} [AddCommGroup Z] (f : Y → Z)
    (c : FreeAbelianGroup Y) :
    (FreeAbelianGroup.lift f) c =
    (FreeAbelianGroup.toFinsupp c).sum (fun x n => n • f x) := by
  conv_lhs => rw [freeAbelianGroup_eq_sum c]
  simp only [Finsupp.sum, map_sum, map_zsmul, FreeAbelianGroup.lift_apply_of]

open Classical in
/-- The support of a finite sum of free-abelian-group elements is contained in the union
of the supports of the summands. -/
lemma support_finset_sum {Y Z : Type*}
    (s : Finset Y) (f : Y → FreeAbelianGroup Z) :
    (∑ i ∈ s, f i).support ⊆ s.biUnion (fun i => (f i).support) := by
  induction s using Finset.induction with
  | empty => simp [FreeAbelianGroup.support_zero]
  | @insert x s' hxs ih =>
    intro τ hτ
    rw [Finset.sum_insert hxs] at hτ
    rcases Finset.mem_union.mp (FreeAbelianGroup.support_add _ _ hτ) with h | h
    · exact Finset.mem_biUnion.mpr ⟨x, Finset.mem_insert_self _ _, h⟩
    · obtain ⟨y, hy, hfy⟩ := Finset.mem_biUnion.mp (ih h)
      exact Finset.mem_biUnion.mpr ⟨y, Finset.mem_insert_of_mem hy, hfy⟩

open Classical in
/-- The support of `FreeAbelianGroup.lift f c` is contained in the union over the support
of `c` of the supports of `f x`. -/
lemma support_lift_subset {Y Z : Type*}
    (f : Y → FreeAbelianGroup Z) (c : FreeAbelianGroup Y) :
    ((FreeAbelianGroup.lift f) c).support ⊆
      c.support.biUnion (fun x => (f x).support) := by
  rw [lift_eq_finsupp_sum]
  apply Finset.Subset.trans (support_finset_sum _ _)
  apply Finset.biUnion_mono
  intro x _ τ hτ
  by_cases hn : (FreeAbelianGroup.toFinsupp c) x = 0
  · simp [hn, FreeAbelianGroup.support_zero] at hτ
  · rwa [FreeAbelianGroup.support_zsmul _ hn] at hτ

open Classical in
/-- If a property `P` holds on the supports of `f x` for every `x` in the support of `c`,
then it holds on the support of `FreeAbelianGroup.lift f c`. -/
lemma lift_support_forall {Y Z : Type*} (f : Y → FreeAbelianGroup Z)
    (c : FreeAbelianGroup Y) (P : Z → Prop)
    (hP : ∀ x ∈ c.support, ∀ y ∈ (f x).support, P y) :
    ∀ y ∈ ((FreeAbelianGroup.lift f) c).support, P y := by
  intro y hy
  obtain ⟨x, hxc, hxf⟩ := Finset.mem_biUnion.mp (support_lift_subset f c hy)
  exact hP x hxc y hxf

end
