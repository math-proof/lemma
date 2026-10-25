/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/BasedRings.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TensorCategories.code.GrothendieckRingCategorical.Part4
import Lemma.Category.Atlas.v1.TensorCategories.code.GrothendieckRingCategorical
import Lemma.Category.Atlas.v1.TensorCategories.code.GradedVec
import Lemma.Category.Atlas.v1.TensorCategories.code.TannakaReconstruction
import Theorem.v1.Atlas.TensorCategories.code.GradedVec.Part6
import Structure.v1.Atlas.TensorCategories.code.TannakaReconstruction
import Structure.v1.Atlas.TensorCategories.code.BasedRings.Part3
open Finset


/-- A multifusion ring is a fusion ring if it is unital, i.e. the unit set `I₀` is a
singleton. -/
def MultifusionRingDef.IsFusionRing {ι : Type*} [DecidableEq ι] [Fintype ι]
    (B : MultifusionRingDef ι) : Prop :=
  ∃ u : ι, B.I₀ = {u}

namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : FusionRing ι)

/-- Bundle a `FusionRing` into a `MultifusionRingDef`: take `I₀ = {R.unit}` and propagate
the multiplication, duality, and associativity data. -/
def toMultifusionRingDef : MultifusionRingDef ι where
  N := R.N
  I₀ := {R.unit}
  star := R.star
  star_star := R.star_star
  assoc := R.assoc
  sum_I₀_mul_left := by
    intro j k; simp only [Finset.sum_singleton]; exact R.unit_mul j k
  sum_I₀_mul_right := by
    intro i k; simp only [Finset.sum_singleton]; exact R.mul_unit i k
  duality_trace := R.duality_trace_singleton
  star_anti := R.star_anti_involution

/-- The group ring `ℤ[G]` of a finite group `G`, regarded as a fusion ring with basis
indexed by `G`: the structure constants encode multiplication in `G` and the duality
involution is inversion. -/
def groupRingFusionRing (G : Type*) [DecidableEq G] [Fintype G] [Group G] :
    FusionRing G where
  unit := 1
  N g h k := if g * h = k then 1 else 0
  star := fun g => g⁻¹
  star_star := by intro g; simp
  unit_mul := by intro j k; simp
  mul_unit := by intro i k; simp
  duality := by
    intro i j
    show (if i * j = 1 then 1 else 0) = (if j = i⁻¹ then 1 else 0)
    congr 1
    exact propext ⟨fun h => by rw [mul_eq_one_iff_eq_inv] at h; rw [h]; simp,
      fun h => by rw [h, mul_inv_cancel]⟩
  assoc := by
    intro i j k l
    have lhs_eq : (∑ m : G, (if i * j = m then 1 else 0) * (if m * k = l then 1 else 0)) =
        if i * j * k = l then 1 else 0 := by
      simp_rw [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have rhs_eq : (∑ m : G, (if j * k = m then 1 else 0) * (if i * m = l then 1 else 0)) =
        if i * (j * k) = l then 1 else 0 := by
      simp_rw [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [lhs_eq, rhs_eq, mul_assoc]
  N_star_transpose := by
    intro i j k
    show (if i * j = k then 1 else 0) = (if i⁻¹ * k = j then 1 else 0)
    congr 1
    exact propext ⟨fun h => by rw [← h]; group,
      fun h => by rw [← h]; group⟩

end FusionRing
