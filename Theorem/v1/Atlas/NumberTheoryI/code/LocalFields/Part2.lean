module
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import Mathlib.Analysis.Normed.Field.ProperSpace
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.Analysis.Normed.Algebra.GelfandMazur
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.NumberTheory.Ostrowski
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.NumberTheory.Padics.WithVal
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.RingTheory.Valuation.Discrete.RankOne
public import Def.v1.Atlas.NumberTheoryI.code.Adeles.Part10
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.Adeles
public import Def.v1.Atlas.NumberTheoryI.code.LocalFields
open Metric Filter Set Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalFields.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

attribute [instance] IsLocalField.locallyCompact


theorem absValFromNorm_isNontrivial (L : Type*) [IsLocalField L] [CharZero L] :
    (absValFromNorm L).IsNontrivial := by
  by_contra h_triv
  simp only [AbsoluteValue.IsNontrivial, absValFromNorm, AbsoluteValue.coe_mk,
    MulHom.coe_mk, not_exists, not_and, not_not] at h_triv
  let S : Set L := range (fun n : ℤ => (n : L))
  have h_sep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ dist x y := by
    rintro _ ⟨n, rfl⟩ _ ⟨m, rfl⟩ hnm
    simp only [dist_eq_norm]
    rw [show (n : L) - (m : L) = ((n - m : ℤ) : L) from by push_cast; ring,
        show ‖((n - m : ℤ) : L)‖ = ‖((n - m : ℚ) : L)‖ from by push_cast; ring_nf,
        h_triv _ (by exact_mod_cast sub_ne_zero.mpr (fun h => hnm (congrArg _ h)))]
  have hS_sub : S ⊆ closedBall (0 : L) 1 := by
    rintro _ ⟨n, rfl⟩; simp only [mem_closedBall, dist_zero_right]
    by_cases hn : (n : ℚ) = 0
    · simp [show (n : L) = 0 from by exact_mod_cast hn]
    · rw [show ‖(n : L)‖ = ‖((n : ℚ) : L)‖ from by push_cast; ring_nf, h_triv _ hn]
  obtain ⟨x, _, hx⟩ := (infinite_range_of_injective (fun (_ : ℤ) _ h => by
    exact_mod_cast h) : S.Infinite).exists_accPt_of_subset_isCompact
    (isCompact_closedBall 0 1) hS_sub
  exact not_accPt_of_separated h_sep x hx

