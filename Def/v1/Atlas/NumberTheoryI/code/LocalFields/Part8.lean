/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalFields.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Analysis.Normed.Field.ProperSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Analysis.Normed.Algebra.GelfandMazur
import Mathlib.RingTheory.LaurentSeries
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.NumberTheory.Ostrowski
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.NumberTheory.Padics.WithVal
import Mathlib.Topology.Algebra.UniformRing
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Def.v1.Atlas.NumberTheoryI.code.Adeles.Part10
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Adeles
import Theorem.v1.Atlas.NumberTheoryI.code.LocalFields.Part8
open Metric Filter Set Topology

attribute [instance] IsLocalField.locallyCompact


noncomputable def localField_charZero_normedAlgebra_structure
    (L : Type*) [IsLocalField L] [CharZero L] :
    (Σ' (_ : Algebra ℝ L), ContinuousSMul ℝ L) ⊕
    (Σ' (p : ℕ) (_ : Fact (Nat.Prime p)) (_ : Algebra ℚ_[p] L), ContinuousSMul ℚ_[p] L) := by
  classical
  have hnt := absValFromNorm_isNontrivial L
  have hostr := Rat.AbsoluteValue.equiv_real_or_padic (absValFromNorm L) hnt
  haveI : CompleteSpace L := complete_of_proper
  by_cases h_real : (absValFromNorm L).IsEquiv Rat.AbsoluteValue.real
  ·

    rw [absValFromNorm_eq_normAbsValQ_castHom] at h_real
    let f := extendRingHom_real (Rat.castHom L) h_real
    letI : Algebra ℝ L := f.toAlgebra
    have hcont : Continuous (algebraMap ℝ L) :=
      extendRingHom_real_continuous (Rat.castHom L) h_real
    exact Sum.inl ⟨‹Algebra ℝ L›, continuousSMul_of_algebraMap ℝ L hcont⟩
  ·
    have h_padic := hostr.resolve_left h_real
    let p := Classical.choose h_padic.exists
    have hp_spec := Classical.choose_spec h_padic.exists
    have hfact : Fact (Nat.Prime p) := Classical.choose hp_spec
    have h_equiv : (absValFromNorm L).IsEquiv (Rat.AbsoluteValue.padic p) :=
      Classical.choose_spec hp_spec
    rw [absValFromNorm_eq_normAbsValQ_castHom] at h_equiv
    let f := extendRingHom_padic_of_equiv (Rat.castHom L) p h_equiv
    letI : Algebra ℚ_[p] L := f.toAlgebra
    have hcont : Continuous (algebraMap ℚ_[p] L) :=
      extendRingHom_padic_of_equiv_continuous (Rat.castHom L) p h_equiv
    exact Sum.inr ⟨p, hfact, ‹Algebra ℚ_[p] L›, continuousSMul_of_algebraMap ℚ_[p] L hcont⟩

