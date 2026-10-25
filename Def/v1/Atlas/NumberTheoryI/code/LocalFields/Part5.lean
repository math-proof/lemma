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
import Theorem.v1.Atlas.NumberTheoryI.code.LocalFields.Part5
open Metric Filter Set Topology

attribute [instance] IsLocalField.locallyCompact


@[reducible]
noncomputable def completion_normedAlgebra_padic_of_eq
    (L_v : Type*) [NontriviallyNormedField L_v] [CompleteSpace L_v]
    (j : ℚ →+* L_v)
    (p : ℕ) [Fact (Nat.Prime p)]
    (heq : normAbsValQ j = Rat.AbsoluteValue.padic p) :
    NormedAlgebra ℚ_[p] L_v := by
  let f := extendRingHom_padic j p heq
  have hiso := extendRingHom_padic_isometry j p heq
  letI : Algebra ℚ_[p] L_v := f.toAlgebra
  exact NormedAlgebra.mk (fun r x => by
    have : (algebraMap ℚ_[p] L_v) r = f r := rfl
    rw [Algebra.smul_def, norm_mul, this, hiso])

@[reducible]
noncomputable def completion_normedAlgebra_padic
    (L_v : Type*) [NontriviallyNormedField L_v] [CompleteSpace L_v]
    (j : ℚ →+* L_v)
    (p : ℕ) [Fact (Nat.Prime p)]
    (hequiv : (normAbsValQ j).IsEquiv (Rat.AbsoluteValue.padic p))
    (hnorm_p : ‖j (↑p : ℚ)‖ = (↑p : ℝ)⁻¹) :
    NormedAlgebra ℚ_[p] L_v :=
  completion_normedAlgebra_padic_of_eq L_v j p
    (normAbsValQ_isEquiv_padic_eq j p hequiv hnorm_p)

