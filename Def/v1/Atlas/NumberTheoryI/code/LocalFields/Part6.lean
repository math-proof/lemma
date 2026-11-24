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
public import Theorem.v1.Atlas.NumberTheoryI.code.LocalFields.Part6
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


@[reducible]
noncomputable def completion_normedAlgebra_real_of_eq
    (L_v : Type*) [NontriviallyNormedField L_v] [CompleteSpace L_v]
    (j : ℚ →+* L_v)
    (heq : normAbsValQ j = Rat.AbsoluteValue.real) :
    NormedAlgebra ℝ L_v := by
  have hequiv : (normAbsValQ j).IsEquiv Rat.AbsoluteValue.real :=
    heq ▸ AbsoluteValue.IsEquiv.refl _

  let f := extendRingHom_real j hequiv


  have hiso : ∀ r : ℝ, ‖f r‖ = ‖r‖ := by
    intro r
    have hclosed : IsClosed {x : ℝ | ‖f x‖ = ‖x‖} := by
      apply isClosed_eq
      · exact continuous_norm.comp (extendRingHom_real_continuous j hequiv)
      · exact continuous_norm
    have hdense : closure (Set.range (Rat.cast : ℚ → ℝ)) ⊆ {x | ‖f x‖ = ‖x‖} := by
      apply hclosed.closure_subset_iff.mpr
      rintro _ ⟨q, rfl⟩
      show ‖f (q : ℝ)‖ = ‖(q : ℝ)‖
      rw [extendRingHom_real_extends j hequiv q]
      have h1 : (normAbsValQ j) q = Rat.AbsoluteValue.real q := congr_fun (congr_arg _ heq) q
      change ‖j q‖ = _ at h1
      rw [h1, Rat.AbsoluteValue.real_eq_abs, Real.norm_eq_abs]
      push_cast; rfl
    exact hdense (Rat.isDenseEmbedding_coe_real.dense r)

  letI : Algebra ℝ L_v := f.toAlgebra
  exact NormedAlgebra.mk (fun r x => by
    have : (algebraMap ℝ L_v) r = f r := rfl
    rw [Algebra.smul_def, norm_mul, this, hiso])

@[reducible]
noncomputable def completion_normedAlgebra_real
    (L_v : Type*) [NontriviallyNormedField L_v] [CompleteSpace L_v]
    (j : ℚ →+* L_v)
    (hequiv : (normAbsValQ j).IsEquiv Rat.AbsoluteValue.real)
    (hnorm_2 : ‖j (2 : ℚ)‖ = 2) :
    NormedAlgebra ℝ L_v :=
  completion_normedAlgebra_real_of_eq L_v j
    (normAbsValQ_isEquiv_real_eq j hequiv hnorm_2)

