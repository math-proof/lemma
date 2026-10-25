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
import Def.v1.Atlas.NumberTheoryI.code.LocalFields.Part4
open Metric Filter Set Topology

attribute [instance] IsLocalField.locallyCompact


lemma extendRingHom_padic_on_rat
    {L_v : Type*} [NontriviallyNormedField L_v] [CompleteSpace L_v]
    (j : ℚ →+* L_v) (p : ℕ) [Fact (Nat.Prime p)]
    (heq : normAbsValQ j = Rat.AbsoluteValue.padic p)
    (q : ℚ) : extendRingHom_padic j p heq (q : ℚ_[p]) = j q := by
  simp only [extendRingHom_padic, RingHom.coe_comp, Function.comp_apply,
             RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  have h1 : Padic.withValRingEquiv.symm (q : ℚ_[p]) =
      ((WithVal.equiv (Rat.padicValuation p)).symm q : (Rat.padicValuation p).Completion) := by
    apply Padic.withValRingEquiv.injective
    rw [Padic.withValRingEquiv.apply_symm_apply]; symm
    simp only [Padic.withValRingEquiv]
    erw [UniformSpace.Completion.extensionHom_coe _
      (Padic.isUniformInducing_cast_withVal.uniformContinuous.continuous)]
    simp
  rw [h1]
  erw [UniformSpace.Completion.extensionHom_coe _ (j_comp_equiv_continuous j p heq)]
  simp

lemma extendRingHom_padic_continuous
    {L_v : Type*} [NontriviallyNormedField L_v] [CompleteSpace L_v]
    (j : ℚ →+* L_v) (p : ℕ) [Fact (Nat.Prime p)]
    (heq : normAbsValQ j = Rat.AbsoluteValue.padic p) :
    Continuous (extendRingHom_padic j p heq) := by
  show Continuous (fun x : ℚ_[p] =>
    (UniformSpace.Completion.extensionHom
      (j.comp (WithVal.equiv (Rat.padicValuation p)).toRingHom)
      (j_comp_equiv_continuous j p heq))
      (Padic.withValRingEquiv.symm x))
  exact Continuous.comp
    (show Continuous (UniformSpace.Completion.extension
      (j.comp (WithVal.equiv (Rat.padicValuation p)).toRingHom)) from
      UniformSpace.Completion.continuous_extension)
    Padic.withValUniformEquiv.symm.continuous

lemma extendRingHom_padic_isometry
    {L_v : Type*} [NontriviallyNormedField L_v] [CompleteSpace L_v]
    (j : ℚ →+* L_v) (p : ℕ) [Fact (Nat.Prime p)]
    (heq : normAbsValQ j = Rat.AbsoluteValue.padic p)
    (x : ℚ_[p]) :
    ‖extendRingHom_padic j p heq x‖ = ‖x‖ := by
  have key : (fun x => ‖extendRingHom_padic j p heq x‖) = (fun x => ‖x‖) := by
    apply DenseRange.equalizer (Padic.denseRange_ratCast p)
    · exact continuous_norm.comp (extendRingHom_padic_continuous j p heq)
    · exact continuous_norm
    · ext q; simp only [Function.comp_apply]
      rw [extendRingHom_padic_on_rat]
      have h1 : normAbsValQ j q = Rat.AbsoluteValue.padic p q := by rw [heq]
      simp only [normAbsValQ, AbsoluteValue.coe_mk, MulHom.coe_mk, Rat.AbsoluteValue.padic] at h1
      rw [h1, Padic.eq_padicNorm]
  exact congr_fun key x

