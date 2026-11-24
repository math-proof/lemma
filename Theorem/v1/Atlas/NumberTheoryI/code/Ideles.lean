module
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.Topology.Algebra.Group.Compact
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import Mathlib.GroupTheory.FiniteIndexNormalSubgroup
public import Def.v1.Atlas.NumberTheoryI.code.Adeles.Part10
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.Adeles
public import Instance.v1.Atlas.NumberTheoryI.code.Ideles


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Ideles.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

open NumberField IsDedekindDomain

namespace Ideles

section IdeleGroup

variable (K : Type*) [Field K] [NumberField K]

lemma adeleRing_unit_fin_norm_finMulSupport (a : IdeleGroup K) :
    (Function.mulSupport
      (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
        ‖(a : NumberField.AdeleRing (𝓞 K) K).2 v‖)).Finite := by
  have ha := (a : NumberField.AdeleRing (𝓞 K) K).2.2
  have hai := (↑a⁻¹ : NumberField.AdeleRing (𝓞 K) K).2.2
  rw [Filter.eventually_cofinite] at ha hai
  apply Set.Finite.subset (ha.union hai)
  intro v hv
  rw [Function.mem_mulSupport] at hv
  simp only [Set.mem_union, Set.mem_setOf_eq]
  by_contra h
  push Not at h
  obtain ⟨hv1, hv2⟩ := h
  have h1 : ‖(a : NumberField.AdeleRing (𝓞 K) K).2 v‖ ≤ 1 :=
    Valued.toNormedField.norm_le_one_iff.mpr hv1
  have h2 : ‖(↑a⁻¹ : NumberField.AdeleRing (𝓞 K) K).2 v‖ ≤ 1 :=
    Valued.toNormedField.norm_le_one_iff.mpr hv2
  have hmul : (↑a : NumberField.AdeleRing (𝓞 K) K).2 v *
      (↑a⁻¹ : NumberField.AdeleRing (𝓞 K) K).2 v = 1 := by
    change ((↑a : NumberField.AdeleRing (𝓞 K) K).2 *
      (↑a⁻¹ : NumberField.AdeleRing (𝓞 K) K).2) v =
      (1 : NumberField.AdeleRing (𝓞 K) K).2 v
    congr 1; exact congr_arg Prod.snd (Units.mul_inv a)
  have hnm : ‖(a : NumberField.AdeleRing (𝓞 K) K).2 v‖ *
      ‖(↑a⁻¹ : NumberField.AdeleRing (𝓞 K) K).2 v‖ = 1 := by
    rw [← norm_mul, hmul, norm_one]
  have hge : 1 ≤ ‖(a : NumberField.AdeleRing (𝓞 K) K).2 v‖ := by
    by_contra hlt; push Not at hlt
    linarith [mul_le_mul_of_nonneg_left h2
      (norm_nonneg ((a : NumberField.AdeleRing (𝓞 K) K).2 v))]
  exact hv (le_antisymm h1 hge)

end IdeleGroup
end Ideles
end
