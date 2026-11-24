module
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Norm
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Units.Basic
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
public import Theorem.Set.Closure.eq.N.of.Eq
public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Ideal.Norm.RelNorm
public import Mathlib.RingTheory.FractionalIdeal.Extended
public import Mathlib.RingTheory.Invariant.Basic
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.Lemma247
public import Def.v1.Atlas.NumberTheoryI.code.ArtinUnramified.Part8


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

open scoped Pointwise

open NumberField

namespace ArtinUnramified

attribute [instance] CyclicExtensionData.instGroupG
  CyclicExtensionData.instFiniteG CyclicExtensionData.instCyclicG
  CyclicExtensionData.instCommGroupM CyclicExtensionData.instFiniteM
  CyclicExtensionData.instAction

lemma normToClK_well_defined
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    {I J : nonZeroDivisors (Ideal (𝓞 L))}
    (h : ClassGroup.mk0 I = ClassGroup.mk0 J) :
    normToClK K L I = normToClK K L J := by
  rw [ClassGroup.mk0_eq_mk0_iff] at h
  obtain ⟨x, y, hx, hy, heq⟩ := h
  have heq' : Ideal.spanNorm (𝓞 K) (Ideal.span {x} * I.val) =
               Ideal.spanNorm (𝓞 K) (Ideal.span {y} * J.val) := by rw [heq]
  rw [Ideal.spanNorm_mul, Ideal.spanNorm_mul, Ideal.spanNorm_singleton,
      Ideal.spanNorm_singleton] at heq'
  unfold normToClK spanNormNZD
  simp only [MonoidHom.comp_apply, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [ClassGroup.mk0_eq_mk0_iff]
  exact ⟨_, _, by rwa [ne_eq, Algebra.intNorm_eq_zero],
         by rwa [ne_eq, Algebra.intNorm_eq_zero], heq'⟩

lemma normToClK_of_mk0_eq_one
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    {I : nonZeroDivisors (Ideal (𝓞 L))} (h : ClassGroup.mk0 I = 1) :
    normToClK K L I = 1 := by
  have h' : ClassGroup.mk0 I =
      ClassGroup.mk0 ⟨⊤, by rw [mem_nonZeroDivisors_iff_ne_zero]; exact top_ne_bot⟩ := by
    rw [h]; symm; rw [ClassGroup.mk0_eq_one_iff]
    exact ⟨1, by simp [Ideal.span_singleton_one]⟩
  rw [normToClK_well_defined h']
  show ClassGroup.mk0 (spanNormNZD K L ⟨⊤, _⟩) = 1
  rw [ClassGroup.mk0_eq_one_iff]
  show Submodule.IsPrincipal (Ideal.spanNorm (𝓞 K) ⊤)
  rw [Ideal.spanNorm_top]
  exact ⟨1, by simp [Ideal.span_singleton_one]⟩

end ArtinUnramified
end
