/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AdvancedKahler.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.ConnectionsCurvature
import Structure.v1.Atlas.GeometryOfManifolds.code.ConnectionsCurvature.Part7
import Class.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler.Part2
set_option autoImplicit false

open DifferentialFormSpace


/-- Holomorphic bundle structure: a $(0,1)$-connection operator
$\bar\partial_E : \Omega^{0,q}(E) \to \Omega^{0,q+1}(E)$ on $E$-valued forms
satisfying the integrability condition $\bar\partial_E^2 = 0$. -/
structure HolomorphicBundleStr
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (Sections : Type*) [AddCommGroup Sections]
    (FormsWithValues : ℕ → Type*) [∀ q, AddCommGroup (FormsWithValues q)] where
  delbar_E : ∀ {q : ℕ}, FormsWithValues q → FormsWithValues (q + 1)
  delbar_sq : ∀ {q : ℕ} (σ : FormsWithValues q), delbar_E (delbar_E σ) = 0
  delbar_add : ∀ {q : ℕ} (σ τ : FormsWithValues q),
    delbar_E (σ + τ) = delbar_E σ + delbar_E τ

/-- A holomorphic section of a holomorphic bundle: a section $\sigma$ such that
$\bar\partial_E \sigma = 0$. -/
structure HolomorphicSection
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {Sections : Type*} [AddCommGroup Sections]
    {FormsWithValues : ℕ → Type*} [∀ q, AddCommGroup (FormsWithValues q)]
    (hol : HolomorphicBundleStr (inst := inst) Sections FormsWithValues)
    (toSections : Sections → FormsWithValues 0) where
  section_ : Sections
  is_holomorphic : hol.delbar_E (toSections section_) = 0


/-- A Hermitian metric datum on a line bundle, represented abstractly by an
invertible element $h \in R$ in a ring of bundle endomorphisms. -/
structure HermitianBundleMetric (R : Type*) [Ring R] where
  h : R
  h_inv : R
  h_inv_left : h_inv * h = 1
  h_right_inv : h * h_inv = 1


/-- Data attached to a Hermitian line bundle: a closed curvature $2$-form
$R^\nabla \in \Omega^2(M)$ representing $2\pi \cdot c_1(L) \in H^2(M, \mathbb{R})$. -/
structure LineBundleData
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF] where
  curvature : Ω 2
  curvature_closed : inst.d curvature = 0


