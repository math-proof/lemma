/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafCohomology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.CohomologyP1
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CohomologyP1
import Mathlib.RingTheory.Flat.Localization
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Localization.Away.Basic

namespace SheafCohomology


section SheafCondition

variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]

/-- The "restriction to the cover" map for an `A`-module `M`: it sends `m` to the
pair of its images in the localizations away from `f` and from `g`. This is the
first map of the Čech complex for the two-element cover `{D(f), D(g)}`. -/
noncomputable def locProductMap (f g : A) :
    M →ₗ[A] LocalizedModule (Submonoid.powers f) M × LocalizedModule (Submonoid.powers g) M :=
  LinearMap.prod
    (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
    (LocalizedModule.mkLinearMap (Submonoid.powers g) M)

/-- `f` becomes a unit in `A[(fg)⁻¹]`. -/
lemma isUnit_algebraMap_of_away_mul_left :
    IsUnit (algebraMap A (Localization.Away (f * g)) f) := by
  have hu := IsLocalization.map_units (Localization.Away (f * g))
    (⟨f * g, 1, pow_one _⟩ : Submonoid.powers (f * g))
  simp at hu; exact hu.1

/-- `g` becomes a unit in `A[(fg)⁻¹]`. -/
lemma isUnit_algebraMap_of_away_mul_right :
    IsUnit (algebraMap A (Localization.Away (f * g)) g) := by
  have hu := IsLocalization.map_units (Localization.Away (f * g))
    (⟨f * g, 1, pow_one _⟩ : Submonoid.powers (f * g))
  simp at hu; exact hu.2

/-- The restriction `A[f⁻¹] → A[(fg)⁻¹]` induced by the universal property
of localization. This is one of the two Čech restriction maps for `{D(f), D(g)}`. -/
noncomputable def cechMapFromF :
    Localization.Away f →+* Localization.Away (f * g) :=
  Localization.awayLift (algebraMap A (Localization.Away (f * g))) f
    (isUnit_algebraMap_of_away_mul_left A f g)

/-- The restriction `A[g⁻¹] → A[(fg)⁻¹]` induced by the universal property
of localization. -/
noncomputable def cechMapFromG :
    Localization.Away g →+* Localization.Away (f * g) :=
  Localization.awayLift (algebraMap A (Localization.Away (f * g))) g
    (isUnit_algebraMap_of_away_mul_right A f g)

/-- The Čech differential `A[f⁻¹] × A[g⁻¹] → A[(fg)⁻¹]`, sending
`(s, t) ↦ s|_{D(fg)} - t|_{D(fg)}`. Its cokernel is `H¹` for the two-element cover. -/
noncomputable def cechDifferential :
    Localization.Away f × Localization.Away g → Localization.Away (f * g) :=
  fun p => cechMapFromF A f g p.1 - cechMapFromG A f g p.2

/-- `H⁰(ℙ¹, O(n))`, realized concretely as the Čech `H⁰` of degree `n` sections. -/
abbrev H0 (n : ℤ) : Type := ↥(CechH0 k n)

/-- `H¹(ℙ¹, O(n))`, realized concretely as the quotient of Laurent series in one
variable by the sum of "non-negative degree" and "degree `≤ n`" subspaces. -/
abbrev H1 (n : ℤ) : Type := (ℤ →₀ k) ⧸ (NonNeg k ⊔ AtMost k n)

/-- `H⁰(ℙ¹, O(n)) = 0` for `n < 0`: no global sections in negative degree. -/
lemma finrank_H0_of_neg (n : ℤ) (hn : n < 0) :
    Module.finrank k (H0 k n) = 0 := by
  show Module.finrank k ↥(CechH0 k n) = 0
  rw [H0_vanishes_neg k n hn]
  exact finrank_bot k (ℤ →₀ k)

/-- `dim H⁰(ℙ¹, O(n)) = n + 1` for `n ≥ 0`: the global sections of `O(n)` are
the homogeneous polynomials of degree `n` in two variables. -/
lemma finrank_H0_of_nonneg (n : ℤ) (hn : 0 ≤ n) :
    Module.finrank k (H0 k n) = (n + 1).toNat := by
  show Module.finrank k ↥(CechH0 k n) = (n + 1).toNat
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  rw [finrank_H0_nonneg]
  simp

/-- `H¹(ℙ¹, O(n)) = 0` for `n ≥ 0`: higher cohomology of non-negative twists
vanishes on ℙ¹. -/
lemma finrank_H1_of_nonneg (n : ℤ) (hn : 0 ≤ n) :
    Module.finrank k (H1 k n) = 0 := by
  show Module.finrank k ((ℤ →₀ k) ⧸ (NonNeg k ⊔ AtMost k n)) = 0
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  exact finrank_H1_nonneg k m

/-- `dim H¹(ℙ¹, O(n)) = -n - 1` for `n < 0`: combinatorial count of Laurent terms
of strictly negative degree above the cutoff `n`. -/
lemma finrank_H1_of_neg (n : ℤ) (hn : n < 0) :
    Module.finrank k (H1 k n) = (-n - 1).toNat :=
  finrank_H1_neg k n hn

/-- Serre duality on ℙ¹, non-negative case: `dim H¹(O(n)) = dim H⁰(O(-2 - n))`.
For `n ≥ 0` both sides vanish, confirming the duality. The canonical bundle on
ℙ¹ is `O(-2)`, so `O(n)∨ ⊗ K = O(-2 - n)`. -/
theorem serre_duality_nonneg (n : ℤ) (hn : 0 ≤ n) :
    Module.finrank k (H1 k n) = Module.finrank k (H0 k (-2 - n)) := by
  rw [finrank_H1_of_nonneg k n hn, finrank_H0_of_neg k (-2 - n) (by omega)]

/-- Serre duality on ℙ¹, negative case: `dim H¹(O(n)) = dim H⁰(O(-2 - n))`.
For `n < 0`, `-2 - n` may be `≥ 0` or `= -1`; both sub-cases give matching
dimensions. -/
theorem serre_duality_neg (n : ℤ) (hn : n < 0) :
    Module.finrank k (H1 k n) = Module.finrank k (H0 k (-2 - n)) := by
  rw [finrank_H1_of_neg k n hn]
  by_cases h : -2 - n < 0
  ·
    rw [finrank_H0_of_neg k (-2 - n) h]

    have : n = -1 := by omega
    subst this; simp
  ·
    push Not at h
    rw [finrank_H0_of_nonneg k (-2 - n) h]

    congr 1; omega

end SerreDuality


section EulerCharacteristic

open CohomologyP1

variable (k : Type) [Field k]

/-- Euler characteristic of `O(n)` on ℙ¹: `χ(O(n)) = h⁰(O(n)) - h¹(O(n)) = n + 1`.
This is the Riemann–Roch formula for line bundles on ℙ¹ (genus `0`). -/
theorem euler_characteristic (n : ℤ) :
    (Module.finrank k (H0 k n) : ℤ) -
    (Module.finrank k (H1 k n) : ℤ) = n + 1 := by
  by_cases hn : 0 ≤ n
  ·
    rw [finrank_H0_of_nonneg k n hn, finrank_H1_of_nonneg k n hn]
    simp [Int.toNat_of_nonneg (by omega : 0 ≤ n + 1)]
  ·
    push Not at hn
    rw [finrank_H0_of_neg k n hn, finrank_H1_of_neg k n hn]
    simp; omega

end EulerCharacteristic

end SheafCohomology
