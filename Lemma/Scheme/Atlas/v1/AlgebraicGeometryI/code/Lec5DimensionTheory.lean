import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.Lec5DimensionTheory
open Set


/--
[irreducible_curves_homeomorphic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec5DimensionTheory.lean)
-/
@[path]
lemma irreducible_curves_homeomorphic
  {X Y : Type u}
  [TopologicalSpace X]
  [TopologicalSpace Y]
  [T1Space X]
  [T1Space Y]
-- given
  (hX : ProperClosedFinite X)
  (hY : ProperClosedFinite Y)
  (hcard : Cardinal.mk X = Cardinal.mk Y) :
-- imply
  Nonempty (X ≃ₜ Y) := by
-- proof
  rw [Cardinal.eq] at hcard
  obtain ⟨e⟩ := hcard
  exact ⟨Homeomorph.ofEquivProperClosedFinite hX hY e⟩

/--
[WithBot.le_zero_of_add_one_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec5DimensionTheory.lean)
-/
@[path]
lemma WithBot.le_zero_of_add_one_le_one
  {x : WithBot ℕ∞}
-- given
  (h : x + 1 ≤ 1) :
-- imply
  x ≤ 0 := by
-- proof
  match x, h with
  | ⊥, _ => exact bot_le
  | (y : ℕ∞), h =>
    show (↑y : WithBot ℕ∞) ≤ ↑(0 : ℕ∞); rw [WithBot.coe_le_coe]
    match y with
    | ⊤ =>
      exfalso
      have h1 : (↑(⊤ : ℕ∞) : WithBot ℕ∞) + 1 = ↑(⊤ : ℕ∞) := by
        show (↑(⊤ : ℕ∞) : WithBot ℕ∞) + ↑(1 : ℕ∞) = ↑(⊤ : ℕ∞)
        rw [← WithBot.coe_add]; simp
      rw [h1, show (1 : WithBot ℕ∞) = ↑((1 : ℕ) : ℕ∞) from rfl, WithBot.coe_le_coe] at h
      simp at h
    | (n : ℕ) =>
      show (↑n : ℕ∞) ≤ 0
      have hconv : (↑(↑n : ℕ∞) : WithBot ℕ∞) + 1 = ↑((↑(n + 1) : ℕ∞)) := by
        show (↑(↑n : ℕ∞) : WithBot ℕ∞) + ↑(1 : ℕ∞) = _; rw [← WithBot.coe_add]; norm_cast
      rw [hconv, show (1 : WithBot ℕ∞) = ↑((1 : ℕ) : ℕ∞) from rfl, WithBot.coe_le_coe] at h
      norm_cast at h ⊢; omega

/--
[isArtinianRing_quotient_of_dim_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec5DimensionTheory.lean)
-/
@[path]
lemma isArtinianRing_quotient_of_dim_le_one
  [CommRing A]
  [IsDomain A]
  [IsNoetherianRing A]
  {I : Ideal A}
-- given
  (hdim : ringKrullDim A ≤ 1)
  (hI : I ≠ ⊥) :
-- imply
  IsArtinianRing (A ⧸ I) := by
-- proof
  have ⟨g, hgI, hg0⟩ : ∃ g ∈ I, g ≠ (0 : A) := by
    by_contra h; push Not at h; apply hI
    ext x; simp; exact ⟨h x, fun hx => hx ▸ I.zero_mem⟩
  have h2 : ringKrullDim (A ⧸ Ideal.span {g}) ≤ 0 :=
    WithBot.le_zero_of_add_one_le_one _
      (le_trans (ringKrullDim_quotient_succ_le_of_nonZeroDivisor
        (mem_nonZeroDivisors_of_ne_zero hg0)) hdim)
  have hgI' : Ideal.span {g} ≤ I := by rwa [Ideal.span_le, Set.singleton_subset_iff]
  haveI : Ring.KrullDimLE 0 (A ⧸ I) := ⟨le_trans (ringKrullDim_le_of_surjective
    (Ideal.Quotient.factor hgI') (Ideal.Quotient.factor_surjective hgI')) h2⟩
  haveI : IsNoetherianRing (A ⧸ I) := Ideal.Quotient.isNoetherianRing I
  exact IsNoetherianRing.isArtinianRing_of_krullDimLE_zero

/--
[zeroLocus_finite_of_dim_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec5DimensionTheory.lean)
-/
@[path]
lemma zeroLocus_finite_of_dim_le_one
  [CommRing A]
  [IsDomain A]
  [IsNoetherianRing A]
  {I : Ideal A}
-- given
  (hdim : ringKrullDim A ≤ 1)
  (hI : I ≠ ⊥) :
-- imply
  (PrimeSpectrum.zeroLocus (I : Set A)).Finite := by
-- proof
  haveI := isArtinianRing_quotient_of_dim_le_one hdim I hI
  haveI : Empty.Finite (PrimeSpectrum (A ⧸ I)) := IsArtinianRing.instFinitePrimeSpectrum _
  have : Empty.Finite ↥(PrimeSpectrum.zeroLocus (I : Set A)) :=
    Empty.Finite.of_equiv _ (Ideal.primeSpectrumQuotientOrderIsoZeroLocus I).toEquiv
  exact Set.toFinite _

/--
[properClosedFinite_primeSpectrum_of_dim_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec5DimensionTheory.lean)
-/
@[path]
lemma properClosedFinite_primeSpectrum_of_dim_le_one
  [CommRing A]
  [IsDomain A]
  [IsNoetherianRing A]
-- given
  (hdim : ringKrullDim A ≤ 1) :
-- imply
  ProperClosedFinite (PrimeSpectrum A) := by
-- proof
  intro S hS hne
  have hS_eq : S = PrimeSpectrum.zeroLocus ↑(PrimeSpectrum.vanishingIdeal S) := by
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hS.closure_eq]
  have hI_ne : PrimeSpectrum.vanishingIdeal S ≠ ⊥ := by
    intro h; apply hne; rw [hS_eq, h, PrimeSpectrum.zeroLocus_bot]
  rw [hS_eq]
  exact zeroLocus_finite_of_dim_le_one hdim _ hI_ne

/--
[continuous_of_injective_of_T1_properClosedFinite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec5DimensionTheory.lean)
-/
@[path]
private lemma continuous_of_injective_of_T1_properClosedFinite_eq
  [TopologicalSpace X]
  [TopologicalSpace Y]
  [T1Space X]
  {f : X → Y}
-- given
  (hY : ProperClosedFinite Y)
  (hf_inj : Function.Injective f) :
-- imply
  Continuous f := by
-- proof
  apply continuous_of_injective_of_T1_properClosedFinite hY hf_inj


-- created on 2026-10-23
