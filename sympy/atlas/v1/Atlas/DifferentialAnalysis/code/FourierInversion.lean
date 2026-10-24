/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierInversion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import sympy.atlas.v1.Atlas.DifferentialAnalysis.code.TestFunctions
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.TestFunctions
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SobolevEmbedding
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SchwartzRepresentation
import sympy.atlas.v1.Atlas.DifferentialAnalysis.code.SobolevEmbedding
import sympy.atlas.v1.Atlas.DifferentialAnalysis.code.SchwartzRepresentation
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.TransferInstance
import Mathlib.Analysis.Fourier.LpSpace

open Real MeasureTheory MeasureTheory.Measure
open scoped FourierTransform ComplexInnerProductSpace SchwartzMap

noncomputable section

namespace FourierInversion

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

section Isomorphism

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The Fourier transform as a continuous `ℂ`-linear equivalence on the
Schwartz space `𝓢(V, E)`. -/
def fourierSchwartzCLE : 𝓢(V, E) ≃L[ℂ] 𝓢(V, E) :=
  FourierTransform.fourierCLE ℂ 𝓢(V, E)

/-- The Fourier transform on tempered distributions packaged as a `ℂ`-linear
equivalence `𝓢'(E, F) ≃ₗ[ℂ] 𝓢'(E, F)`. -/
def fourierTemperedDistributionEquiv : 𝓢'(E, F) ≃ₗ[ℂ] 𝓢'(E, F) :=
  fourierEquiv ℂ 𝓢'(E, F)

/-- Fourier inversion on tempered distributions: `𝓕⁻(𝓕 u) = u`. -/
@[simp]
theorem fourier_inverse_left (u : 𝓢'(E, F)) : 𝓕⁻ (𝓕 u) = u :=
  fourierInv_fourier_eq u

/-- Fourier inversion on tempered distributions: `𝓕(𝓕⁻ u) = u`. -/
theorem fourier_inverse_right (u : 𝓢'(E, F)) : 𝓕 (𝓕⁻ u) = u :=
  fourier_fourierInv_eq u

variable {n : ℕ}

/-- The `k`-fold iterated distributional derivative in the `j`-th coordinate
direction, applied to a tempered distribution `u`. -/
def iterDistribDerivCoord (j : Fin n) (k : ℕ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) :=
  (fun v => ∂_{EuclideanSpace.single j (1 : ℝ)} v)^[k] u

/-- The mixed iterated distributional derivative `∂^α u` indexed by a
multi-index `α : Fin n → ℕ`, defined by composing the per-coordinate iterated
derivatives over all coordinates. -/
def iterDistribDeriv (α : Fin n → ℕ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) :=
  (List.finRange n).foldr (fun j v => iterDistribDerivCoord j (α j) v) u

/-- The `k`-fold iterated operation of multiplication by `2πi·ξ_j` on a
tempered distribution, which is the Fourier-side counterpart of the iterated
derivative in the `j`-th coordinate. -/
def iterCoordMulFourier (j : Fin n) (k : ℕ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) :=
  (fun v => (2 * ↑Real.pi * Complex.I) •
    smulLeftCLM ℂ (fun ξ => ↑(@inner ℝ _ _ ξ (EuclideanSpace.single j 1))) v)^[k] u

/-- The multi-index iterated multiplication operation `(2πi)^|α| ξ^α u` on a
tempered distribution, Fourier-dual to the multi-index derivative `∂^α`. -/
def iterMulFourier (α : Fin n → ℕ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) :=
  (List.finRange n).foldr (fun j v => iterCoordMulFourier j (α j) v) u

/-- The `k`-fold iterated operation of multiplication by `-2πi·x_j` on a
tempered distribution, used to express the iterated coordinate derivative on
the Fourier side after inversion. -/
def iterCoordNegMulDistrib (j : Fin n) (k : ℕ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) :=
  (fun v => -(2 * ↑Real.pi * Complex.I) •
    smulLeftCLM ℂ (fun x => ↑(@inner ℝ _ _ x (EuclideanSpace.single j 1))) v)^[k] u

/-- The multi-index iterated multiplication `(-2πi)^|α| x^α u` on a tempered
distribution, packaged via a fold over coordinates. -/
def iterNegMulDistrib (α : Fin n → ℕ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) :=
  (List.finRange n).foldr (fun j v => iterCoordNegMulDistrib j (α j) v) u

/-- The Sobolev weight `⟨ξ⟩^s = (1 + ‖ξ‖²)^{s/2}`, written using the
Japanese bracket. This is the standard symbol whose `L²`-decay determines
the Sobolev exponent `s`. -/
def sobolevWeight (s : ℝ) (ξ : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (japaneseBracket n ξ) ^ s

/-- The Sobolev weight `⟨ξ⟩^s` is strictly positive for every `ξ` and every
real exponent `s`. -/
theorem sobolevWeight_pos (s : ℝ) (ξ : EuclideanSpace ℝ (Fin n)) :
    0 < sobolevWeight n s ξ :=
  Real.rpow_pos_of_pos (japaneseBracket_pos n ξ) s

/-- Membership in the Sobolev space `H^s(ℝⁿ)`: a tempered distribution `u`
belongs to `H^s` if there exists `g ∈ L²` such that, for every Schwartz
function `φ`, `(𝓕 u)(φ) = ∫ ⟨ξ⟩^{-s} g(ξ) φ(ξ) dξ`. Equivalently, `𝓕 u`
is given by integration against the `L²` function `⟨ξ⟩^{-s} g`. -/
def MemHs (s : ℝ) (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : Prop :=
  ∃ g : EuclideanSpace ℝ (Fin n) → ℂ,
    MemLp g 2 ∧
    ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      (𝓕 u) φ = ∫ ξ, (sobolevWeight n s ξ : ℂ)⁻¹ * g ξ * φ ξ

/-- The Sobolev space `H^s(ℝⁿ)` realised as the subtype of tempered
distributions satisfying `MemHs n s`. -/
def Hs (s : ℝ) : Type :=
  { u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) // MemHs n s u }

/-- The `L²` "witness" function attached to a Sobolev distribution: it is
the function `g` produced by the existential in `MemHs`. Concretely,
`𝓕 u = ⟨ξ⟩^{-s} · witnessFunc s u` as distributions. -/
def Hs.witnessFunc (s : ℝ) (u : Hs n s) : EuclideanSpace ℝ (Fin n) → ℂ :=
  u.2.choose

/-- The witness function attached to a Sobolev distribution is in `L²`. -/
lemma Hs.witnessFunc_memLp (s : ℝ) (u : Hs n s) :
    MemLp (Hs.witnessFunc n s u) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  u.2.choose_spec.1

/-- The witness function packaged as an honest element of the Hilbert space
`L²(ℝⁿ; ℂ)`. -/
def Hs.witnessL2 (s : ℝ) (u : Hs n s) :
    MeasureTheory.Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  MemLp.toLp (Hs.witnessFunc n s u) (Hs.witnessFunc_memLp n s u)

/-- The defining property of `Hs.witnessFunc`: pairing `𝓕 u` against a
Schwartz function recovers the integral of `⟨ξ⟩^{-s} · witnessFunc · φ`. -/
lemma Hs.witnessFunc_spec (s : ℝ) (u : Hs n s) :
    ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      (𝓕 u.1) φ = ∫ ξ, (sobolevWeight n s ξ : ℂ)⁻¹ * Hs.witnessFunc n s u ξ * φ ξ :=
  u.2.choose_spec.2


/-- Given an `L²` function `f`, construct the element of `H^s` whose witness
function is `f`: namely, `𝓕⁻¹ (⟨ξ⟩^{-s} f)` as a tempered distribution. -/
def Hs.fromL2 (s : ℝ)
    (f : MeasureTheory.Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    Hs n s := by

  set w : EuclideanSpace ℝ (Fin n) → ℂ := fun ξ => (sobolevWeight n s ξ : ℂ)⁻¹


  set v : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) :=
    TemperedDistribution.smulLeftCLM ℂ w (Lp.toTemperedDistribution f)

  set u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) := 𝓕⁻ v

  have hmem : MemHs n s u := by
    refine ⟨↑↑f, Lp.memLp f, fun φ => ?_⟩

    have hFu : 𝓕 u = v := FourierInversion.fourier_inverse_right v
    rw [hFu]


    simp only [v, TemperedDistribution.smulLeftCLM_apply_apply,
      Lp.toTemperedDistribution_apply]


    have hw_temp : w.HasTemperateGrowth := by
      show (fun ξ => (sobolevWeight n s ξ : ℂ)⁻¹).HasTemperateGrowth

      have heq : (fun ξ : EuclideanSpace ℝ (Fin n) => (sobolevWeight n s ξ : ℂ)⁻¹) =
          (fun ξ => (sobolevWeight n (-s) ξ : ℂ)) := by
        ext ξ
        simp only [sobolevWeight]
        rw [← Complex.ofReal_inv]
        congr 1
        exact (rpow_neg (le_of_lt (japaneseBracket_pos n ξ)) s).symm
      rw [heq]

      apply Function.Complex.hasTemperateGrowth_ofReal.comp
      show (fun ξ : EuclideanSpace ℝ (Fin n) => sobolevWeight n (-s) ξ).HasTemperateGrowth
      show (fun ξ => (japaneseBracket n ξ) ^ (-s)).HasTemperateGrowth
      have : (fun ξ : EuclideanSpace ℝ (Fin n) => (1 + ‖ξ‖ ^ 2) ^ ((-s) / 2)).HasTemperateGrowth :=
        Function.hasTemperateGrowth_one_add_norm_sq_rpow _ ((-s) / 2)
      suffices h : (fun ξ : EuclideanSpace ℝ (Fin n) => (japaneseBracket n ξ) ^ (-s)) =
          (fun ξ => (1 + ‖ξ‖ ^ 2) ^ ((-s) / 2)) by
        rw [h]; exact this
      ext ξ
      simp only [japaneseBracket]
      rw [Real.sqrt_eq_rpow, ← rpow_mul (by positivity : (0 : ℝ) ≤ 1 + ‖ξ‖ ^ 2)]
      congr 1
      ring

    congr 1
    ext ξ
    rw [SchwartzMap.smulLeftCLM_apply_apply hw_temp]
    simp only [smul_eq_mul, w]
    ring
  exact ⟨u, hmem⟩

/-- Right inverse: extracting the `L²` witness from `Hs.fromL2 s f` recovers
`f`. Uses Lebesgue uniqueness of integration against smooth, compactly
supported test functions to conclude the underlying functions are equal a.e. -/
theorem Hs.fromL2_witnessL2 (s : ℝ)
    (f : MeasureTheory.Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    Hs.witnessL2 n s (Hs.fromL2 n s f) = f := by

  apply MeasureTheory.Lp.ext

  have h_wl2 : ↑↑(Hs.witnessL2 n s (Hs.fromL2 n s f)) =ᵐ[volume]
      Hs.witnessFunc n s (Hs.fromL2 n s f) :=
    MeasureTheory.MemLp.coeFn_toLp _

  refine h_wl2.trans ?_


  set u := Hs.fromL2 n s f
  set g₁ := Hs.witnessFunc n s u
  set g₂ : EuclideanSpace ℝ (Fin n) → ℂ := ↑↑f

  have hg₁_spec := Hs.witnessFunc_spec n s u

  have hg₂_spec : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      (𝓕 u.1) φ = ∫ ξ, (sobolevWeight n s ξ : ℂ)⁻¹ * g₂ ξ * φ ξ := by
    intro φ


    have hFu : 𝓕 u.1 = TemperedDistribution.smulLeftCLM ℂ
        (fun ξ => (sobolevWeight n s ξ : ℂ)⁻¹)
        (MeasureTheory.Lp.toTemperedDistribution f) :=
      FourierInversion.fourier_inverse_right _
    rw [hFu]
    simp only [TemperedDistribution.smulLeftCLM_apply_apply,
      MeasureTheory.Lp.toTemperedDistribution_apply]
    have hw_temp : (fun ξ : EuclideanSpace ℝ (Fin n) =>
        (sobolevWeight n s ξ : ℂ)⁻¹).HasTemperateGrowth := by
      have heq : (fun ξ : EuclideanSpace ℝ (Fin n) => (sobolevWeight n s ξ : ℂ)⁻¹) =
          (fun ξ => (sobolevWeight n (-s) ξ : ℂ)) := by
        ext ξ
        simp only [sobolevWeight]
        rw [← Complex.ofReal_inv]
        congr 1
        exact (rpow_neg (le_of_lt (japaneseBracket_pos n ξ)) s).symm
      rw [heq]
      apply Function.Complex.hasTemperateGrowth_ofReal.comp
      show (fun ξ : EuclideanSpace ℝ (Fin n) => sobolevWeight n (-s) ξ).HasTemperateGrowth
      show (fun ξ => (japaneseBracket n ξ) ^ (-s)).HasTemperateGrowth
      have : (fun ξ : EuclideanSpace ℝ (Fin n) => (1 + ‖ξ‖ ^ 2) ^ ((-s) / 2)).HasTemperateGrowth :=
        Function.hasTemperateGrowth_one_add_norm_sq_rpow _ ((-s) / 2)
      suffices h : (fun ξ : EuclideanSpace ℝ (Fin n) => (japaneseBracket n ξ) ^ (-s)) =
          (fun ξ => (1 + ‖ξ‖ ^ 2) ^ ((-s) / 2)) by
        rw [h]; exact this
      ext ξ
      simp only [japaneseBracket]
      rw [Real.sqrt_eq_rpow, ← rpow_mul (by positivity : (0 : ℝ) ≤ 1 + ‖ξ‖ ^ 2)]
      congr 1
      ring
    congr 1
    ext ξ
    rw [SchwartzMap.smulLeftCLM_apply_apply hw_temp]
    simp only [smul_eq_mul]
    ring

  have hint_eq : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      ∫ ξ, (sobolevWeight n s ξ : ℂ)⁻¹ * g₁ ξ * φ ξ =
      ∫ ξ, (sobolevWeight n s ξ : ℂ)⁻¹ * g₂ ξ * φ ξ := by
    intro φ
    rw [← hg₁_spec φ, ← hg₂_spec φ]


  have hg₁_li : MeasureTheory.LocallyIntegrable g₁ volume :=
    (Hs.witnessFunc_memLp n s u).locallyIntegrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hg₂_li : MeasureTheory.LocallyIntegrable g₂ volume :=
    (MeasureTheory.Lp.memLp f).locallyIntegrable (by norm_num : (1 : ENNReal) ≤ 2)
  apply ae_eq_of_integral_contDiff_smul_eq hg₁_li hg₂_li
  intro g_test hg_smooth hg_supp


  have hw_htg : (fun ξ : EuclideanSpace ℝ (Fin n) => sobolevWeight n s ξ).HasTemperateGrowth := by
    show (fun ξ => (japaneseBracket n ξ) ^ s).HasTemperateGrowth
    have : (fun ξ : EuclideanSpace ℝ (Fin n) => (1 + ‖ξ‖ ^ 2) ^ (s / 2)).HasTemperateGrowth :=
      Function.hasTemperateGrowth_one_add_norm_sq_rpow _ (s / 2)
    suffices h : (fun ξ : EuclideanSpace ℝ (Fin n) => (japaneseBracket n ξ) ^ s) =
        (fun ξ => (1 + ‖ξ‖ ^ 2) ^ (s / 2)) by
      rw [h]; exact this
    ext ξ
    simp only [japaneseBracket]
    rw [Real.sqrt_eq_rpow, ← rpow_mul (by positivity : (0 : ℝ) ≤ 1 + ‖ξ‖ ^ 2)]
    congr 1; ring
  have hψ_smooth := hg_smooth.mul hw_htg.1
  have hψ_supp : HasCompactSupport (fun ξ => g_test ξ * sobolevWeight n s ξ) :=
    hg_supp.mul_right

  set φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) :=
    (hψ_supp.comp_left Complex.ofReal_zero).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hψ_smooth)

  have key := hint_eq φ


  have heq_lhs : (fun x => g_test x • g₁ x) =
      (fun x => (sobolevWeight n s x : ℂ)⁻¹ * g₁ x * φ x) := by
    ext ξ
    simp only [φ, HasCompactSupport.toSchwartzMap_toFun, Function.comp,
      Complex.ofReal_mul, smul_eq_mul, Complex.real_smul]
    have hw_ne : (sobolevWeight n s ξ : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (sobolevWeight_pos n s ξ))
    field_simp
  have heq_rhs : (fun x => g_test x • g₂ x) =
      (fun x => (sobolevWeight n s x : ℂ)⁻¹ * g₂ x * φ x) := by
    ext ξ
    simp only [φ, HasCompactSupport.toSchwartzMap_toFun, Function.comp,
      Complex.ofReal_mul, smul_eq_mul, Complex.real_smul]
    have hw_ne : (sobolevWeight n s ξ : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (sobolevWeight_pos n s ξ))
    field_simp
  calc ∫ x, g_test x • g₁ x
      = ∫ x, (sobolevWeight n s x : ℂ)⁻¹ * g₁ x * φ x := congr_arg _ heq_lhs
    _ = ∫ x, (sobolevWeight n s x : ℂ)⁻¹ * g₂ x * φ x := key
    _ = ∫ x, g_test x • g₂ x := congr_arg _ heq_rhs.symm

/-- Left inverse: starting from a Sobolev distribution `u`, taking the
`L²` witness and then applying `Hs.fromL2` returns `u`. Uses Fourier
inversion on tempered distributions. -/
theorem Hs.witnessL2_fromL2 (s : ℝ) (u : Hs n s) :
    Hs.fromL2 n s (Hs.witnessL2 n s u) = u := by
  apply Subtype.ext

  simp only [Hs.fromL2, Hs.witnessL2]


  suffices h : (TemperedDistribution.smulLeftCLM ℂ
      (fun ξ => (sobolevWeight n s ξ : ℂ)⁻¹))
      (MeasureTheory.Lp.toTemperedDistribution
        (MemLp.toLp (Hs.witnessFunc n s u) (Hs.witnessFunc_memLp n s u))) =
      𝓕 u.val by
    rw [h]
    exact FourierInversion.fourier_inverse_left u.val

  apply ContinuousLinearMap.ext
  intro φ


  have hw_temp : (fun ξ => (sobolevWeight n s ξ : ℂ)⁻¹).HasTemperateGrowth := by
    have heq : (fun ξ : EuclideanSpace ℝ (Fin n) => (sobolevWeight n s ξ : ℂ)⁻¹) =
        (fun ξ => (sobolevWeight n (-s) ξ : ℂ)) := by
      ext ξ
      simp only [sobolevWeight]
      rw [← Complex.ofReal_inv]
      congr 1
      exact (rpow_neg (le_of_lt (japaneseBracket_pos n ξ)) s).symm
    rw [heq]
    apply Function.Complex.hasTemperateGrowth_ofReal.comp
    show (fun ξ : EuclideanSpace ℝ (Fin n) => sobolevWeight n (-s) ξ).HasTemperateGrowth
    show (fun ξ => (japaneseBracket n ξ) ^ (-s)).HasTemperateGrowth
    have : (fun ξ : EuclideanSpace ℝ (Fin n) => (1 + ‖ξ‖ ^ 2) ^ ((-s) / 2)).HasTemperateGrowth :=
      Function.hasTemperateGrowth_one_add_norm_sq_rpow _ ((-s) / 2)
    suffices hh : (fun ξ : EuclideanSpace ℝ (Fin n) => (japaneseBracket n ξ) ^ (-s)) =
        (fun ξ => (1 + ‖ξ‖ ^ 2) ^ ((-s) / 2)) by
      rw [hh]; exact this
    ext ξ
    simp only [japaneseBracket]
    rw [Real.sqrt_eq_rpow, ← rpow_mul (by positivity : (0 : ℝ) ≤ 1 + ‖ξ‖ ^ 2)]
    congr 1
    ring


  trans (∫ ξ : EuclideanSpace ℝ (Fin n),
    (sobolevWeight n s ξ : ℂ)⁻¹ * Hs.witnessFunc n s u ξ * φ ξ)
  ·
    show ((TemperedDistribution.smulLeftCLM ℂ
        (fun ξ => (sobolevWeight n s ξ : ℂ)⁻¹))
        (MeasureTheory.Lp.toTemperedDistribution
          (MemLp.toLp (Hs.witnessFunc n s u) (Hs.witnessFunc_memLp n s u)))) φ =
      ∫ ξ : EuclideanSpace ℝ (Fin n),
        (sobolevWeight n s ξ : ℂ)⁻¹ * Hs.witnessFunc n s u ξ * φ ξ
    rw [show ((TemperedDistribution.smulLeftCLM ℂ
        (fun ξ => (sobolevWeight n s ξ : ℂ)⁻¹))
        (MeasureTheory.Lp.toTemperedDistribution
          (MemLp.toLp (Hs.witnessFunc n s u) (Hs.witnessFunc_memLp n s u)))) φ =
      (MeasureTheory.Lp.toTemperedDistribution
        (MemLp.toLp (Hs.witnessFunc n s u) (Hs.witnessFunc_memLp n s u)))
        (SchwartzMap.smulLeftCLM ℂ (fun ξ => (sobolevWeight n s ξ : ℂ)⁻¹) φ) from
      TemperedDistribution.smulLeftCLM_apply_apply _ _ _]
    rw [MeasureTheory.Lp.toTemperedDistribution_apply]
    refine MeasureTheory.integral_congr_ae ?_
    have hae := MeasureTheory.MemLp.coeFn_toLp
      (f := Hs.witnessFunc n s u) (hf := Hs.witnessFunc_memLp n s u)
    filter_upwards [hae] with ξ hξ
    simp only [smul_eq_mul]
    rw [SchwartzMap.smulLeftCLM_apply_apply hw_temp, smul_eq_mul, hξ]
    ring
  ·
    exact (Hs.witnessFunc_spec n s u φ).symm

/-- The set-level bijection `Hs n s ≃ L²(ℝⁿ; ℂ)` provided by the witness
function construction. -/
noncomputable def Hs.equivLp (s : ℝ) :
    Hs n s ≃ MeasureTheory.Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) where
  toFun := Hs.witnessL2 n s
  invFun := Hs.fromL2 n s
  left_inv := Hs.witnessL2_fromL2 n s
  right_inv := Hs.fromL2_witnessL2 n s


/-- Transport the `NormedAddCommGroup` structure from `L²(ℝⁿ; ℂ)` to
`Hs n s` along the bijection `Hs.equivLp`. -/
@[reducible]
noncomputable def Hs.instNormedAddCommGroup (s : ℝ) : NormedAddCommGroup (Hs n s) :=
  (Hs.equivLp n s).normedAddCommGroup
attribute [instance] Hs.instNormedAddCommGroup


/-- Transport the complex inner-product-space structure from `L²(ℝⁿ; ℂ)` to
`Hs n s` along the bijection `Hs.equivLp`. The inner product on `H^s` is
`⟨u, v⟩_{H^s} := ⟨witnessL2 u, witnessL2 v⟩_{L²}`. -/
@[reducible]
noncomputable def Hs.instInnerProductSpace (s : ℝ) : InnerProductSpace ℂ (Hs n s) := by
  letI := Hs.instNormedAddCommGroup n s
  letI : NormedSpace ℂ (Hs n s) := Equiv.normedSpace ℂ (Hs.equivLp n s)
  letI : Inner ℂ (Hs n s) :=
    ⟨fun x y => (inner (𝕜 := ℂ) (Hs.equivLp n s x) (Hs.equivLp n s y) : ℂ)⟩
  exact {
    norm_sq_eq_re_inner := fun x => by
      show ‖x‖ ^ 2 = RCLike.re (inner (𝕜 := ℂ) (Hs.equivLp n s x) (Hs.equivLp n s x))
      have h : ‖x‖ = ‖Hs.equivLp n s x‖ := rfl
      rw [h]
      exact InnerProductSpace.norm_sq_eq_re_inner (Hs.equivLp n s x)
    conj_inner_symm := fun x y => by
      show starRingEnd ℂ (inner (𝕜 := ℂ) (Hs.equivLp n s y) (Hs.equivLp n s x)) =
           inner (𝕜 := ℂ) (Hs.equivLp n s x) (Hs.equivLp n s y)
      exact InnerProductSpace.conj_inner_symm (Hs.equivLp n s x) (Hs.equivLp n s y)
    add_left := fun x y z => by
      show inner (𝕜 := ℂ) (Hs.equivLp n s (x + y)) (Hs.equivLp n s z) =
           inner (𝕜 := ℂ) (Hs.equivLp n s x) (Hs.equivLp n s z) +
           inner (𝕜 := ℂ) (Hs.equivLp n s y) (Hs.equivLp n s z)
      have hadd : (Hs.equivLp n s) (x + y) = (Hs.equivLp n s) x + (Hs.equivLp n s) y := by
        simp [show (x + y : Hs n s) = (Hs.equivLp n s).symm
          ((Hs.equivLp n s) x + (Hs.equivLp n s) y) from rfl]
      rw [hadd]
      exact inner_add_left _ _ _
    smul_left := fun x y r => by
      show inner (𝕜 := ℂ) (Hs.equivLp n s (r • x)) (Hs.equivLp n s y) =
           starRingEnd ℂ r * inner (𝕜 := ℂ) (Hs.equivLp n s x) (Hs.equivLp n s y)
      have hsmul : (Hs.equivLp n s) (r • x) = r • (Hs.equivLp n s) x := by
        simp [show (r • x : Hs n s) = (Hs.equivLp n s).symm
          (r • (Hs.equivLp n s) x) from rfl]
      rw [hsmul]
      exact inner_smul_left _ _ _
  }
attribute [instance] Hs.instInnerProductSpace


/-- The norm on `H^s` is defined to equal the `L²` norm of the witness:
`‖u‖_{H^s} = ‖witnessL2 u‖_{L²}`. -/
theorem Hs.norm_witnessL2 (s : ℝ) (u : Hs n s) :
    ‖u‖ = ‖Hs.witnessL2 n s u‖ := rfl


/-- The witness map `Hs n s → L²` is additive. -/
theorem Hs.witnessL2_add (s : ℝ) (u v : Hs n s) :
    Hs.witnessL2 n s (u + v) = Hs.witnessL2 n s u + Hs.witnessL2 n s v := by
  show (Hs.equivLp n s) (u + v) = (Hs.equivLp n s) u + (Hs.equivLp n s) v
  simp [show (u + v : Hs n s) = (Hs.equivLp n s).symm
    ((Hs.equivLp n s) u + (Hs.equivLp n s) v) from rfl]


/-- The witness map `Hs n s → L²` is `ℂ`-linear. -/
theorem Hs.witnessL2_smul (s : ℝ) (c : ℂ) (u : Hs n s) :
    Hs.witnessL2 n s (c • u) = c • Hs.witnessL2 n s u := by
  show (Hs.equivLp n s) (c • u) = c • (Hs.equivLp n s) u
  simp [show (c • u : Hs n s) = (Hs.equivLp n s).symm
    (c • (Hs.equivLp n s) u) from rfl]

/-- The "Fourier-weight" linear isometric equivalence between `H^s(ℝⁿ)` and
`L²(ℝⁿ; ℂ)` sending each `u` to its `L²` witness `⟨ξ⟩^s · 𝓕u`. This is the
fundamental Hilbert-space identification underlying the definition of
`H^s`. -/
noncomputable def fourierWeightEquiv (s : ℝ) :
    Hs n s ≃ₗᵢ[ℂ] MeasureTheory.Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  LinearIsometryEquiv.ofSurjective
    ({ toLinearMap :=
        { toFun := Hs.witnessL2 n s
          map_add' := Hs.witnessL2_add n s
          map_smul' := Hs.witnessL2_smul n s }
       norm_map' := fun u => (Hs.norm_witnessL2 n s u).symm } : Hs n s →ₗᵢ[ℂ]
         MeasureTheory.Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (fun f => ⟨Hs.fromL2 n s f, Hs.fromL2_witnessL2 n s f⟩)

/-- The Sobolev duality identification: `H^{-s} ≃ (H^s)'` as anti-linear
isometric equivalences, obtained by composing the two Fourier-weight
isometries with the Riesz representation `H^s ≃ (H^s)'`. This is part of
Proposition 9.8 of Melrose. -/
noncomputable def dualIdentification (s : ℝ) :
    Hs n (-s) ≃ₗᵢ⋆[ℂ] (Hs n s →L[ℂ] ℂ) :=
  ((fourierWeightEquiv n (-s)).trans (fourierWeightEquiv n s).symm).trans
    (InnerProductSpace.toDual ℂ (Hs n s))
