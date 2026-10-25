/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Def.Analysis.CStarAlgebra.Stinespring.Part4


section

open scoped CStarAlgebra InnerProduct

open scoped ComplexOrder InnerProductSpace

universe u

namespace MetaMathlibExt.Stinespring

-- N6 (i) mul
theorem stinespringLeftMul0_mul (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (c d : A) :
    stinespringLeftMul0 A H φ (c * d)
      = stinespringLeftMul0 A H φ c ∘ₗ stinespringLeftMul0 A H φ d := by
  apply LinearMap.ext
  intro f
  simp only [stinespringLeftMul0, LinearMap.coe_comp, Function.comp_apply,
    Finsupp.lmapDomain_apply, LinearEquiv.coe_coe, StinespringPre.ofPre_toPre]
  rw [← Finsupp.mapDomain_comp]
  have hfun : (fun a : A => (c * d) * a) = ((fun a => c * a) ∘ fun a => d * a) := by
    funext a
    simp only [Function.comp_apply]
    exact mul_assoc c d a
  rw [hfun]

-- N6 (i) one
theorem stinespringLeftMul0_one (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) :
    stinespringLeftMul0 A H φ 1 = LinearMap.id := by
  apply LinearMap.ext
  intro f
  simp only [stinespringLeftMul0, LinearMap.coe_comp, Function.comp_apply,
    Finsupp.lmapDomain_apply, LinearEquiv.coe_coe, LinearMap.id_apply]
  rw [show (fun a : A => (1 : A) * a) = id from funext fun a => one_mul a]
  rw [Finsupp.mapDomain_id]
  exact StinespringPre.toPre_ofPre A H φ f

-- N6 (ii) inner formula
theorem stinespringLeftMul0_inner (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (f g : StinespringPre A H φ) (c : A) :
    ⟪f, stinespringLeftMul0 A H φ c g⟫_ℂ = stinespringPhi A H φ f c g := by
  have hmid : ∀ (a : A) (x : H),
      ((Finsupp.mapDomain (fun b => c * b) (StinespringPre.ofPre A H φ g)).sum
        (fun b y => ⟪x, φ (star a * b) y⟫_ℂ))
      = ((StinespringPre.ofPre A H φ g).sum
        (fun b y => ⟪x, φ (star a * (c * b)) y⟫_ℂ)) := by
    intro a x
    apply Finsupp.sum_mapDomain_index
    · intro b
      simp [map_zero]
    · intro b y₁ y₂
      show ⟪x, φ (star a * b) (y₁ + y₂)⟫_ℂ = _
      rw [map_add, inner_add_right]
  rw [stinespring_pre_inner_def]
  change stinespringForm φ _ _ = _
  simp only [stinespringForm, stinespringLeftMul0, LinearMap.coe_comp, Function.comp_apply,
    Finsupp.lmapDomain_apply, LinearEquiv.coe_coe, StinespringPre.ofPre_toPre,
    stinespringPhi]
  exact Finsupp.sum_congr (fun a _ => hmid a _)

-- N6 (iii) Phi add
theorem stinespringPhi_add (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (f : StinespringPre A H φ) (c d : A)
    (g : StinespringPre A H φ) :
    stinespringPhi A H φ f (c + d) g
      = stinespringPhi A H φ f c g + stinespringPhi A H φ f d g := by
  have term : ∀ (a : A) (x : H) (b : A) (y : H),
      ⟪x, φ (star a * ((c + d) * b)) y⟫_ℂ
        = ⟪x, φ (star a * (c * b)) y⟫_ℂ + ⟪x, φ (star a * (d * b)) y⟫_ℂ := by
    intro a x b y
    have harg : star a * ((c + d) * b) = star a * (c * b) + star a * (d * b) := by
      rw [add_mul, mul_add]
    rw [harg, map_add _ _ _, add_apply, inner_add_right]
  simp only [stinespringPhi]
  rw [← Finsupp.sum_add]
  refine Finsupp.sum_congr (fun a _ => ?_)
  rw [← Finsupp.sum_add]
  exact Finsupp.sum_congr (fun b _ => term a _ b _)

-- N6 (iii) Phi smul
theorem stinespringPhi_smul (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (f : StinespringPre A H φ) (r : ℂ) (c : A)
    (g : StinespringPre A H φ) :
    stinespringPhi A H φ f (r • c) g = r * stinespringPhi A H φ f c g := by
  have term : ∀ (a : A) (x : H) (b : A) (y : H),
      ⟪x, φ (star a * ((r • c) * b)) y⟫_ℂ = r * ⟪x, φ (star a * (c * b)) y⟫_ℂ := by
    intro a x b y
    have harg : star a * ((r • c) * b) = r • (star a * (c * b)) := by
      rw [smul_mul_assoc, mul_smul_comm]
    rw [harg, map_smul, smul_apply, inner_smul_right]
  simp only [stinespringPhi]
  rw [Finsupp.mul_sum]
  refine Finsupp.sum_congr (fun a _ => ?_)
  rw [Finsupp.mul_sum]
  exact Finsupp.sum_congr (fun b _ => term a _ b _)

-- N6 (iii) Phi one
theorem stinespringPhi_one (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (f g : StinespringPre A H φ) :
    stinespringPhi A H φ f 1 g = ⟪f, g⟫_ℂ := by
  have term : ∀ (a : A) (x : H) (b : A) (y : H),
      ⟪x, φ (star a * (1 * b)) y⟫_ℂ = ⟪x, φ (star a * b) y⟫_ℂ := by
    intro a x b y
    rw [one_mul]
  rw [stinespring_pre_inner_def]
  change stinespringPhi A H φ f 1 g = stinespringForm φ _ _
  simp only [stinespringPhi, stinespringForm]
  exact Finsupp.sum_congr (fun a _ => Finsupp.sum_congr (fun b _ => term a _ b _))

-- N6 (iv) adjoint
theorem stinespringLeftMul0_adj (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (c : A) (f g : StinespringPre A H φ) :
    ⟪stinespringLeftMul0 A H φ c f, g⟫_ℂ
      = ⟪f, stinespringLeftMul0 A H φ (star c) g⟫_ℂ := by
  have hop : ∀ a b : A, φ (star a * (c * b))
      = ContinuousLinearMap.adjoint (φ (star b * ((star c) * a))) := by
    intro a b
    rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star φ, star_mul, star_star, star_mul,
      star_star, mul_assoc]
  have term : ∀ (a : A) (x : H) (b : A) (y : H),
      (starRingEnd ℂ) ⟪x, φ (star a * (c * b)) y⟫_ℂ
        = ⟪y, φ (star b * ((star c) * a)) x⟫_ℂ := by
    intro a x b y
    rw [inner_conj_symm, hop a b, ContinuousLinearMap.adjoint_inner_left]
  have hswap : (starRingEnd ℂ) (stinespringPhi A H φ g c f)
      = stinespringPhi A H φ f (star c) g := by
    simp only [stinespringPhi, map_finsuppSum, term]
    exact (Finsupp.sum_comm _ _ _).symm
  rw [← inner_conj_symm, stinespringLeftMul0_inner, hswap,
    ← stinespringLeftMul0_inner]

-- N7 Phi neg / sub helpers
theorem stinespringPhi_neg (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (f : StinespringPre A H φ) (c : A)
    (g : StinespringPre A H φ) :
    stinespringPhi A H φ f (-c) g = -stinespringPhi A H φ f c g := by
  have hneg : (-1 : ℂ) • c = -c := by rw [neg_smul, one_smul]
  rw [← hneg, stinespringPhi_smul, neg_one_mul]

theorem stinespringPhi_sub (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (f : StinespringPre A H φ) (c d : A)
    (g : StinespringPre A H φ) :
    stinespringPhi A H φ f (c - d) g
      = stinespringPhi A H φ f c g - stinespringPhi A H φ f d g := by
  rw [sub_eq_add_neg, stinespringPhi_add, stinespringPhi_neg, sub_eq_add_neg]

theorem stinespringPhi_algebraMap (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (f : StinespringPre A H φ) (t : ℝ)
    (g : StinespringPre A H φ) :
    stinespringPhi A H φ f (algebraMap ℝ A t) g = (t : ℂ) * ⟪f, g⟫_ℂ := by
  rw [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul, stinespringPhi_smul,
    stinespringPhi_one]

-- N7 norm bound
theorem stinespringLeftMul0_bound (A H : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (c : A) (f : StinespringPre A H φ) :
    ‖stinespringLeftMul0 A H φ c f‖ ≤ ‖c‖ * ‖f‖ := by
  have hpos : ∀ d : A, 0 ≤ d →
      0 ≤ RCLike.re (stinespringPhi A H φ f d f) := by
    intro d hd
    obtain ⟨s, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hd
    rw [← stinespringLeftMul0_inner, stinespringLeftMul0_mul]
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [← stinespringLeftMul0_adj]
    exact inner_self_nonneg
  have hd : 0 ≤ algebraMap ℝ A (‖c‖ ^ 2) - star c * c :=
    sub_nonneg.mpr (CStarAlgebra.star_mul_le_algebraMap_norm_sq c)
  have hkey := hpos _ hd
  have hexpand : stinespringPhi A H φ f (algebraMap ℝ A (‖c‖ ^ 2) - star c * c) f
      = ((‖c‖ ^ 2 : ℝ) : ℂ) * ⟪f, f⟫_ℂ
        - ⟪stinespringLeftMul0 A H φ c f, stinespringLeftMul0 A H φ c f⟫_ℂ := by
    rw [stinespringPhi_sub, stinespringPhi_algebraMap]
    congr 1
    rw [← stinespringLeftMul0_inner, stinespringLeftMul0_mul]
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [← stinespringLeftMul0_adj]
  rw [hexpand, RCLike.re_to_complex, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at hkey
  simp only [← RCLike.re_to_complex] at hkey
  rw [← norm_sq_eq_re_inner (𝕜 := ℂ) f,
    ← norm_sq_eq_re_inner (𝕜 := ℂ) (stinespringLeftMul0 A H φ c f)] at hkey
  have hsq : ‖stinespringLeftMul0 A H φ c f‖ ^ 2 ≤ (‖c‖ * ‖f‖) ^ 2 := by
    rw [mul_pow]
    linarith [hkey]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp hsq

end MetaMathlibExt.Stinespring
end
