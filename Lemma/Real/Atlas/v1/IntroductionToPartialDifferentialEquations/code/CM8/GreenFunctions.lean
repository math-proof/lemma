import Mathlib
import Initialize.Tactic.Attr.Basic
import Structure.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM8.GreenFunctions.Part2
open Real Set Topology CM8
open Finset


namespace CM8

/--
[normSq_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM8/GreenFunctions.lean)
-/
@[path]
lemma normSq_pos
  {x : Fin 3 → ℝ}
-- given
  (hx : euclidNorm x ≠ 0) :
-- imply
  0 < normSq x := by
-- proof
  unfold normSq euclidNorm at *
  by_contra h; push Not at h
  exact hx (by rw [le_antisymm h (Finset.sum_nonneg (fun j _ => sq_nonneg (x j)))]; simp)

end CM8

namespace CM8

/--
[euclidNorm_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM8/GreenFunctions.lean)
-/
@[path]
lemma euclidNorm_pos
  {x : Fin 3 → ℝ}
-- given
  (hx : euclidNorm x ≠ 0) :
-- imply
  0 < euclidNorm x :=
-- proof
  lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hx)

end CM8

namespace CM8

/--
[continuous_euclidNorm3](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM8/GreenFunctions.lean)
-/
@[path]
lemma continuous_euclidNorm3
-- imply
  Continuous (euclidNorm : (Fin 3 → ℝ) → ℝ) := by
-- proof
  unfold euclidNorm
  exact Real.continuous_sqrt.comp (continuous_finset_sum _ fun j _ => (continuous_apply j).pow 2)

end CM8

namespace CM8

/--
[isOpen_euclidNorm_ne](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM8/GreenFunctions.lean)
-/
@[path]
lemma isOpen_euclidNorm_ne
-- imply
  IsOpen {y : Fin 3 → ℝ | euclidNorm y ≠ 0} :=
-- proof
  continuous_euclidNorm3.isOpen_preimage _ isOpen_ne

end CM8

namespace CM8

/--
[hasFDerivAt_normSq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM8/GreenFunctions.lean)
-/
@[path]
lemma hasFDerivAt_normSq
  {x : Fin 3 → ℝ} :
-- imply
  HasFDerivAt normSq (normSq_CLM x) x := by
-- proof
  unfold normSq
  rw [show (fun y : Fin 3 → ℝ => ∑ j : Fin 3, y j ^ 2) =
    ∑ j : Fin 3, (fun y : Fin 3 → ℝ => y j ^ 2) from by ext y; simp [Finset.sum_apply]]
  apply HasFDerivAt.sum; intro j _
  convert (hasFDerivAt_apply (𝕜 := ℝ) (ι := Fin 3) (F' := fun _ => ℝ) j x).pow 2 using 1
  simp [mul_comm]

end CM8

namespace CM8

/--
[normSq_CLM_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM8/GreenFunctions.lean)
-/
@[path]
lemma normSq_CLM_apply
  {x : Fin 3 → ℝ}
  {i : Fin 3} :
-- imply
  normSq_CLM x (Pi.single i 1) = 2 * x i := by
-- proof
  unfold normSq_CLM
  simp [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, Pi.single_apply, Finset.sum_ite_eq']

end CM8

namespace CM8

/--
[hasDerivAt_g](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM8/GreenFunctions.lean)
-/
@[path]
lemma hasDerivAt_g
  {s : ℝ}
-- given
  (hs : 0 < s) :
-- imply
  HasDerivAt (fun s => -1 / (4 * π * Real.sqrt s)) (1 / (8 * π * (Real.sqrt s) ^ 3)) s := by
-- proof
  have hsqrt_ne := ne_of_gt (Real.sqrt_pos.mpr hs)
  have h_h : HasDerivAt (fun r => -1 / (4 * π * r))
    ((-1/(4*π)) * (-(Real.sqrt s ^ 2)⁻¹)) (Real.sqrt s) := by
    convert (hasDerivAt_inv hsqrt_ne).const_mul (-1/(4*π)) using 1; ext r; ring
  convert h_h.comp s (Real.hasDerivAt_sqrt (ne_of_gt hs)) using 1
  field_simp; ring

end CM8

namespace CM8

/--
[hasFDerivAt_Phi3](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM8/GreenFunctions.lean)
-/
@[path]
lemma hasFDerivAt_Phi3
  {y : Fin 3 → ℝ}
-- given
  (hy : euclidNorm y ≠ 0) :
-- imply
  HasFDerivAt Phi3 ((1 / (8 * π * (euclidNorm y) ^ 3)) • normSq_CLM y) y := by
-- proof
  have h := (hasDerivAt_g (normSq y) (normSq_pos y hy)).comp_hasFDerivAt y (hasFDerivAt_normSq y)
  convert h using 1

end CM8

namespace CM8

/--
[fderiv_Phi3_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM8/GreenFunctions.lean)
-/
@[path]
lemma fderiv_Phi3_apply
  {y : Fin 3 → ℝ}
  {i : Fin 3}
-- given
  (hy : euclidNorm y ≠ 0) :
-- imply
  fderiv ℝ Phi3 y (Pi.single i 1) = y i / (4 * π * (euclidNorm y) ^ 3) := by
-- proof
  rw [(hasFDerivAt_Phi3 y hy).fderiv]
  simp [ContinuousLinearMap.smul_apply, normSq_CLM_apply]; ring

end CM8

namespace CM8

/--
[hasDerivAt_sqrt_cube](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM8/GreenFunctions.lean)
-/
@[path]
lemma hasDerivAt_sqrt_cube
  {s : ℝ}
-- given
  (hs : 0 < s) :
-- imply
  HasDerivAt (fun s => (Real.sqrt s) ^ 3) ((3 / 2) * Real.sqrt s) s := by
-- proof
  convert (Real.hasDerivAt_sqrt (ne_of_gt hs)).pow 3 using 1; simp; field_simp

end CM8

namespace CM8

/--
[hasDerivAt_inv_4pi_R3](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM8/GreenFunctions.lean)
-/
@[path]
lemma hasDerivAt_inv_4pi_R3
  {s : ℝ}
-- given
  (hs : 0 < s) :
-- imply
  HasDerivAt (fun s => (4 * π * (Real.sqrt s) ^ 3)⁻¹) (-(4 * π * ((3 / 2) * Real.sqrt s)) / (4 * π * (Real.sqrt s) ^ 3) ^ 2) s := by
-- proof
  have hdenom_ne : 4 * π * (Real.sqrt s) ^ 3 ≠ 0 := by positivity
  have h_R3 := hasDerivAt_sqrt_cube s hs
  have h_denom : HasDerivAt (fun s => 4 * π * (Real.sqrt s) ^ 3)
    (4 * π * ((3/2) * Real.sqrt s)) s := h_R3.const_mul _
  exact h_denom.inv hdenom_ne

end CM8

namespace CM8

/--
[hasFDerivAt_h](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM8/GreenFunctions.lean)
-/
@[path]
lemma hasFDerivAt_h
  {y : Fin 3 → ℝ}
-- given
  (hy : euclidNorm y ≠ 0) :
-- imply
  HasFDerivAt (fun y => (4 * π * (euclidNorm y) ^ 3)⁻¹) ((-(4 * π * ((3 / 2) * euclidNorm y)) / (4 * π * (euclidNorm y) ^ 3) ^ 2) • normSq_CLM y) y := by
-- proof
  have h := (hasDerivAt_inv_4pi_R3 (normSq y) (normSq_pos y hy)).comp_hasFDerivAt y (hasFDerivAt_normSq y)
  convert h using 1

end CM8

namespace CM8

/--
[differentiableAt_F](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM8/GreenFunctions.lean)
-/
@[path]
lemma differentiableAt_F
  {x : Fin 3 → ℝ}
  {i : Fin 3}
-- given
  (hx : euclidNorm x ≠ 0) :
-- imply
  DifferentiableAt ℝ (fun y => y i / (4 * π * (euclidNorm y) ^ 3)) x := by
-- proof
  have h1 : DifferentiableAt ℝ (fun y : Fin 3 → ℝ => y i) x :=
    (ContinuousLinearMap.proj (R := ℝ) (ι := Fin 3) (φ := fun _ => ℝ) i).differentiableAt
  have h2 : DifferentiableAt ℝ (fun y => (4 * π * (euclidNorm y) ^ 3)⁻¹) x :=
    (hasFDerivAt_h x hx).differentiableAt
  have : (fun y : Fin 3 → ℝ => y i / (4 * π * (euclidNorm y) ^ 3)) =
    (fun y => y i * (4 * π * (euclidNorm y) ^ 3)⁻¹) := by ext y; ring
  rw [this]; exact h1.mul h2

end CM8

namespace CM8

/--
[euclidNorm_update_sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM8/GreenFunctions.lean)
-/
@[path]
lemma euclidNorm_update_sq
  {x : Fin 3 → ℝ}
  {i : Fin 3}
  {t : ℝ} :
-- imply
  (∑ j : Fin 3, (Function.update x i t j) ^ 2) = t ^ 2 + restSq x i := by
-- proof
  unfold restSq
  fin_cases i <;> simp [Fin.sum_univ_three, Function.update_apply, Finset.sum_filter] <;> ring

end CM8

namespace CM8

/--
[hasDerivAt_phi_2d](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM8/GreenFunctions.lean)
-/
@[path]
lemma hasDerivAt_phi_2d
  {t C : ℝ}
-- given
  (hpos : 0 < t ^ 2 + C) :
-- imply
  HasDerivAt (fun t => t / (4 * π * (√(t ^ 2 + C)) ^ 3)) ((C - 2 * t ^ 2) / (4 * π * (√(t ^ 2 + C)) ^ 5)) t := by
-- proof
  have hR_pos : 0 < √(t ^ 2 + C) := Real.sqrt_pos.mpr hpos
  have hR_ne : √(t ^ 2 + C) ≠ 0 := ne_of_gt hR_pos
  have h4piR3_ne : 4 * π * √(t ^ 2 + C) ^ 3 ≠ 0 := by positivity
  have h_num : HasDerivAt (fun t : ℝ => t) 1 t := hasDerivAt_id t
  have h_sqrt : HasDerivAt (fun t => √(t ^ 2 + C)) (t / √(t ^ 2 + C)) t := by
    have h1 : HasDerivAt (fun t => t ^ 2 + C) (2 * t) t :=
      ((hasDerivAt_pow 2 t).add_const C).congr_deriv (by ring)
    exact (h1.sqrt (ne_of_gt hpos)).congr_deriv (by field_simp)
  have h_cube : HasDerivAt (fun t => (√(t ^ 2 + C)) ^ 3)
    (3 * (√(t ^ 2 + C)) ^ 2 * (t / √(t ^ 2 + C))) t := h_sqrt.pow 3
  have h_denom : HasDerivAt (fun t => 4 * π * (√(t ^ 2 + C)) ^ 3)
    (4 * π * (3 * √(t ^ 2 + C) ^ 2 * (t / √(t ^ 2 + C)))) t := h_cube.const_mul _
  convert h_num.div h_denom h4piR3_ne using 1
  have hR2 : √(t ^ 2 + C) ^ 2 = t ^ 2 + C := Real.sq_sqrt (le_of_lt hpos)
  field_simp; nlinarith [hR2, sq_nonneg t, sq_nonneg (√(t ^ 2 + C))]
set_option maxHeartbeats 800000 in

end CM8

namespace CM8

/--
[Phi3_harmonic_away](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM8/GreenFunctions.lean)
-/
@[path]
lemma Phi3_harmonic_away
  {x : Fin 3 → ℝ}
-- given
  (hx : euclidNorm x ≠ 0) :
-- imply
  laplacian Phi3 x = 0 := by
-- proof
  unfold laplacian
  have h_eq : ∀ i : Fin 3,
    fderiv ℝ (fun y => fderiv ℝ Phi3 y (Pi.single i 1)) x =
    fderiv ℝ (fun y => y i / (4 * π * (euclidNorm y) ^ 3)) x := by
    intro i; apply Filter.EventuallyEq.fderiv_eq
    exact Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨{y | euclidNorm y ≠ 0}, isOpen_euclidNorm_ne.mem_nhds hx,
        fun y hy => fderiv_Phi3_apply y hy i⟩
  simp_rw [h_eq]
  have h_bridge : ∀ i : Fin 3,
    fderiv ℝ (fun y => y i / (4 * π * (euclidNorm y) ^ 3)) x (Pi.single i 1) =
    deriv (fun t => (Function.update x i t) i /
      (4 * π * (euclidNorm (Function.update x i t)) ^ 3)) (x i) := by
    intro i
    have hf' : DifferentiableAt ℝ (fun y => y i / (4 * π * (euclidNorm y) ^ 3))
      (Function.update x i (x i)) := by
      rw [Function.update_eq_self]; exact differentiableAt_F x hx i
    have h_comp := hf'.hasFDerivAt.comp_hasDerivAt (x i) (hasDerivAt_update x i (x i))
    simp only [Function.comp_def] at h_comp
    rw [h_comp.deriv]; simp [Function.update_eq_self]
  simp_rw [h_bridge]
  have h_1d : ∀ i : Fin 3,
    (fun t => (Function.update x i t) i /
      (4 * π * (euclidNorm (Function.update x i t)) ^ 3)) =
    (fun t => t / (4 * π * (√(t ^ 2 + restSq x i)) ^ 3)) := by
    intro i; ext t; simp only [Function.update_self, euclidNorm, euclidNorm_update_sq]
  simp_rw [h_1d]
  have hR_pos : 0 < euclidNorm x := euclidNorm_pos x hx
  have hR_sq : euclidNorm x ^ 2 = ∑ j : Fin 3, x j ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg (fun j _ => sq_nonneg (x j)))
  have h_sum_split : ∀ i : Fin 3, x i ^ 2 + restSq x i = ∑ j : Fin 3, x j ^ 2 := by
    intro i; unfold restSq
    rw [← Finset.add_sum_erase Finset.univ (fun j => x j ^ 2) (Finset.mem_univ i)]
    congr 1; apply Finset.sum_congr _ (fun _ _ => rfl)
    ext j; simp [Finset.mem_erase, ne_comm]
  have hpos : ∀ i : Fin 3, 0 < x i ^ 2 + restSq x i := by
    intro i; rw [h_sum_split, ← hR_sq]; exact sq_pos_of_pos hR_pos
  have h_deriv : ∀ i : Fin 3,
    deriv (fun t => t / (4 * π * (√(t ^ 2 + restSq x i)) ^ 3)) (x i) =
    (restSq x i - 2 * (x i) ^ 2) / (4 * π * (√(x i ^ 2 + restSq x i)) ^ 5) :=
    fun i => (hasDerivAt_phi_2d (x i) (restSq x i) (hpos i)).deriv
  simp_rw [h_deriv]
  have h_norm : ∀ i : Fin 3, √(x i ^ 2 + restSq x i) = euclidNorm x := by
    intro i; unfold euclidNorm; congr 1; exact h_sum_split i
  simp_rw [h_norm]
  rw [show (∑ i : Fin 3, (restSq x i - 2 * x i ^ 2) / (4 * π * euclidNorm x ^ 5)) =
    (∑ i : Fin 3, (restSq x i - 2 * x i ^ 2)) / (4 * π * euclidNorm x ^ 5)
    from by rw [Finset.sum_div]]
  rw [div_eq_zero_iff]; left
  unfold restSq
  simp only [Fin.sum_univ_three, Finset.sum_filter]
  simp (config := { decide := true })
  ring

end CM8

namespace CM8

/--
[laplacian_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM8/GreenFunctions.lean)
-/
@[path]
lemma laplacian_sub
  {n : ℕ}
  {f g : (Fin n → ℝ) → ℝ}
  {x : Fin n → ℝ}
-- given
  (hf : ∀ y, DifferentiableAt ℝ f y)
  (hg : ∀ y, DifferentiableAt ℝ g y)
  (hf2 : ∀ i : Fin n, DifferentiableAt ℝ (fun y => fderiv ℝ f y (Pi.single i 1)) x)
  (hg2 : ∀ i : Fin n, DifferentiableAt ℝ (fun y => fderiv ℝ g y (Pi.single i 1)) x) :
-- imply
  laplacian (f - g) x = laplacian f x - laplacian g x := by
-- proof
  unfold laplacian
  rw [← Finset.sum_sub_distrib]
  congr 1; ext i
  have h_inner : (fun y => fderiv ℝ (f - g) y (Pi.single i 1)) =
    (fun y => fderiv ℝ f y (Pi.single i 1) - fderiv ℝ g y (Pi.single i 1)) := by
    ext y; rw [fderiv_sub (hf y) (hg y)]; simp [ContinuousLinearMap.sub_apply]
  rw [h_inner]
  have h_sub : fderiv ℝ (fun y => fderiv ℝ f y (Pi.single i 1) - fderiv ℝ g y (Pi.single i 1)) x =
    fderiv ℝ (fun y => fderiv ℝ f y (Pi.single i 1)) x -
    fderiv ℝ (fun y => fderiv ℝ g y (Pi.single i 1)) x := by
    have : (fun y => fderiv ℝ f y (Pi.single i 1) - fderiv ℝ g y (Pi.single i 1)) =
      (fun y => fderiv ℝ f y (Pi.single i 1)) - (fun y => fderiv ℝ g y (Pi.single i 1)) := by
      ext y; simp [Pi.sub_apply]
    rw [this]; exact fderiv_sub (hf2 i) (hg2 i)
  rw [h_sub]; simp [ContinuousLinearMap.sub_apply]

end CM8


-- created on 2026-10-23
