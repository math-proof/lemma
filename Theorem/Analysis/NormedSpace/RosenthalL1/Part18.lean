/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Nth
import Def.Analysis.NormedSpace.RosenthalL1.Part17
/-!
# Rosenthal's `ℓ¹` theorem

This file proves that every bounded sequence in a real or complex Banach space has either a weakly
Cauchy subsequence or a subsequence with a uniform `ℓ¹` lower bound.
-/


namespace FunctionalAnalysis.RosenthalL1Wanted

theorem rosenthal_dualEval_continuous
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (x : ℕ → E) (n : ℕ) : Continuous (rosenthalDualEval (𝕜 := 𝕜) x n) :=
  (WeakDual.eval_continuous (x n)).comp continuous_subtype_val

theorem rosenthal_dualEval_eq_strong
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (x : ℕ → E) (n : ℕ) (g : RosenthalDualBall 𝕜 E) :
    rosenthalDualEval (𝕜 := 𝕜) x n g =
      rosenthalDualBallStrong (𝕜 := 𝕜) g (x n) := by
  exact (WeakDual.toStrongDual_apply g.1 (x n)).symm

theorem rosenthal_dual_sum_error
    {𝕜 E : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (y : ℕ → E) (u v : 𝕜) (delta : ℝ)
    (a : ℕ →₀ 𝕜) (P : Finset ℕ) (hP : P ⊆ a.support)
    (g h : RosenthalDualBall 𝕜 E)
    (hgu : ∀ i ∈ a.support \ P,
      dist (rosenthalDualEval (𝕜 := 𝕜) y i g) u ≤ delta)
    (hgv : ∀ i ∈ P,
      dist (rosenthalDualEval (𝕜 := 𝕜) y i g) v ≤ delta)
    (hhu : ∀ i ∈ a.support,
      dist (rosenthalDualEval (𝕜 := 𝕜) y i h) u ≤ delta) :
    ‖rosenthalDualBallStrong g (∑ i ∈ a.support, a i • y i) -
        rosenthalDualBallStrong h (∑ i ∈ a.support, a i • y i) -
          ∑ i ∈ P, a i * (v - u)‖ ≤
      2 * delta * ∑ i ∈ a.support, ‖a i‖ := by
  classical
  let F := rosenthalDualBallStrong g
  let G := rosenthalDualBallStrong h
  let target : ℕ → 𝕜 := fun i => if i ∈ P then v - u else 0
  have herr : ∀ i ∈ a.support,
      ‖(F (y i) - G (y i)) - target i‖ ≤ 2 * delta := by
    intro i hi
    by_cases hiP : i ∈ P
    · have hFv : ‖F (y i) - v‖ ≤ delta := by
        simpa [F, dist_eq_norm, rosenthal_dualEval_eq_strong] using hgv i hiP
      have hGu : ‖G (y i) - u‖ ≤ delta := by
        simpa [G, dist_eq_norm, rosenthal_dualEval_eq_strong] using hhu i hi
      rw [show target i = v - u by simp [target, hiP]]
      rw [show (F (y i) - G (y i)) - (v - u) =
          (F (y i) - v) - (G (y i) - u) by ring]
      exact (norm_sub_le _ _).trans (by linarith)
    · have hiDiff : i ∈ a.support \ P := Finset.mem_sdiff.mpr ⟨hi, hiP⟩
      have hFu : ‖F (y i) - u‖ ≤ delta := by
        simpa [F, dist_eq_norm, rosenthal_dualEval_eq_strong] using hgu i hiDiff
      have hGu : ‖G (y i) - u‖ ≤ delta := by
        simpa [G, dist_eq_norm, rosenthal_dualEval_eq_strong] using hhu i hi
      rw [show target i = 0 by simp [target, hiP], sub_zero]
      rw [show F (y i) - G (y i) = (F (y i) - u) - (G (y i) - u) by ring]
      exact (norm_sub_le _ _).trans (by linarith)
  have hsum : ‖∑ i ∈ a.support,
      a i * ((F (y i) - G (y i)) - target i)‖ ≤
      2 * delta * ∑ i ∈ a.support, ‖a i‖ := by
    calc
      ‖∑ i ∈ a.support, a i * ((F (y i) - G (y i)) - target i)‖ ≤
          ∑ i ∈ a.support, ‖a i * ((F (y i) - G (y i)) - target i)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ i ∈ a.support, ‖a i‖ * (2 * delta) := by
        exact Finset.sum_le_sum fun i hi => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (herr i hi) (norm_nonneg _)
      _ = 2 * delta * ∑ i ∈ a.support, ‖a i‖ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
  have htarget : (∑ i ∈ a.support, a i * target i) =
      ∑ i ∈ P, a i * (v - u) := by
    calc
      (∑ i ∈ a.support, a i * target i) = ∑ i ∈ P, a i * target i := by
        symm
        exact Finset.sum_subset hP fun i hi hiP => by simp [target, hiP]
      _ = ∑ i ∈ P, a i * (v - u) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [target, hi]
  have heq :
      F (∑ i ∈ a.support, a i • y i) -
          G (∑ i ∈ a.support, a i • y i) -
            ∑ i ∈ P, a i * (v - u) =
        ∑ i ∈ a.support, a i * ((F (y i) - G (y i)) - target i) := by
    rw [map_sum, map_sum]
    simp_rw [map_smul, smul_eq_mul]
    rw [← Finset.sum_sub_distrib, ← htarget, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  change ‖F (∑ i ∈ a.support, a i • y i) -
      G (∑ i ∈ a.support, a i • y i) -
        ∑ i ∈ P, a i * (v - u)‖ ≤ _
  rw [heq]
  exact hsum

end FunctionalAnalysis.RosenthalL1Wanted
