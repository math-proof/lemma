/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.SetTheory.Cardinal.Free
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Pi.Irrational
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.MetricSpace.IsometricSMul
import Def.MeasureTheory.Geometry.BanachTarski.Part13


namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/-- Iterates of `btSigma` rotate about `btC` by multiples of the angle. -/
theorem btSigma_iterate (n : ℕ) (x : btE) :
    (⇑btSigma)^[n] x =
      btC + btIsoOfUnitary (btRotZ ((n : ℝ) * 1)) (x + (-btC)) := by
  induction n with
  | zero =>
    rw [Function.iterate_zero_apply]
    simp only [Nat.cast_zero, zero_mul, btRotZ_zero, btIsoOfUnitary_one]
    abel
  | succ n ih =>
    rw [show n + 1 = n.succ from rfl, Function.iterate_succ_apply', ih,
      btSigma_apply]
    have hcan : btC + btIsoOfUnitary (btRotZ ((n : ℝ) * 1)) (x + -btC) + -btC =
        btIsoOfUnitary (btRotZ ((n : ℝ) * 1)) (x + -btC) := by abel
    rw [hcan]
    have hcast : ((n + 1 : ℕ) : ℝ) * 1 = 1 + (n : ℝ) * 1 := by push_cast; ring
    rw [hcast, btRotZ_add, btIsoOfUnitary_mul]

/-- The ball is congruent to the punctured ball. -/
theorem btCongr_ball_punctured :
    btCongr (Metric.closedBall (0 : btE) 1) (Metric.closedBall (0 : btE) 1 \ {0}) := by
  have hnorm : ∀ n : ℕ, ‖(⇑btSigma)^[n] 0‖ ≤ 1 := by
    intro n
    rw [btSigma_iterate]
    calc ‖btC + btIsoOfUnitary (btRotZ ((n : ℝ) * 1)) (0 + -btC)‖
        ≤ ‖btC‖ + ‖btIsoOfUnitary (btRotZ ((n : ℝ) * 1)) (0 + -btC)‖ :=
          norm_add_le _ _
      _ = 1 := by
          rw [btC_norm, btIsoOfUnitary_norm, zero_add, norm_neg, btC_norm]
          norm_num
  have hY : ∀ n : ℕ, (⇑btSigma)^[n] '' ({0} : Set btE) ⊆
      Metric.closedBall (0 : btE) 1 := by
    intro n
    rw [Set.image_singleton, Set.singleton_subset_iff,
      Metric.mem_closedBall, dist_zero_right]
    exact hnorm n
  have hne : ∀ n : ℕ, 1 ≤ n → (⇑btSigma)^[n] 0 ≠ 0 := by
    intro n hn hcon
    have hsum : btC + btIsoOfUnitary (btRotZ ((n : ℝ) * 1)) (0 + -btC) = 0 :=
      (btSigma_iterate n 0).symm.trans hcon
    have hfixpt : btIsoOfUnitary (btRotZ ((n : ℝ) * 1)) (0 + -btC) = -btC :=
      eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact hsum)
    have hMfix : Matrix.mulVec (btRotZ ((n : ℝ) * 1) : Matrix (Fin 3) (Fin 3) ℝ)
        (-(WithLp.ofLp btC)) = -(WithLp.ofLp btC) := by
      have e := congrArg WithLp.ofLp hfixpt
      rw [btIsoOfUnitary_apply, btOfLp_add, btOfLp_zero, btOfLp_neg] at e
      rw [zero_add] at e
      exact e
    have hcos : Real.cos ((n : ℝ) * 1) = 1 := by
      apply btRotZ_fix_cos _ _ hMfix
      intro hcon2
      have hfst := congrArg Prod.fst hcon2
      simp only [Pi.neg_apply, btC_coord0] at hfst
      norm_num at hfst
    obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff _).mp hcos
    have hn0 : n ≠ 0 := by omega
    have hnR : ((n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hn0
    have hk0 : k ≠ 0 := by
      rintro rfl
      simp only [Int.cast_zero, zero_mul] at hk
      rw [mul_one] at hk
      exact hnR hk.symm
    have hpi : Real.pi = ((n : ℕ) : ℝ) / (2 * ((k : ℤ) : ℝ)) := by
      have hkR : ((k : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hk0
      rw [eq_div_iff (mul_ne_zero two_ne_zero hkR)]
      have hring : ((k : ℤ) : ℝ) * (2 * Real.pi) = (2 * ((k : ℤ) : ℝ)) * Real.pi :=
        by ring
      rw [hring, mul_one] at hk
      rw [mul_comm]
      exact hk
    have hpi' : Real.pi = ((((n : ℚ) / (2 * (k : ℚ)))) : ℚ) := by
      exact_mod_cast hpi
    exact irrational_pi.ne_rat _ hpi'
  have hdisj : ∀ n : ℕ, 1 ≤ n → Disjoint ((⇑btSigma)^[n] '' ({0} : Set btE)) {0} := by
    intro n hn
    rw [Set.disjoint_left]
    intro a ha ha0
    obtain ⟨z, hz, rfl⟩ := ha
    simp only [Set.mem_singleton_iff] at hz
    subst hz
    exact hne n hn ha0
  exact btCongr_absorb btSigma hY hdisj

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted
