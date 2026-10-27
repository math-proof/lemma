import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Def.Analysis.SpecialFunctions.ArcsinCentralBinomialReciprocal.Part2


namespace MetaMathlibExt

theorem choose_pos' (n : ℕ) : (0:ℝ) < (Nat.choose (2*n) n : ℝ) := by
  have h : 0 < Nat.choose (2*n) n := Nat.choose_pos (by omega)
  exact_mod_cast h

theorem choose_ne' (n : ℕ) : (Nat.choose (2*n) n : ℝ) ≠ 0 :=
  ne_of_gt (choose_pos' n)

theorem Aterm_zero (x : ℝ) : Aterm x 0 = 0 := by
  simp [Aterm]

theorem choose_rec (n : ℕ) :
    (Nat.choose (2*(n+1)) (n+1) : ℝ) * ((n:ℝ)+1)
      = (Nat.choose (2*n) n : ℝ)*(2*(2*(n:ℝ)+1)) := by
  have h1 := Nat.choose_mul_factorial_mul_factorial (show n+1 ≤ 2*(n+1) by omega)
  have h2 := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2*n by omega)
  have e1 : 2*(n+1) - (n+1) = n+1 := by omega
  have e2 : 2*n - n = n := by omega
  rw [e1] at h1; rw [e2] at h2
  have f1 : (((n+1).factorial:ℕ):ℝ) = ((n:ℝ)+1)*(((n.factorial):ℕ):ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have f2 : (((2*(n+1)).factorial : ℕ):ℝ) = (2*(n:ℝ)+2)*((((2*n+1).factorial) : ℕ):ℝ) := by
    have e : 2*(n+1) = (2*n+1)+1 := by omega
    rw [e, Nat.factorial_succ]; push_cast; ring
  have f3 : ((((2*n+1).factorial) : ℕ):ℝ) = (2*(n:ℝ)+1)*((((2*n).factorial):ℕ):ℝ) := by
    have e : 2*n+1 = (2*n)+1 := by omega
    rw [e, Nat.factorial_succ]; push_cast; ring
  have h1r : (Nat.choose (2*(n+1)) (n+1) : ℝ) * (((n:ℝ)+1) * ((n.factorial:ℕ):ℝ))
        * (((n:ℝ)+1) * ((n.factorial:ℕ):ℝ))
      = (2*(n:ℝ)+2) * ((2*(n:ℝ)+1) * ((Nat.choose (2*n) n : ℝ)
        * ((n.factorial:ℕ):ℝ) * ((n.factorial:ℕ):ℝ))) := by
    have h1r0 : (Nat.choose (2*(n+1)) (n+1) : ℝ) * (((n+1).factorial:ℕ):ℝ)
          * (((n+1).factorial:ℕ):ℝ) = (((2*(n+1)).factorial:ℕ):ℝ) := by
      exact_mod_cast h1
    have h2r0 : (Nat.choose (2*n) n : ℝ) * (((n.factorial):ℕ):ℝ) * (((n.factorial):ℕ):ℝ)
        = ((((2*n).factorial):ℕ):ℝ) := by exact_mod_cast h2
    rw [f1, f2, f3, ← h2r0] at h1r0
    linear_combination h1r0
  have hFn : (((n.factorial : ℕ)):ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hF2 : ((((n.factorial : ℕ)):ℝ))^2 ≠ 0 := pow_ne_zero 2 hFn
  have key : (Nat.choose (2*(n+1)) (n+1) : ℝ) * ((n:ℝ)+1)^2
      = (Nat.choose (2*n) n : ℝ) * (2*((n:ℝ)+1)*(2*(n:ℝ)+1)) := by
    have step : (Nat.choose (2*(n+1)) (n+1) : ℝ) * ((n:ℝ)+1)^2
          * ((((n.factorial : ℕ)):ℝ))^2
        = (Nat.choose (2*n) n : ℝ) * (2*((n:ℝ)+1)*(2*(n:ℝ)+1))
          * ((((n.factorial : ℕ)):ℝ))^2 := by
      linear_combination h1r
    exact mul_right_cancel₀ hF2 step
  have hNe : ((n:ℝ)+1) ≠ 0 := by positivity
  have hcancel : (Nat.choose (2*(n+1)) (n+1) : ℝ) * ((n:ℝ)+1) * ((n:ℝ)+1)
      = ((Nat.choose (2*n) n : ℝ) * (2*(2*(n:ℝ)+1))) * ((n:ℝ)+1) := by
    linear_combination key
  exact mul_right_cancel₀ hNe hcancel

theorem four_pow_le (n : ℕ) (hn : 1 ≤ n) :
    (4^n : ℝ) ≤ 2*(n:ℝ)*(Nat.choose (2*n) n : ℝ) := by
  induction n, hn using Nat.le_induction with
  | base =>
    have hC21 : Nat.choose (2*1) 1 = 2 := by decide
    norm_num [hC21]
  | succ n hn ih =>
    have hr := choose_rec n
    have hC : (0:ℝ) ≤ (Nat.choose (2*n) n : ℝ) := le_of_lt (choose_pos' n)
    have e : (4^(n+1) : ℝ) = 4*4^n := by rw [pow_succ]; ring
    rw [e]
    push_cast
    calc (4:ℝ)*4^n ≤ 4*(2*(n:ℝ)*(Nat.choose (2*n) n : ℝ)) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = 8*(n:ℝ)*(Nat.choose (2*n) n : ℝ) := by ring
      _ ≤ 2*((n:ℝ)+1)*(Nat.choose (2*(n+1)) (n+1) : ℝ) := by
          have h2 : ((n:ℝ)+1)*(Nat.choose (2*(n+1)) (n+1) : ℝ)
                - 4*(n:ℝ)*(Nat.choose (2*n) n : ℝ)
              = 2*(Nat.choose (2*n) n : ℝ) := by
            linear_combination hr
          have h3 : (0:ℝ) ≤ 2*((n:ℝ)+1)*(Nat.choose (2*(n+1)) (n+1) : ℝ)
              - 8*(n:ℝ)*(Nat.choose (2*n) n : ℝ) := by
            have hexpand : 2*((n:ℝ)+1)*(Nat.choose (2*(n+1)) (n+1) : ℝ)
                - 8*(n:ℝ)*(Nat.choose (2*n) n : ℝ)
                = 2*((((n:ℝ)+1)*(Nat.choose (2*(n+1)) (n+1) : ℝ)
                  - 4*(n:ℝ)*(Nat.choose (2*n) n : ℝ))) := by ring
            rw [hexpand, h2]
            exact mul_nonneg (by norm_num) (mul_nonneg (by norm_num) hC)
          linarith

theorem ratio_le (n : ℕ) (hn : 1 ≤ n) :
    (4^n : ℝ)/((n:ℝ)*(Nat.choose (2*n) n : ℝ)) ≤ 2 := by
  have hpos : (0:ℝ) < (n:ℝ)*(Nat.choose (2*n) n : ℝ) := by
    apply mul_pos _ (choose_pos' n)
    exact_mod_cast (by omega : 0 < n)
  rw [div_le_iff₀ hpos]
  linear_combination (four_pow_le n hn)

theorem summable_succ_mul_geom (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun n : ℕ => ((n:ℝ)+1)*q^n) := by
  have h1 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := q) (by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]; exact hq1)
  have h2 := summable_geometric_of_lt_one hq0 hq1
  have e : (fun n : ℕ => ((n:ℝ)+1)*q^n)
      = (fun n : ℕ => ((n:ℝ)^1*q^n + q^n)) := by
    funext n; ring
  rw [e]
  exact h1.add h2

theorem summable_Aterm (x : ℝ) (hx : |x| < 1) : Summable (Aterm x) := by
  have hx2 : x^2 < 1 := by
    nlinarith [hx, abs_nonneg x, sq_abs x]
  have hgeom := summable_geometric_of_lt_one (sq_nonneg x) hx2
  have hbound := (hgeom.mul_left 2)
  apply Summable.of_norm_bounded hbound
  intro n
  by_cases hn : n = 0
  · subst hn
    rw [Aterm_zero]
    simp
  · have hC : (0:ℝ) < (Nat.choose (2*n) n : ℝ) := choose_pos' n
    have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hratio := ratio_le n (by omega)
    have hnorm : ‖Aterm x n‖ = ((4^n:ℝ)/((n:ℝ)*(Nat.choose (2*n) n : ℝ)))*(x^2)^n := by
      simp only [Aterm, Real.norm_eq_abs, abs_div]
      rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ)*(Nat.choose (2*n) n : ℝ))]
      have habs : |(2*x)^(2*n)| = (4^n:ℝ)*(x^2)^n := by
        rw [abs_pow]
        have : |2*x|^(2*n) = (|2*x|^2)^n := by rw [← pow_mul]
        rw [this]
        have h2x : |2*x|^2 = 4*x^2 := by
          rw [sq_abs]; ring
        rw [h2x, mul_pow]
      rw [habs]
      ring
    rw [hnorm]
    calc ((4^n:ℝ)/((n:ℝ)*(Nat.choose (2*n) n : ℝ)))*(x^2)^n
        ≤ 2*(x^2)^n := by
          apply mul_le_mul_of_nonneg_right hratio (pow_nonneg (sq_nonneg x) n)
      _ = 2*((x^2)^n) := by ring

end MetaMathlibExt
