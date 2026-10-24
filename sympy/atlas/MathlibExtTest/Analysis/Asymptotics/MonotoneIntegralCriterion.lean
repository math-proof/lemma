/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Asymptotics/MonotoneIntegralCriterion.lean -/


import sympy.atlas.Analysis.Asymptotics.MonotoneIntegralCriterion
import Mathlib.NumberTheory.Chebyshev

open Filter MeasureTheory Set Topology Asymptotics

/-- Abstract signature: the criterion applies to any `MonotoneOn` function with
convergent normalized-deviation integral. -/
example (f : ℝ → ℝ) (hf : MonotoneOn f (Ici 1))
    (hconv : ∃ L : ℝ,
      Tendsto (fun x => ∫ t in Ioc 1 x, (f t - t) / t ^ 2) atTop (𝓝 L)) :
    f ~[atTop] (fun x : ℝ => x) :=
  Asymptotics.isEquivalent_id_of_monotoneOn_of_tendsto_integral_sub_div_sq f hf hconv

/-- The identity satisfies the criterion with limit `0`. -/
example : (fun x : ℝ => x) ~[atTop] (fun x : ℝ => x) := by
  refine Asymptotics.isEquivalent_id_of_monotoneOn_of_tendsto_integral_sub_div_sq _
    (monotone_id.monotoneOn _) ⟨0, ?_⟩
  have hfun : (fun x : ℝ => ∫ t in Ioc 1 x, (t - t) / t ^ 2) = fun _ => 0 :=
    funext fun x =>
      setIntegral_eq_zero_of_forall_eq_zero (fun t _ => by simp)
  rw [hfun]
  exact tendsto_const_nhds

/-- A function agreeing with the identity on `[1, ∞)` but not globally monotone:
negation below `1`. This witnesses why `MonotoneOn` is the right hypothesis. -/
private noncomputable def spikeBelowOne : ℝ → ℝ := fun x => if x < 1 then -x else x

example : spikeBelowOne = fun x => if x < 1 then -x else x := rfl

example : MonotoneOn spikeBelowOne (Ici 1) := by
  intro a ha b hb hab
  have ha1 : 1 ≤ a := mem_Ici.mp ha
  have hb1 : 1 ≤ b := mem_Ici.mp hb
  have ea : spikeBelowOne a = a := by
    change (if a < 1 then -a else a) = a
    rw [ite_eq_right (by linarith)]
  have eb : spikeBelowOne b = b := by
    change (if b < 1 then -b else b) = b
    rw [ite_eq_right (by linarith)]
  rw [ea, eb]
  exact hab

example : ¬ Monotone spikeBelowOne := by
  intro h
  have hle := h (show (-1 : ℝ) ≤ 0 by norm_num)
  have e1 : spikeBelowOne (-1) = 1 := by
    change (if (-1 : ℝ) < 1 then -(-1) else -1) = 1
    rw [ite_eq_left (show (-1 : ℝ) < 1 by norm_num), neg_neg]
  have e0 : spikeBelowOne 0 = 0 := by
    change (if (0 : ℝ) < 1 then -(0 : ℝ) else 0) = 0
    rw [ite_eq_left (show (0 : ℝ) < 1 by norm_num), neg_zero]
  rw [e1, e0] at hle
  norm_num at hle

/-- The criterion applies to `spikeBelowOne`: its integral is identically `0`
since the integrand vanishes on every `Ioc 1 x`. -/
example : spikeBelowOne ~[atTop] (fun x : ℝ => x) := by
  refine Asymptotics.isEquivalent_id_of_monotoneOn_of_tendsto_integral_sub_div_sq _
    ?_ ⟨0, ?_⟩
  · intro a ha b hb hab
    have ha1 : 1 ≤ a := mem_Ici.mp ha
    have hb1 : 1 ≤ b := mem_Ici.mp hb
    have ea : spikeBelowOne a = a := by
      change (if a < 1 then -a else a) = a
      rw [ite_eq_right (by linarith)]
    have eb : spikeBelowOne b = b := by
      change (if b < 1 then -b else b) = b
      rw [ite_eq_right (by linarith)]
    rw [ea, eb]
    exact hab
  · have hfun : (fun x : ℝ => ∫ t in Ioc 1 x, (spikeBelowOne t - t) / t ^ 2)
        = fun _ => 0 := by
      funext x
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro t ht
      have ht1 : 1 < t := ht.1
      have et : spikeBelowOne t = t := by
        change (if t < 1 then -t else t) = t
        rw [ite_eq_right (by linarith)]
      rw [et, sub_self, zero_div]
    rw [hfun]
    exact tendsto_const_nhds

/-- Chebyshev's `θ` satisfies the monotonicity hypothesis on `[1, ∞)`. -/
example : MonotoneOn Chebyshev.theta (Ici 1) := Chebyshev.theta_mono.monotoneOn _
