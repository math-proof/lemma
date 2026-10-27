/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Asymptotics/MonotoneIntegralCriterion.lean -/


import Theorem.Analysis.Asymptotics.MonotoneIntegralCriterion
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

