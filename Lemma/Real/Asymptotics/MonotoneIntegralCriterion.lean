import Mathlib
import sympy.Basic
import sympy.Analysis.Asymptotics.MonotoneIntegralCriterion

open Asymptotics Filter MeasureTheory Set Topology

/--
[isEquivalent_id_of_monotoneOn_of_tendsto_integral_sub_div_sq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Asymptotics/MonotoneIntegralCriterion.lean)
-/
@[path]
private lemma isEquivalent_id_of_monotoneOn_of_tendsto_integral_sub_div_sq_eq
-- given
  (f : ℝ → ℝ)
  (hf : MonotoneOn f (Ici 1))
  (hconv : ∃ L : ℝ,
    Tendsto (fun x => ∫ t in Ioc 1 x, (f t - t) / t ^ 2)
      atTop (𝓝 L)) :
-- imply
  f ~[atTop] (fun x : ℝ => x) :=
-- proof
  Asymptotics.isEquivalent_id_of_monotoneOn_of_tendsto_integral_sub_div_sq f hf hconv


-- created on 2026-10-09
