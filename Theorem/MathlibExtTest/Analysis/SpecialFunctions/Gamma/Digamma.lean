/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/SpecialFunctions/Gamma/Digamma.lean -/


import Def.Analysis.SpecialFunctions.Gamma.Digamma
import Lemma.Complex.Digamma
import Lemma.Real.Digamma


example (x : ℝ) (hx : 0 < x) :
    HasSum (fun j : ℕ => 1 / ((j : ℝ) + 1) - 1 / (x + (j : ℝ) + 1))
      (deriv (fun t => Real.log (Real.Gamma t)) (x + 1) + Real.eulerMascheroniConstant) :=
  Real.hasSum_digamma_series x hx

example (y : ℝ) (hy : 0 < y) :
    deriv (deriv fun t => Real.log (Real.Gamma t)) (y + 1) =
      ∑' j : ℕ, 1 / (y + (j : ℝ) + 1) ^ 2 :=
  Real.deriv_deriv_log_Gamma_add_one y hy

example (w : ℂ) (hw : ∀ m : ℕ, w ≠ -(m : ℂ)) :
    AnalyticAt ℂ Complex.Gamma w ∧ AnalyticAt ℂ Complex.digamma w :=
  ⟨Complex.analyticAt_Gamma w hw, Complex.analyticAt_digamma w hw⟩

example (t : ℝ) (ht : 0 < t) : deriv Complex.Gamma (t : ℂ) = ((deriv Real.Gamma t : ℝ) : ℂ) :=
  Complex.deriv_Gamma_ofReal t ht

example (z : ℂ) :
    Summable fun k : ℕ => ‖(1 / (z + (k + 1 : ℕ)) ^ 2 : ℂ)‖ :=
  Complex.summable_norm_one_div_add_nat_succ_sq z

-- Pole case: at `z = -1` the `k = 0` term is `1 / 0 = 0` by totalized division.
example : Summable fun k : ℕ => ‖(1 / ((-1 : ℂ) + (k + 1 : ℕ)) ^ 2 : ℂ)‖ :=
  Complex.summable_norm_one_div_add_nat_succ_sq _

example : Summable (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 2) :=
  Real.summable_one_div_add_nat_succ_sq

example (s : ℂ) (hs : 1 < s.re) :
    HasSum (fun j : ℕ => Complex.digammaSeriesTerm j s)
      (Complex.digamma s + (Real.eulerMascheroniConstant : ℂ)) :=
  Complex.hasSum_digamma_series s hs

example (s : ℂ) (hs : 1 < s.re) :
    Summable (fun j : ℕ => Complex.digammaSeriesTerm j s) :=
  Complex.summable_digammaSeriesTerm s hs

