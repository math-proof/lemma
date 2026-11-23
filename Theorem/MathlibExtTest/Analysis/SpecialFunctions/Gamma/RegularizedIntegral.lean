/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/SpecialFunctions/Gamma/RegularizedIntegral.lean -/
module

public import Theorem.Analysis.SpecialFunctions.Gamma.RegularizedIntegral
public import Theorem.Real.RegularizedIntegral
open MeasureTheory Set

public section

example :
    (Real.eulerMascheroniConstant : ℂ) =
      (∫ t : ℝ in 0..1, (((1 - Real.exp (-t)) / t : ℝ) : ℂ)) -
        ∫ t : ℝ in Ioi 1, ((Real.exp (-t) / t : ℝ) : ℂ) :=
  Real.eulerMascheroniConstant_eq_regularized_integrals

