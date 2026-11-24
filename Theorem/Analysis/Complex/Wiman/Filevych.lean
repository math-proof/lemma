module
public import Theorem.Complex.Wiman.CorrectedEstimateAbsorption
public import Theorem.Measure.Lebesgue.Finite
public import Theorem.Complex.Wiman.MaximumTermTendsToInfinity
public import Theorem.Analysis.Complex.Wiman.CorrectedMajorantBoundOffExceptionalSet
public import Theorem.Complex.Wiman.CorrectedMajorantBoundOffExceptionalSet
public import Theorem.Complex.Wiman.MaximumModulusLeMajorant
public import Theorem.Complex.Wiman.MaximumTermLeModulus
public import Theorem.Analysis.Complex.Wiman.MaximumModulusLeMajorant
public import Theorem.Analysis.Complex.Wiman.MaximumTermLeModulus


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/Filevych.lean -/
/-!
# An unbounded-radius Wiman corollary

This file proves a strict corollary of the classical theorem quoted in
P. Filevych, *The Baire categories and Wiman's inequality for entire functions*,
Matematychni Studii 20(2) (2003), 215–221, DOI: 10.30970/ms.20.2.215-221.

The cited theorem applies to every entire function and every exponent greater
than `1 / 2`, and states that the exceptional radii have finite logarithmic
measure. The result below instead assumes transcendence, fixes the exponent to
`2 / 3`, and concludes only that suitable radii are unbounded.
-/
noncomputable section
end
namespace Complex

open Filter MeasureTheory Set

end Complex
