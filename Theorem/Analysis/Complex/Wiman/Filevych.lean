/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/Wiman/Filevych.lean -/

import Lemma.Complex.Wiman.CorrectedEstimateAbsorption
import Lemma.Measure.Lebesgue.Finite
import Lemma.Complex.Wiman.MaximumTermTendsToInfinity
import Theorem.Analysis.Complex.Wiman.CorrectedMajorantBoundOffExceptionalSet
import Lemma.Complex.Wiman.CorrectedMajorantBoundOffExceptionalSet
import Lemma.Complex.Wiman.MaximumModulusLeMajorant
import Lemma.Complex.Wiman.MaximumTermLeModulus
import Theorem.Analysis.Complex.Wiman.MaximumModulusLeMajorant
import Theorem.Analysis.Complex.Wiman.MaximumTermLeModulus
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
