/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Gamma/RegularizedIntegral.lean -/

import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# A regularized-integral formula for the Euler-Mascheroni constant

This file expresses the Euler-Mascheroni constant as the difference of two convergent
integrals obtained by splitting and regularizing the logarithmic Gamma integral at one.
-/

open Filter Set Topology MeasureTheory Asymptotics Real

noncomputable section

namespace Real
end Real
