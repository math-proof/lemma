/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM3/FourierSeries.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM2.HeatEquationSetup
open MeasureTheory Real Filter Topology Set

noncomputable section

namespace FourierFacts

open HeatEquation

/-- Basic facts about the Fourier sine series on $[0, 1]$ (Theorem 4.1):
for $f \in L^2([0, 1])$, the Fourier sine partial sums converge to $f$ in $L^2$,
the Parseval identity $\|f\|_{L^2}^2 = \sum_m \tfrac{1}{2} A_m^2$ holds, and if $f$
is continuous on $[0, 1]$ then the convergence is uniform on any closed subinterval
$[a, b] \subset (0, 1)$. -/
end FourierFacts
