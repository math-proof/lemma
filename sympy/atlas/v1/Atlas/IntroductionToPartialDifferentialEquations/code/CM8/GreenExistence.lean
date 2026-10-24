/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM8/GreenExistence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM8.RepresentationFormulas
import Lemma.Real.Atlas.v1.IntroductionToPartialDifferentialEquations.code.CM8.RepresentationFormulas

open Real Set MeasureTheory Classical

noncomputable section

namespace CM8

/-- Theorem 2.1 (basic existence and uniqueness for the Dirichlet problem):
on a bounded Lipschitz domain $\Omega \subset \mathbb{R}^n$ ($n \geq 2$) with
continuous boundary data $g \in C(\partial \Omega)$, the Poisson problem
$\Delta u = f$ in $\Omega$ with $u = g$ on $\partial \Omega$ has a unique solution
$u \in C^2(\Omega) \cap C(\overline{\Omega})$. -/
end CM8
