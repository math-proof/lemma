/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAxisStaircase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearSeparation.Part2


namespace StatMech.FrontierA

open scoped Convex NNReal

open Set


def kwHorizontalPart (z : ℂ) : ℂ := z.re

def kwVerticalPart (z : ℂ) : ℂ := z.im * Complex.I

end StatMech.FrontierA
