/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAxisStaircase.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearSeparation.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAxisStaircase


namespace StatMech.FrontierA

open scoped Convex NNReal

open Set


noncomputable def kwStairBase (a b : ℂ) (N : ℕ) (k : Fin (N + 2)) : ℂ :=
  AffineMap.lineMap a b (k.val / (N + 1 : ℝ))


noncomputable def kwStairCorner (a b : ℂ) (N : ℕ) (k : Fin (N + 1)) : ℂ :=
  kwStairBase a b N k.castSucc +
    (N + 1 : ℝ)⁻¹ * kwHorizontalPart (b - a)

end StatMech.FrontierA
