/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardAdaptiveIdealHomotopy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveIdealSimple.Part2


namespace StatMech.FrontierA

open Set

noncomputable def KWAdaptivePatchedData.idealAxisHomotopyVertex
    {n M : ℕ} [NeZero n] [NeZero M]
    {polygon : KWFiniteSimplePolygon n}
    (patch : KWAdaptivePatchedData (M := M) polygon)
    (t : ℝ) (j : Fin (n * (2 * (M + 1)))) : ℂ :=
  AffineMap.lineMap (patch.idealVertex j) (patch.vertex j) t

end StatMech.FrontierA
