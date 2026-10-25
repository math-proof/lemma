/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CornerCount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.WindingAssembly.Part2


namespace StatMech.Onsager.CornerCount

open StatMech.Onsager.WindingAssembly

open StatMech.Onsager.SplitConstruction


def bigSquare : List Pt := [(0, 0), (2, 0), (2, 2), (0, 2)]

end StatMech.Onsager.CornerCount
