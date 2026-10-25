/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CornerCount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.WindingAssembly.Part2
import Theorem.StatisticalMechanics.Code.Onsager.CornerCount.Part2


namespace StatMech.Onsager.CornerCount

open StatMech.Onsager.WindingAssembly

open StatMech.Onsager.SplitConstruction


def stepList (V : List Pt) : List Pt :=
  List.zipWith (fun p q : Pt => ((q.1 - p.1 : ℤ), (q.2 - p.2 : ℤ))) V (V.rotate 1)


end StatMech.Onsager.CornerCount
