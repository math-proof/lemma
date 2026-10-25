/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Fintype.Fin
import Mathlib.Order.Hom.PowersetCard
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertex.Part2
open Finset Matrix


namespace StatMech.FrontierD

def sixVertexUpCount {N : ℕ} (x : SixVertexRow N) : ℕ :=
  #{i | x i}


def sixVertexUpPositions {N : ℕ} (x : SixVertexRow N) : List (Fin N) :=
  ({i | x i} : Finset (Fin N)).sort (· ≤ ·)

end StatMech.FrontierD
