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
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertex.Part3
open Finset Matrix


namespace StatMech.FrontierD

def sixVertexSectorRow {N n : ℕ} (x : SixVertexSector N n) : SixVertexRow N :=
  fun i => decide (i ∈ (x : Finset (Fin N)))

end StatMech.FrontierD
