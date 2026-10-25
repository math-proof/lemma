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
import Def.StatisticalMechanics.Code.FrontierD.SixVertex
open Finset Matrix


namespace StatMech.FrontierD

abbrev SixVertexConfiguration (T : EvenTorus) :=
  {ω : SixVertexArrows T // ω.IceRule}


abbrev SixVertexRow (N : ℕ) := Fin N → Bool


end StatMech.FrontierD
