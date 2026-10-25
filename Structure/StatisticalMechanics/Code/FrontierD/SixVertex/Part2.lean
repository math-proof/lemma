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
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertex
open Finset Matrix


namespace StatMech.FrontierD

@[ext]
structure SixVertexArrows (T : EvenTorus) where
  horizontal : T.Vertex → Bool
  vertical : T.Vertex → Bool
deriving DecidableEq, Fintype

end StatMech.FrontierD
