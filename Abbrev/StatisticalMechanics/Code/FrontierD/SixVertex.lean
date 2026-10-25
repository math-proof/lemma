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
import Structure.StatisticalMechanics.Code.FrontierD.SixVertex
open Finset Matrix


namespace StatMech.FrontierD

abbrev EvenTorus.Vertex (T : EvenTorus) := Fin T.width × Fin T.height


end StatMech.FrontierD
