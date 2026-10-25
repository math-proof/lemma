/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/PlanarFKDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.KWGeometricDual.Part22
import Theorem.StatisticalMechanics.Code.BeffaraDC.Duality
import Theorem.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality
open Finset SimpleGraph Set


namespace StatMech

namespace BeffaraDC

open Lattice Ising Walls


noncomputable def pfdFace (P : PlanarZ2Subgraph) (f : Site 2) : kwg_Face P :=
  (whb_faceRegion (imageGraph P)).connectedComponentMk f


end BeffaraDC
end StatMech
