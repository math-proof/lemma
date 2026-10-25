/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertex.Part9
import Def.StatisticalMechanics.Code.FrontierD.SixVertexRectangleBoundary.Part3
open Finset


namespace StatMech.FrontierD

abbrev SixVertexToroidalBoundary (N M : ℕ) :=
  (Fin M → Bool) × (Fin N → Bool)


end StatMech.FrontierD
