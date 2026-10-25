/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKStarTriangle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.FKTrihexDuality
open Finset
open scoped BigOperators


namespace StatMech

namespace FK

namespace PeriodicPlanar

open FrontierA


inductive ThreeTerminalConnectivity
  | separate
  | pair01
  | pair12
  | pair20
  | together
  deriving DecidableEq, Fintype


end PeriodicPlanar
end FK
end StatMech
