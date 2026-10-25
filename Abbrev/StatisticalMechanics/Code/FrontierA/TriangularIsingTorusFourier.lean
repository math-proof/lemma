/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFourier.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusKacWard.Part2
import Theorem.StatisticalMechanics.Code.Onsager.KWSpinFourier.Part3
open scoped BigOperators Matrix


namespace StatMech.FrontierA

open StatMech.Onsager

abbrev triangularTorusDart (L : Nat) :=
  (ZMod L × ZMod L) × Fin 6


end StatMech.FrontierA
