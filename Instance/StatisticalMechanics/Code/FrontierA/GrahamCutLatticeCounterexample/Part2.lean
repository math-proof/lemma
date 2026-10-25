/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCutLatticeCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.FrontierA.GrahamCutLatticeCounterexample.Part2
open Finset


namespace StatMech.FrontierA

instance grahamC4ReachWithin_decidable
    (C : Finset (Fin 4)) (u v : Fin 4) :
    Decidable (grahamC4ReachWithin C u v) := by
  unfold grahamC4ReachWithin
  infer_instance


end StatMech.FrontierA
