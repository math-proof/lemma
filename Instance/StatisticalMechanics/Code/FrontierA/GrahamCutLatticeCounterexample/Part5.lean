/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCutLatticeCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.FrontierA.GrahamCutLatticeCounterexample.Part5
open Finset


namespace StatMech.FrontierA

instance grahamK23ReachWithin_decidable
    (C : Finset (Fin 5)) (u v : Fin 5) :
    Decidable (grahamK23ReachWithin C u v) := by
  unfold grahamK23ReachWithin
  infer_instance


end StatMech.FrontierA
