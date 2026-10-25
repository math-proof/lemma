/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCutLatticeCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.FrontierA.GrahamCutLatticeCounterexample
open Finset


namespace StatMech.FrontierA

instance grahamC4Adj_decidable (u v : Fin 4) :
    Decidable (grahamC4Adj u v) := by
  unfold grahamC4Adj
  infer_instance


end StatMech.FrontierA
