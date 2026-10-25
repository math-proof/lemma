/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCutLatticeCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.FrontierA.GrahamCutLatticeCounterexample.Part4
open Finset


namespace StatMech.FrontierA

instance grahamK23Adj_decidable (u v : Fin 5) :
    Decidable (grahamK23Adj u v) := by
  unfold grahamK23Adj
  infer_instance


end StatMech.FrontierA
