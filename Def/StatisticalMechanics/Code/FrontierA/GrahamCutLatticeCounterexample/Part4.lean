/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCutLatticeCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCutLatticeCounterexample
open Finset


namespace StatMech.FrontierA

def grahamK23Adj (u v : Fin 5) : Prop :=
  ((u = 0 \/ u = 1) /\ (v = 2 \/ v = 3 \/ v = 4)) \/
    ((v = 0 \/ v = 1) /\ (u = 2 \/ u = 3 \/ u = 4))

end StatMech.FrontierA
