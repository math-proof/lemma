/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCutLatticeCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
open Finset


namespace StatMech.FrontierA

def grahamC4Adj (u v : Fin 4) : Prop :=
  (u = 0 /\ v = 1) \/ (u = 1 /\ v = 0) \/
  (u = 1 /\ v = 3) \/ (u = 3 /\ v = 1) \/
  (u = 3 /\ v = 2) \/ (u = 2 /\ v = 3) \/
  (u = 2 /\ v = 0) \/ (u = 0 /\ v = 2)

end StatMech.FrontierA
