/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalWilson.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeWilsonAffine.Part3
import Inductive.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalWilson
open scoped BigOperators
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech.FrontierA

noncomputable section

def cubicalPlaquetteIncidence {a b c : Nat} :
    CubicalPlaquette a b c → Finset (CubicalEdge a b c)
  | .xy i j k =>
      {.x i j.castSucc k, .x i j.succ k,
        .y i.castSucc j k, .y i.succ j k}
  | .xz i j k =>
      {.x i j k.castSucc, .x i j k.succ,
        .z i.castSucc j k, .z i.succ j k}
  | .yz i j k =>
      {.y i j k.castSucc, .y i j k.succ,
        .z i j.castSucc k, .z i j.succ k}


def cubicalEdgeEndpoints {a b c : Nat} :
    CubicalEdge a b c → Finset (CubicalVertex a b c)
  | .x i j k =>
      {⟨i.castSucc, j, k⟩, ⟨i.succ, j, k⟩}
  | .y i j k =>
      {⟨i, j.castSucc, k⟩, ⟨i, j.succ, k⟩}
  | .z i j k =>
      {⟨i, j, k.castSucc⟩, ⟨i, j, k.succ⟩}


def cubicalVertexStar {a b c : Nat} (v : CubicalVertex a b c) :
    Finset (CubicalEdge a b c) :=
  Finset.univ.filter fun e => v ∈ cubicalEdgeEndpoints e


end
end StatMech.FrontierA
