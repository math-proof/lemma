/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Basic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Theorem.v1.Atlas.Buildings.code.ChamberComplex.Basic
public import Theorem.Finset.Adjacent
public import Theorem.Nat.NotChamberAdjacent
public import Def.v1.Atlas.Buildings.code.ChamberComplex.CoxeterComplex.Part2
public import Mathlib.Order.Zorn
public section

set_option maxHeartbeats 800000

variable {V : Type*} [DecidableEq V]


/-- A simplicial map from $K$ to $L$: a vertex function sending faces of $K$ to faces of $L$. -/
structure SimplicialMap (K L : SimplicialComplex V) where
  toFun : V → V
  map_face : ∀ s ∈ K.faces, s.image toFun ∈ L.faces

