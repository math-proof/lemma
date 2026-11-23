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
public import Structure.v1.Atlas.Buildings.code.Building.Basic

@[expose] public section

set_option maxHeartbeats 800000

variable {V : Type*} [DecidableEq V]


/-- `A` is a subcomplex of `K` iff every face of `A` is a face of `K`. -/
def IsSubcomplex (A K : SimplicialComplex V) : Prop :=
  A.faces ⊆ K.faces

