/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/StrongIsometryExt.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Structure.v1.Atlas.Buildings.code.Building.Basic.Part2
public import Mathlib.GroupTheory.Coxeter.Length
public import Structure.v1.Atlas.Buildings.code.Building.StrongIsometryExt

@[expose] public section

set_option maxHeartbeats 800000

variable {V : Type*} [DecidableEq V]


/-- A *strong isometry* $f : Y \to f(Y)$ between sets of chambers is a
bijection that preserves the $W$-valued distance $\delta$. -/
def IsStrongIsometry {b : Building V} (δW : Building.WValuedDist b)
    (Y Z : Set (Finset V))
    (φ : Finset V → Finset V) : Prop :=
  (∀ C ∈ Y, φ C ∈ Z) ∧
  (∀ C ∈ Z, ∃ D ∈ Y, φ D = C) ∧
  (∀ C ∈ Y, ∀ D ∈ Y,
    δW.delta (φ C) (φ D) = δW.delta C D)

