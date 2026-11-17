/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/IsometryGroups.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.GroupTheory.Coxeter.Basic
public import Mathlib.GroupTheory.Coxeter.Length
public import Structure.v1.Atlas.Buildings.code.SphericalBuilding.IsometryGroups.Part2

@[expose] public section

set_option linter.unusedSectionVars false


namespace IsometryBuilding

variable {k : Type*} [CommRing k] {V : Type*} [AddCommGroup V] [Module k V]


/-- The Coxeter matrix $M$ is of type $C_n$: diagonal entries are $1$, consecutive simple
reflections satisfy $m_{i,i+1} = 3$ except the last pair which has $m_{n-2, n-1} = 4$, and all
non-adjacent pairs commute ($m_{ij} = 2$). -/
def TypeCn (n : ℕ) (M : CoxeterMatrix (Fin n)) : Prop :=


  (∀ i : Fin n, M i i = 1) ∧
  (∀ i j : Fin n, i ≠ j → (

    (i.val + 1 = j.val ∧ j.val < n - 1 → M i j = 3) ∧

    (i.val + 1 = j.val ∧ j.val = n - 1 ∧ 1 < n → M i j = 4) ∧

    (i.val + 1 < j.val ∨ j.val + 1 < i.val → M i j = 2)))

end IsometryBuilding
