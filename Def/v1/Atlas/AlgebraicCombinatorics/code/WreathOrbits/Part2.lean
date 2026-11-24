module
public import Instance.v1.Atlas.AlgebraicCombinatorics.code.YoungLattice.Part3
public import Theorem.Finset.Atlas.v1.AlgebraicCombinatorics.code.YoungLattice
public import Mathlib.Data.Multiset.Sort
public import Mathlib.Data.Finset.Card
public import Mathlib.Order.Fin.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Data.List.Sort
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.List.GetD
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Logic.Equiv.Basic
public import Structure.v1.Atlas.AlgebraicCombinatorics.code.WreathOrbits
set_option autoImplicit false


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WreathOrbits.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace WreathOrbits

variable {m n : ℕ}

def WreathElem.actOn (g : WreathElem m n) (p : Fin m × Fin n) : Fin m × Fin n :=
  (g.σ p.1, g.τ p.1 p.2)

def WreathElem.actOnSet (g : WreathElem m n) (S : Finset (Fin m × Fin n)) :
    Finset (Fin m × Fin n) :=
  S.image g.actOn

def SameOrbit (S T : Finset (Fin m × Fin n)) : Prop :=
  ∃ g : WreathElem m n, g.actOnSet S = T

end WreathOrbits
