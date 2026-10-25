/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFiniteGhostComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicWeightedDirichletComparison.Part6
open Finset SimpleGraph


namespace StatMech.Universality

noncomputable section

def isingFiniteGhostGraph
    {V : Type*} (G : SimpleGraph V) (ghostRate : V → Real) :
    SimpleGraph (Option V) where
  Adj x y :=
    match x, y with
    | some a, some b => G.Adj a b
    | some a, none => 0 < ghostRate a
    | none, some b => 0 < ghostRate b
    | none, none => False
  symm := by
    constructor
    intro x y hxy
    cases x with
    | none =>
        cases y with
        | none => exact hxy
        | some y => exact hxy
    | some x =>
        cases y with
        | none => exact hxy
        | some y => exact G.symm.symm x y hxy
  loopless := by
    constructor
    intro x hxx
    cases x with
    | none => exact hxx
    | some x => exact G.loopless.irrefl x hxx


noncomputable def isingFiniteGhostConductance
    {V : Type*} (G : SimpleGraph V) (ghostRate : V → Real) :
    Option V → Option V → Real := by
  classical
  exact fun x y ↦ match x, y with
    | some a, some b => if G.Adj a b then 1 else 0
    | some a, none => ghostRate a
    | none, some b => ghostRate b
    | none, none => 0


def isingFiniteGhostExtension
    {V : Type*} (ghostValue : Real) (f : V → Real) : Option V → Real
  | some x => f x
  | none => ghostValue


def isingFiniteGhostBoundary {V : Type*} : Option V → Prop
  | some _ => False
  | none => True


def isingFiniteGhostBoundaryWith
    {V : Type*} (boundary : V → Prop) : Option V → Prop
  | some x => boundary x
  | none => True


def isingFiniteGhostInclusion
    {V : Type*} (G : SimpleGraph V) (ghostRate : V → Real) :
    G →g isingFiniteGhostGraph G ghostRate where
  toFun := some
  map_rel' := by
    intro x y hxy
    exact hxy

end
end StatMech.Universality
