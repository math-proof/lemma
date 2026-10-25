/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part51
open Finset


namespace StatMech.GrahamGHS.FourColor

universe u v uI uW

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


attribute [instance]
  FiniteRelationMinimalTightProblem.stateFintype
  FiniteRelationMinimalTightProblem.stateDecidableEq
  FiniteRelationMinimalTightProblem.tokenFintype
  FiniteRelationMinimalTightProblem.tokenDecidableEq

def CanonicalStableRawTightChargeOrbit.HasRetainedSharedTokenOutput
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    (orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources) : Prop :=
  ∃ source : ↑sources,
    ∃ q : Fin orbit.size,
      ∃ token : ↑(canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources),
        ∃ u : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p,
          source ≠ orbit.states q.succ ∧
          source = orbit.states 0 ∧
          token = canonicalStableRawComponentTightNaturalToken
              ends m j k l zero hloop hjk hkl hk0 p hno component sources
                source ∧
          token = orbit.tokens q ∧
          CanonicalStableRawComponentIncident
              ends m j k l zero hloop hjk hkl hk0 p hno component
                source.1 token.1 ∧
          CanonicalStableRawComponentIncident
              ends m j k l zero hloop hjk hkl hk0 p hno component
                (orbit.states q.succ).1 token.1 ∧
          u.target = canonicalStableRawLeftTokenTarget
              ends m j k l zero hloop hjk hkl hk0 p token.1.1 ∧
          (CanonicalStableRawOwnerStableOutput
                ends m j k l zero hloop hjk hkl hk0 p source.1.1 u ∨
            CanonicalStableRawOwnerAdvancingOutput
                ends m j k l zero hloop hjk hkl hk0 p source.1.1 u) ∧
          canonicalStableRawTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno u = component


def CanonicalStableRawTightChargeOrbit.HasFreshInternalChordOutput
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    (orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources) : Prop :=
  ∃ q r : Fin (orbit.size + 1),
    ∃ token : ↑(canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources),
      ∃ u : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p,
        q ≠ r ∧
        (∀ s, token ≠ orbit.tokens s) ∧
        CanonicalStableRawComponentIncident
            ends m j k l zero hloop hjk hkl hk0 p hno component
              (orbit.states q).1 token.1 ∧
        CanonicalStableRawComponentIncident
            ends m j k l zero hloop hjk hkl hk0 p hno component
              (orbit.states r).1 token.1 ∧
        u.target = canonicalStableRawLeftTokenTarget
            ends m j k l zero hloop hjk hkl hk0 p token.1.1 ∧
        (CanonicalStableRawOwnerStableOutput
              ends m j k l zero hloop hjk hkl hk0 p (orbit.states q).1.1 u ∨
          CanonicalStableRawOwnerAdvancingOutput
              ends m j k l zero hloop hjk hkl hk0 p (orbit.states q).1.1 u) ∧
        canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno u = component


end StatMech.GrahamGHS.FourColor
