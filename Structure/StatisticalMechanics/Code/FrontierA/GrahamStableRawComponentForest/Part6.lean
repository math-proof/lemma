/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part47
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

structure CanonicalStableRawTightChargeOrbit
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)) where
  size : Nat
  states : Fin (size + 1) ↪ ↑sources
  tokens : Fin size ↪
    ↑(canonicalStableRawComponentIncidentNeighborhood
      ends m j k l zero hloop hjk hkl hk0 p hno component sources)
  paired : ∀ i, CanonicalStableRawComponentIncident
    ends m j k l zero hloop hjk hkl hk0 p hno component
      (states i.succ).1 (tokens i).1
  coreSelf : Fin (size + 1)
  coreDirect : Fin (size + 1)
  coreThird : Fin (size + 1)
  coreNatural : Fin size
  coreFirst : Fin size
  origin : ∀ i,
    tokens i = canonicalStableRawComponentTightNaturalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component sources
          (states i.succ) ∨
      tokens i = canonicalStableRawComponentTightSuccessorToken
        ends m j k l zero hloop hjk hkl hk0 p hno component sources
          (states i.succ) ∨
      i = coreFirst
  coreSelf_ne_direct : coreSelf ≠ coreDirect
  coreSelf_ne_third : coreSelf ≠ coreThird
  coreDirect_ne_third : coreDirect ≠ coreThird
  coreNatural_ne_first : coreNatural ≠ coreFirst
  self_natural : CanonicalStableRawComponentIncident
    ends m j k l zero hloop hjk hkl hk0 p hno component
      (states coreSelf).1 (tokens coreNatural).1
  direct_natural : CanonicalStableRawComponentIncident
    ends m j k l zero hloop hjk hkl hk0 p hno component
      (states coreDirect).1 (tokens coreNatural).1
  self_first : CanonicalStableRawComponentIncident
    ends m j k l zero hloop hjk hkl hk0 p hno component
      (states coreSelf).1 (tokens coreFirst).1
  third_first : CanonicalStableRawComponentIncident
    ends m j k l zero hloop hjk hkl hk0 p hno component
      (states coreThird).1 (tokens coreFirst).1


end StatMech.GrahamGHS.FourColor
