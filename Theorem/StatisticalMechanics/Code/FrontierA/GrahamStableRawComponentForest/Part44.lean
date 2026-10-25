/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part44
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

theorem canonicalStableRawComponentTightSuccessorToken_incident
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (state : ↑sources) :
    CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component state.1
        (canonicalStableRawComponentTightSuccessorToken
          ends m j k l zero hloop hjk hkl hk0 p hno component
            sources state).1 :=
  canonicalStableRawComponentSuccessorToken_incident
    ends m j k l zero hloop hjk hkl hk0 p hno component state.1


theorem canonicalStableRawComponent_directOutput_mem_tightNeighborhood
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (state : ↑sources)
    (token : ↑(canonicalStableRawComponentIncidentNeighborhood
      ends m j k l zero hloop hjk hkl hk0 p hno component sources))
    (hincident : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component state.1 token.1)
    (u : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)
    (huTarget : u.target = canonicalStableRawLeftTokenTarget
      ends m j k l zero hloop hjk hkl hk0 p token.1.1)
    (huKind : CanonicalStableRawOwnerStableOutput
        ends m j k l zero hloop hjk hkl hk0 p state.1.1 u ∨
      CanonicalStableRawOwnerAdvancingOutput
        ends m j k l zero hloop hjk hkl hk0 p state.1.1 u)
    (huComponent : canonicalStableRawTokenComponent
      ends m j k l zero hloop hjk hkl hk0 p hno u = component)
    (huDirect : u.target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p u.source) :
    let direct : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component :=
        ⟨u, huComponent, huDirect⟩
    canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component direct ∈
      canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources := by
  classical
  dsimp only
  let direct : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component :=
    ⟨u, huComponent, huDirect⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, state.1, state.2, ?_⟩
  apply (canonicalStableRawWitnessedStateTokenIncidence_iff
    ends m j k l zero hloop hjk hkl hk0 p _ state.1.1).2
  have horiginal := (canonicalStableRawWitnessedStateTokenIncidence_iff
    ends m j k l zero hloop hjk hkl hk0 p token.1.1 state.1.1).1 hincident
  change CanonicalStableRawStateTokenIncidence
    ends m j k l zero hloop hjk hkl hk0 p
      (canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno u) state.1.1
  unfold canonicalStableRawStateLeftToken
  rw [dif_neg huDirect]
  dsimp only [CanonicalStableRawStateTokenIncidence,
    canonicalStableRawDirectLeftToken]
  dsimp only [CanonicalStableRawStateTokenIncidence] at horiginal
  have htarget : u.target.1 = token.1.1.2.1 :=
    congrArg Subtype.val huTarget
  refine ⟨?_, ?_, ?_⟩
  · rcases huKind with huStable | huAdvancing
    · exact Or.inl huStable.1
    · exact Or.inr (Subtype.ext huAdvancing)
  · rw [htarget]
    exact horiginal.2.1
  · rw [htarget]
    exact horiginal.2.2


end StatMech.GrahamGHS.FourColor
