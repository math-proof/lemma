/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part24
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

theorem exists_canonicalStableRawComponentReachesTerminal_of_ownerStable
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (self : CanonicalStableRawComponentSelfState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hstable : CanonicalStableRawOwnerStableStep
      ends m j k l zero hloop hjk hkl hk0 p hno self.1) :
    ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      CanonicalStableRawComponentReachesTerminal
        ends m j k l zero hloop hjk hkl hk0 p hno component
          self terminal := by
  classical
  have hnotExceptional :=
    canonicalStableRawComponentSuccessorToken_not_exceptional_of_ownerStable
      ends m j k l zero hloop hjk hkl hk0 p hno component self hstable
  let terminal : CanonicalStableRawComponentNonexceptionalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component :=
    ⟨canonicalStableRawComponentSuccessorToken
      ends m j k l zero hloop hjk hkl hk0 p hno component
        ⟨self.1, self.2.1⟩, hnotExceptional⟩
  have hterminal : canonicalStableRawComponentForestStep
        ends m j k l zero hloop hjk hkl hk0 p hno component
          ⟨self.1, self.2.1⟩ = Sum.inr terminal := by
    unfold canonicalStableRawComponentForestStep
    rw [dif_neg hnotExceptional]
  refine ⟨terminal, ?_⟩
  unfold CanonicalStableRawComponentReachesTerminal
    FiniteRankTerminalSystem.ReachesTerminal
  apply FiniteRankTerminalSystem.terminals_subset_terminalClosure
    (canonicalStableRawComponentTerminalSystem
      ends m j k l zero hloop hjk hkl hk0 p hno component) self
  unfold canonicalStableRawComponentTerminalSystem
    canonicalStableRawComponentImmediateTerminals
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hterminal⟩


theorem exists_canonicalStableRawComponentForestStep_terminal_of_ownerStable
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (self : CanonicalStableRawComponentSelfState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hstable : CanonicalStableRawOwnerStableStep
      ends m j k l zero hloop hjk hkl hk0 p hno self.1) :
    ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      canonicalStableRawComponentForestStep
          ends m j k l zero hloop hjk hkl hk0 p hno component
            ⟨self.1, self.2.1⟩ = Sum.inr terminal := by
  let hterminal :=
    canonicalStableRawComponentSuccessorToken_not_exceptional_of_ownerStable
      ends m j k l zero hloop hjk hkl hk0 p hno component self hstable
  let terminal : CanonicalStableRawComponentNonexceptionalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component :=
    ⟨canonicalStableRawComponentSuccessorToken
      ends m j k l zero hloop hjk hkl hk0 p hno component
        ⟨self.1, self.2.1⟩, hterminal⟩
  refine ⟨terminal, ?_⟩
  unfold canonicalStableRawComponentForestStep
  rw [dif_neg hterminal]


theorem exists_canonicalStableRawComponentForestStep_direct_of_advancing
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (self : CanonicalStableRawComponentSelfState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hadvancing : CanonicalStableRawOwnerAdvancingStep
      ends m j k l zero hloop hjk hkl hk0 p hno self.1) :
    ∃ direct : CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      canonicalStableRawComponentForestStep
          ends m j k l zero hloop hjk hkl hk0 p hno component
            ⟨self.1, self.2.1⟩ = Sum.inl direct := by
  let hexceptional :=
    canonicalStableRawComponentSuccessorToken_exceptional_of_advancing
      ends m j k l zero hloop hjk hkl hk0 p hno component self hadvancing
  let direct := canonicalStableRawComponentExceptionalSuccessorDirect
    ends m j k l zero hloop hjk hkl hk0 p hno component
      ⟨self.1, self.2.1⟩ hexceptional
  refine ⟨direct, ?_⟩
  unfold canonicalStableRawComponentForestStep
  rw [dif_pos hexceptional]


theorem canonicalStableRawComponentForestStep_token
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (s : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    (match canonicalStableRawComponentForestStep
        ends m j k l zero hloop hjk hkl hk0 p hno component s with
      | Sum.inl direct => canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component direct
      | Sum.inr terminal => terminal.1) =
      canonicalStableRawComponentSuccessorToken
        ends m j k l zero hloop hjk hkl hk0 p hno component s := by
  classical
  by_cases hexceptional : CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawComponentSuccessorToken
          ends m j k l zero hloop hjk hkl hk0 p hno component s).1
  · unfold canonicalStableRawComponentForestStep
    rw [dif_pos hexceptional]
    exact canonicalStableRawComponentExceptionalSuccessorDirect_natural
      ends m j k l zero hloop hjk hkl hk0 p hno component s hexceptional
  · unfold canonicalStableRawComponentForestStep
    rw [dif_neg hexceptional]


theorem canonicalStableRawComponentForestStep_direct_output_or_sibling
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (s : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (direct : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hstep : canonicalStableRawComponentForestStep
        ends m j k l zero hloop hjk hkl hk0 p hno component s =
      Sum.inl direct) :
    ∃ u : CanonicalStableRawExceptionalEdge
        ends m j k l zero hloop hjk hkl hk0 p,
      u.target = direct.1.target ∧
      (CanonicalStableRawOwnerStableOutput
          ends m j k l zero hloop hjk hkl hk0 p s.1 u ∨
        CanonicalStableRawOwnerAdvancingOutput
          ends m j k l zero hloop hjk hkl hk0 p s.1 u) ∧
      canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧
      (u = direct.1 ∨ u.source ≠ direct.1.source) := by
  classical
  let token := canonicalStableRawComponentSuccessorToken
    ends m j k l zero hloop hjk hkl hk0 p hno component s
  have hincident : CanonicalStableRawStateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p token.1 s.1 :=
    (canonicalStableRawWitnessedStateTokenIncidence_iff
      ends m j k l zero hloop hjk hkl hk0 p token.1 s.1).1
        (canonicalStableRawComponentSuccessorToken_incident
          ends m j k l zero hloop hjk hkl hk0 p hno component s)
  obtain ⟨u, huTarget, huKind, huComponent⟩ :=
    canonicalStableRawStateTokenIncidence_outputDichotomy
      ends m j k l zero hloop hjk hkl hk0 p hno token.1 s.1 hincident
  have hforestToken := canonicalStableRawComponentForestStep_token
    ends m j k l zero hloop hjk hkl hk0 p hno component s
  rw [hstep] at hforestToken
  have hrawToken :
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component direct).1 =
        token.1 := congrArg Subtype.val hforestToken
  have hdirectTarget : canonicalStableRawLeftTokenTarget
        ends m j k l zero hloop hjk hkl hk0 p
          (canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component direct).1 =
      direct.1.target := by
    apply Subtype.ext
    change (canonicalStableRawStateLeftToken
      ends m j k l zero hloop hjk hkl hk0 p hno direct.1).2.1 =
        direct.1.target.1
    unfold canonicalStableRawStateLeftToken
    rw [dif_neg direct.2.2]
    rfl
  have huDirectTarget : u.target = direct.1.target := by
    calc
      u.target = canonicalStableRawLeftTokenTarget
          ends m j k l zero hloop hjk hkl hk0 p token.1 := huTarget
      _ = canonicalStableRawLeftTokenTarget
          ends m j k l zero hloop hjk hkl hk0 p
            (canonicalStableRawComponentDirectEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component direct).1 :=
        congrArg (canonicalStableRawLeftTokenTarget
          ends m j k l zero hloop hjk hkl hk0 p) hrawToken.symm
      _ = direct.1.target := hdirectTarget
  refine ⟨u, huDirectTarget, huKind, huComponent.trans s.2, ?_⟩
  by_cases hsource : u.source = direct.1.source
  · exact Or.inl
      (canonicalStableRawExceptionalEdge_eq_of_source_target_eq
        hsource huDirectTarget)
  · exact Or.inr hsource


end StatMech.GrahamGHS.FourColor
