/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part55
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

theorem CanonicalStableRawComponentBalancedDirectBlock.complementNeighborhood_mono
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    Monotone block.complementNeighborhood := by
  classical
  intro smaller larger hsubset token htoken
  obtain ⟨source, hsource, hincident⟩ :=
    (Finset.mem_filter.mp htoken).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ token,
    source, hsubset hsource, hincident⟩


theorem
    CanonicalStableRawTightChargeOrbit.HasDirectOrbitDischarge.richStrictBlock_or_balancedBlock
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
    {orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources}
    (hdischarge : orbit.HasDirectOrbitDischarge) :
    Nonempty (CanonicalStableRawComponentRichStrictBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component) ∨
      ∃ size : Nat, 0 < size ∧
        Nonempty (Fin size ↪ CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component) ∧
        Nonempty (Fin size ↪ CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  dsimp only [CanonicalStableRawTightChargeOrbit.HasDirectOrbitDischarge]
    at hdischarge
  obtain ⟨_entry, start, _hentry, hterminal | hbalanced⟩ := hdischarge
  · left
    obtain ⟨_n, _hn, terminal, _hterminal⟩ := hterminal
    exact exists_canonicalStableRawComponentDirect_richStrictBlock_of_available
      ends m j k l zero hloop hjk hkl hk0 p hno component start terminal
  · exact Or.inr hbalanced


theorem
    CanonicalStableRawTightChargeOrbit.HasDirectOrbitDischarge.richStrict_or_balancedResidual
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
    {orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources}
    (hdeficit : Fintype.card (CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) <
        Fintype.card (CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hdischarge : orbit.HasDirectOrbitDischarge) :
    Nonempty (CanonicalStableRawComponentRichStrictBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component) ∨
      orbit.HasBalancedResidualDeficit := by
  rcases hdischarge.richStrictBlock_or_balancedBlock with hrich |
      ⟨size, hsize, hdirect, htoken⟩
  · exact Or.inl hrich
  · right
    dsimp only [CanonicalStableRawTightChargeOrbit.HasBalancedResidualDeficit]
    refine ⟨size, hsize, hdirect, htoken, ?_⟩
    have hstate := Nat.card_congr
      (canonicalStableRawComponentStateEquivSelfSumDirect
        ends m j k l zero hloop hjk hkl hk0 p hno component)
    simp only [Nat.card_sum] at hstate
    apply strictDeficit_sub_balancedEmbeddings size
      (directBlock := hdirect) (tokenBlock := htoken)
    rw [← hstate]
    simpa only [Nat.card_eq_fintype_card] using hdeficit


theorem
    CanonicalStableRawTightChargeOrbit.HasBalancedResidualDeficit.exists_block
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
    {orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources}
    (hresidual : orbit.HasBalancedResidualDeficit) :
    ∃ block : CanonicalStableRawComponentBalancedDirectBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      Nat.card (CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) - block.size <
        Nat.card (CanonicalStableRawComponentSelfState
            ends m j k l zero hloop hjk hkl hk0 p hno component) +
          (Nat.card (CanonicalStableRawComponentDirectState
            ends m j k l zero hloop hjk hkl hk0 p hno component) -
              block.size) := by
  dsimp only [CanonicalStableRawTightChargeOrbit.HasBalancedResidualDeficit]
    at hresidual
  obtain ⟨size, hsize, ⟨directs⟩, ⟨tokens⟩, hstrict⟩ := hresidual
  exact ⟨⟨size, hsize, directs, tokens⟩, hstrict⟩


theorem CanonicalStableRawComponentBalancedDirectBlock.closed_or_crossing
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    block.IsClosed ∨
      ∃ source token,
        CanonicalStableRawComponentIncident
            ends m j k l zero hloop hjk hkl hk0 p hno component source token ∧
          (∀ i, source ≠ block.sourceBlock i) ∧
          ∃ i, token = block.tokenBlock i := by
  exact finiteRelationTokenClosed_or_crossing
    (CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    block.size block.sourceBlock block.tokenBlock


theorem
    CanonicalStableRawComponentBalancedDirectBlock.complement_strictDeficit
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hdeficit : Fintype.card (CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) <
        Fintype.card (CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    Fintype.card block.TokenComplement <
      Fintype.card block.StateComplement := by
  exact finiteEmbeddingComplement_strictDeficit
    block.size block.sourceBlock block.tokenBlock hdeficit


theorem
    CanonicalStableRawComponentBalancedDirectBlock.stateComplement_card_lt
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    Fintype.card block.StateComplement <
      Fintype.card (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component) := by
  rw [finiteEmbeddingComplement_card]
  have hsize : block.size ≤ Fintype.card
      (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component) := by
    simpa only [Fintype.card_fin] using
      Fintype.card_le_of_injective block.sourceBlock block.sourceBlock.injective
  have hpositive := block.positive
  omega


end StatMech.GrahamGHS.FourColor
