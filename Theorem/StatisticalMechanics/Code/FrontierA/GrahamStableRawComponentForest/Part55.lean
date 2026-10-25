/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part56
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

theorem
    CanonicalStableRawComponentBalancedDirectBlock.no_componentFiberRealization_of_deficit
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
    ¬ block.HasComponentFiberRealization := by
  intro hrealization
  obtain ⟨component', hcomponent'⟩ := hrealization
  have hcomplementPos : 0 < Fintype.card block.StateComplement := by
    have hstrict := block.complement_strictDeficit hdeficit
    omega
  let remaining : block.StateComplement :=
    Classical.choice (Fintype.card_pos_iff.mp hcomplementPos)
  have hremainingComponent : canonicalStableRawTokenComponent
      ends m j k l zero hloop hjk hkl hk0 p hno remaining.1.1 = component' :=
    (hcomponent' remaining.1).2 remaining.2
  have hcomponentEq : component' = component :=
    hremainingComponent.symm.trans remaining.1.2
  let index : Fin block.size := ⟨0, block.positive⟩
  let removed := block.sourceBlock index
  have hremovedMem : removed ∈
      finiteEmbeddingBlock block.size block.sourceBlock := by
    apply Finset.mem_map.mpr
    exact ⟨index, Finset.mem_univ _, rfl⟩
  have hremovedComponent : canonicalStableRawTokenComponent
      ends m j k l zero hloop hjk hkl hk0 p hno removed.1 = component' := by
    rw [hcomponentEq]
    exact removed.2
  exact ((hcomponent' removed).1 hremovedComponent) hremovedMem


theorem
    CanonicalStableRawComponentBalancedDirectBlock.IsClosed.restricts_incidence
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
    {block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component}
    (hclosed : block.IsClosed) (source : block.StateComplement)
    (token : CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hincident : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component source.1 token) :
    token ∉ finiteEmbeddingBlock block.size block.tokenBlock := by
  exact finiteRelationComplement_tokenClosed
    (CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    block.size block.sourceBlock block.tokenBlock hclosed source token hincident


theorem
    CanonicalStableRawComponentBalancedDirectBlock.exists_minimalComplementTightFamily
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
    ∃ family : Finset block.StateComplement,
      family.Nonempty ∧
      (block.complementNeighborhood family).card + 1 = family.card ∧
      (∀ source ∈ family,
        block.complementNeighborhood (family.erase source) =
          block.complementNeighborhood family) ∧
      ∀ smaller : Finset block.StateComplement, smaller ⊂ family ->
        smaller.card ≤ (block.complementNeighborhood smaller).card := by
  apply exists_minimal_deficiency_one_family
    block.complementNeighborhood block.complementNeighborhood_mono
  refine ⟨Finset.univ, ?_⟩
  have hle := Finset.card_le_univ
    (block.complementNeighborhood (Finset.univ :
      Finset block.StateComplement))
  calc
    (block.complementNeighborhood
        (Finset.univ : Finset block.StateComplement)).card ≤
        Fintype.card block.TokenComplement := by
      simpa only [Finset.card_univ] using hle
    _ < Fintype.card block.StateComplement :=
      block.complement_strictDeficit hdeficit
    _ = (Finset.univ : Finset block.StateComplement).card := by simp


theorem
    CanonicalStableRawComponentBalancedDirectBlock.exists_smallerComplementMinimalTightProblem
    {I : Type uI} {W : Type uW} [Fintype I] [DecidableEq I]
    [Fintype W] [DecidableEq W]
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
    (hclosed : block.IsClosed)
    (hdeficit : Fintype.card (CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) <
        Fintype.card (CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    ∃ problem : FiniteRelationMinimalTightProblem.{uI, uI},
      problem.rank < Fintype.card (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component) ∧
      ∀ source : block.StateComplement,
        ∀ token : CanonicalStableRawComponentToken
            ends m j k l zero hloop hjk hkl hk0 p hno component,
          CanonicalStableRawComponentIncident
              ends m j k l zero hloop hjk hkl hk0 p hno component
                source.1 token ->
            token ∉ finiteEmbeddingBlock block.size block.tokenBlock := by
  obtain ⟨family, hnonempty, htight, herase, hproper⟩ :=
    block.exists_minimalComplementTightFamily hdeficit
  let problem : FiniteRelationMinimalTightProblem :=
    { State := block.StateComplement
      Token := block.TokenComplement
      incident := block.complementIncident
      carrier := family
      nonempty := hnonempty
      deficiency_one := by
        simpa only [finiteBipartiteRelationNeighborhood,
          CanonicalStableRawComponentBalancedDirectBlock.complementNeighborhood]
          using htight
      erase_invariant := by
        intro source hsource
        simpa only [finiteBipartiteRelationNeighborhood,
          CanonicalStableRawComponentBalancedDirectBlock.complementNeighborhood]
          using herase source hsource
      proper_hall := by
        intro smaller hsmaller
        simpa only [finiteBipartiteRelationNeighborhood,
          CanonicalStableRawComponentBalancedDirectBlock.complementNeighborhood]
          using hproper smaller hsmaller }
  refine ⟨problem, ?_, fun source token hincident =>
    hclosed.restricts_incidence source token hincident⟩
  rw [problem.rank_eq_carrier_card]
  exact (Finset.card_le_univ family).trans_lt block.stateComplement_card_lt


end StatMech.GrahamGHS.FourColor
