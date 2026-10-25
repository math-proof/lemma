/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part60
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
    CanonicalStableRawComponentBalancedDirectBlock.geometricCrossing_of_crossing
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (source : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (token : CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hincident : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component source token)
    (hsource : ∀ i, source ≠ block.sourceBlock i)
    (index : Fin block.size) (htoken : token = block.tokenBlock index) :
    block.HasGeometricCrossing := by
  have hsourceIncident : CanonicalStableRawWitnessedStateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p token.1 source.1 := hincident
  have hdirectIncident : CanonicalStableRawWitnessedStateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p token.1
        (block.directs index).1 := by
    apply (canonicalStableRawWitnessedStateTokenIncidence_iff
      ends m j k l zero hloop hjk hkl hk0 p token.1
        (block.directs index).1).2
    rw [htoken]
    exact canonicalStableRawStateLeftToken_stateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p hno (block.directs index).1
  rcases canonicalStableRawWitnessedStateTokenIncidence_sharedTokenClassification
      ends m j k l zero hloop hjk hkl hk0 p hno token.1
        source.1 (block.directs index).1 hsourceIncident hdirectIncident with
    heq | ⟨u, htarget, hkind, hcomponent, _⟩ |
      ⟨u, htarget, hkind, hcomponent, _⟩
  · exact False.elim (hsource index (by
      apply Subtype.ext
      exact heq))
  · exact ⟨source, token, index, hincident, hsource, htoken,
      u, htarget, Or.inl hkind, hcomponent.trans source.2⟩
  · exact ⟨source, token, index, hincident, hsource, htoken,
      u, htarget, Or.inr hkind, hcomponent.trans source.2⟩


theorem
    CanonicalStableRawComponentBalancedDirectBlock.HasGeometricCrossing.exists_crossingFamily
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
    (hcross : block.HasGeometricCrossing) :
    ∃ source token,
      ∃ hsource : ∀ i, source ≠ block.sourceBlock i,
        let family := block.crossingFamily source hsource
        source ∈ family.states ∧ token ∈ family.tokens ∧
          CanonicalStableRawComponentIncident
            ends m j k l zero hloop hjk hkl hk0 p hno component source token ∧
          ∃ u : CanonicalStableRawExceptionalEdge
              ends m j k l zero hloop hjk hkl hk0 p,
            u.target = canonicalStableRawLeftTokenTarget
              ends m j k l zero hloop hjk hkl hk0 p token.1 ∧
            (CanonicalStableRawOwnerStableOutput
                  ends m j k l zero hloop hjk hkl hk0 p source.1 u ∨
              CanonicalStableRawOwnerAdvancingOutput
                  ends m j k l zero hloop hjk hkl hk0 p source.1 u) ∧
            canonicalStableRawTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
  obtain ⟨source, token, index, hincident, hsource, htoken,
      u, htarget, hkind, hcomponent⟩ := hcross
  refine ⟨source, token, hsource, ?_, ?_, hincident,
    u, htarget, hkind, hcomponent⟩
  · exact Finset.mem_insert_self _ _
  · apply Finset.mem_map.mpr
    exact ⟨index, Finset.mem_univ _, htoken.symm⟩


theorem
    CanonicalStableRawComponentBalancedDirectBlock.HasGeometricCrossing.exists_reroutedSourceBlock
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
    (hcross : block.HasGeometricCrossing) :
    ∃ source token, ∃ index : Fin block.size,
      ∃ hsource : ∀ i, source ≠ block.sourceBlock i,
        let rerouted := finiteEmbedding_replaceAt
          block.sourceBlock source hsource index
        token = block.tokenBlock index ∧
        rerouted index = source ∧
        (∀ q, q ≠ index -> rerouted q = block.sourceBlock q) ∧
        (∀ q, CanonicalStableRawComponentIncident
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (rerouted q) (block.tokenBlock q)) ∧
        block.sourceBlock index ∉ finiteEmbeddingBlock block.size rerouted := by
  obtain ⟨source, token, index, hincident, hsource, htoken,
      _u, _htarget, _hkind, _hcomponent⟩ := hcross
  refine ⟨source, token, index, hsource, htoken, ?_, ?_, ?_, ?_⟩
  · exact finiteEmbedding_replaceAt_same
      block.sourceBlock source hsource index
  · intro q hq
    exact finiteEmbedding_replaceAt_ne
      block.sourceBlock source hsource index q hq
  · intro q
    by_cases hq : q = index
    · subst q
      rw [finiteEmbedding_replaceAt_same, ← htoken]
      exact hincident
    · rw [finiteEmbedding_replaceAt_ne
        block.sourceBlock source hsource index q hq]
      apply (canonicalStableRawWitnessedStateTokenIncidence_iff
        ends m j k l zero hloop hjk hkl hk0 p
          (block.tokenBlock q).1 (block.sourceBlock q).1).2
      change CanonicalStableRawStateTokenIncidence
        ends m j k l zero hloop hjk hkl hk0 p
          (canonicalStableRawStateLeftToken
            ends m j k l zero hloop hjk hkl hk0 p hno
              (block.directs q).1) (block.directs q).1
      exact canonicalStableRawStateLeftToken_stateTokenIncidence
        ends m j k l zero hloop hjk hkl hk0 p hno (block.directs q).1
  · intro hmem
    obtain ⟨q, _hq, heq⟩ := Finset.mem_map.mp hmem
    exact finiteEmbedding_replaceAt_displaced_fresh
      block.sourceBlock source hsource index q heq.symm


theorem
    CanonicalStableRawComponentBalancedDirectBlock.HasOldOutputCrossing.output_displaced_or_retained
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
    (hcross : block.HasOldOutputCrossing) :
    ∃ source token, ∃ index oldIndex : Fin block.size,
      ∃ hsource : ∀ i, source ≠ block.sourceBlock i,
        let rerouted := finiteEmbedding_replaceAt
          block.sourceBlock source hsource index
        CanonicalStableRawComponentIncident
            ends m j k l zero hloop hjk hkl hk0 p hno component source token ∧
          token = block.tokenBlock index ∧
          block.sourceBlock index ∉
            finiteEmbeddingBlock block.size rerouted ∧
          (oldIndex = index ∨
            block.sourceBlock oldIndex ∈
              finiteEmbeddingBlock block.size rerouted) ∧
          ∃ u : CanonicalStableRawExceptionalEdge
              ends m j k l zero hloop hjk hkl hk0 p,
            u = (block.directs oldIndex).1 ∧
            u.target = canonicalStableRawLeftTokenTarget
              ends m j k l zero hloop hjk hkl hk0 p token.1 ∧
            (CanonicalStableRawOwnerStableOutput
                  ends m j k l zero hloop hjk hkl hk0 p source.1 u ∨
              CanonicalStableRawOwnerAdvancingOutput
                  ends m j k l zero hloop hjk hkl hk0 p source.1 u) := by
  obtain ⟨source, token, index, oldIndex, hincident, hsource, htoken,
      u, hu, htarget, hkind⟩ := hcross
  refine ⟨source, token, index, oldIndex, hsource,
    hincident, htoken, ?_, ?_, u, hu, htarget, hkind⟩
  · intro hmem
    obtain ⟨q, _hq, heq⟩ := Finset.mem_map.mp hmem
    exact finiteEmbedding_replaceAt_displaced_fresh
      block.sourceBlock source hsource index q heq.symm
  · by_cases hold : oldIndex = index
    · exact Or.inl hold
    · right
      apply Finset.mem_map.mpr
      refine ⟨oldIndex, Finset.mem_univ _, ?_⟩
      exact finiteEmbedding_replaceAt_ne
        block.sourceBlock source hsource index oldIndex hold


theorem
    CanonicalStableRawComponentBalancedDirectBlock.HasGeometricCrossing.growth_or_self_or_oldOutput
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component}
    (hcross : block.HasGeometricCrossing) :
    (∃ extended : CanonicalStableRawComponentBalancedDirectBlock
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        extended.size = block.size + 1) ∨
      Nonempty (CanonicalStableRawComponentSelfState
        ends m j k l zero hloop hjk hkl hk0 p hno component) ∨
      block.HasOldOutputCrossing := by
  obtain ⟨source, token, index, hincident, hsource, htoken,
      u, htarget, hkind, hcomponent⟩ := hcross
  by_cases huDirect : u.target.1 ≠ canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p u.source
  · let direct : CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
      ⟨u, hcomponent, huDirect⟩
    by_cases hfresh : ∀ i, direct ≠ block.directs i
    · left
      obtain ⟨directs, _hprefix, _hlast⟩ :=
        finiteEmbedding_snoc block.size block.directs direct hfresh
      let tokens : Fin (block.size + 1) ↪
          CanonicalStableRawComponentToken
            ends m j k l zero hloop hjk hkl hk0 p hno component :=
        directs.trans (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
      exact ⟨⟨block.size + 1, by omega, directs, tokens⟩, rfl⟩
    · right
      right
      push Not at hfresh
      obtain ⟨oldIndex, hold⟩ := hfresh
      exact ⟨source, token, index, oldIndex, hincident, hsource, htoken,
        u, by simpa only [direct] using congrArg Subtype.val hold,
        htarget, hkind⟩
  · right
    left
    have huSelf : u.target.1 = canonicalStableRawSelfBase
        ends m j k l zero hloop hjk hkl hk0 p u.source :=
      Classical.not_not.mp huDirect
    exact ⟨⟨u, hcomponent, huSelf⟩⟩


theorem
    CanonicalStableRawComponentBalancedDirectBlock.HasGeometricCrossing.growth_or_self_or_naturalEscape_or_stableSelf_or_rankDrop
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    {block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component}
    (hcross : block.HasGeometricCrossing) :
    (∃ extended : CanonicalStableRawComponentBalancedDirectBlock
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        extended.size = block.size + 1) ∨
      Nonempty (CanonicalStableRawComponentSelfState
        ends m j k l zero hloop hjk hkl hk0 p hno component) ∨
      block.HasNaturalTokenEscape ∨
      block.HasStableSelfOldOutput ∨
      block.HasAdvancingOldOutputRankDrop := by
  rcases hcross.growth_or_self_or_oldOutput with hgrowth | hself | hold
  · exact Or.inl hgrowth
  · exact Or.inr (Or.inl hself)
  · rcases hold.naturalEscape_or_stableSelf_or_advancingRankDrop with
      hescape | hstable | hrank
    · exact Or.inr (Or.inr (Or.inl hescape))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hstable)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hrank)))


theorem
    CanonicalStableRawComponentBalancedDirectBlock.HasGeometricCrossing.growth_or_self_or_naturalEscape_or_terminal_or_rankDrop
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    [DecidableEq (CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    {block : CanonicalStableRawComponentBalancedDirectBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component}
    (hcross : block.HasGeometricCrossing) :
    (∃ extended : CanonicalStableRawComponentBalancedDirectBlock
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        extended.size = block.size + 1) ∨
      Nonempty (CanonicalStableRawComponentSelfState
        ends m j k l zero hloop hjk hkl hk0 p hno component) ∨
      block.HasNaturalTokenEscape ∨
      Nonempty (CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) ∨
      ∃ source : CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        ∃ u : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p,
          canonicalStableRawTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧
          canonicalStableRawSourceRank ends m j k l zero p u.source <
            canonicalStableRawSourceRank ends m j k l zero p
              source.1.source := by
  rcases hcross.growth_or_self_or_naturalEscape_or_stableSelf_or_rankDrop with
    hgrowth | hself | hescape | hstable | hadvancing
  · exact Or.inl hgrowth
  · exact Or.inr (Or.inl hself)
  · exact Or.inr (Or.inr (Or.inl hescape))
  · rcases hstable.terminal_or_rankDrop with hterminal | hrank
    · exact Or.inr (Or.inr (Or.inr (Or.inl hterminal)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hrank)))
  · obtain ⟨source, _index, _oldIndex, _hsource, _hcrossing, _hnatural,
      u, _hu, _htarget, _hkind, hrank⟩ := hadvancing
    have huComponent : canonicalStableRawTokenComponent
        ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
      rw [_hu]
      exact (block.directs _oldIndex).2.1
    exact Or.inr (Or.inr (Or.inr (Or.inr
      ⟨source, u, huComponent, hrank⟩)))


theorem
    CanonicalStableRawTightChargeOrbit.HasBalancedResidualDeficit.complementTightFamily_or_geometricCrossing
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
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    {orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources}
    (hresidual : orbit.HasBalancedResidualDeficit)
    (hdeficit : Fintype.card (CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) <
        Fintype.card (CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    ∃ block : CanonicalStableRawComponentBalancedDirectBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      (block.IsClosed ∧
        Fintype.card block.StateComplement <
          Fintype.card (CanonicalStableRawComponentState
            ends m j k l zero hloop hjk hkl hk0 p hno component) ∧
        Fintype.card block.TokenComplement <
          Fintype.card block.StateComplement ∧
        (∃ family : Finset block.StateComplement,
          family.Nonempty ∧
          (block.complementNeighborhood family).card + 1 = family.card ∧
          (∀ source ∈ family,
            block.complementNeighborhood (family.erase source) =
              block.complementNeighborhood family) ∧
          ∀ smaller : Finset block.StateComplement, smaller ⊂ family ->
            smaller.card ≤ (block.complementNeighborhood smaller).card) ∧
        ∀ source : block.StateComplement, ∀ token,
          CanonicalStableRawComponentIncident
              ends m j k l zero hloop hjk hkl hk0 p hno component
                source.1 token ->
            token ∉ finiteEmbeddingBlock block.size block.tokenBlock) ∨
      block.HasGeometricCrossing := by
  obtain ⟨block, _hstrict⟩ := hresidual.exists_block
  refine ⟨block, ?_⟩
  rcases block.closed_or_crossing with hclosed |
      ⟨source, token, hincident, hsource, index, htoken⟩
  · left
    exact ⟨hclosed, block.stateComplement_card_lt,
      block.complement_strictDeficit hdeficit,
      block.exists_minimalComplementTightFamily hdeficit,
      fun source token hincident =>
        hclosed.restricts_incidence source token hincident⟩
  · right
    exact block.geometricCrossing_of_crossing
      source token hincident hsource index htoken


theorem
    CanonicalStableRawTightChargeOrbit.HasBalancedResidualDeficit.smallerRecursion_or_crossingContinuation
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
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    {orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources}
    (hresidual : orbit.HasBalancedResidualDeficit)
    (hdeficit : Fintype.card (CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) <
        Fintype.card (CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    ∃ block : CanonicalStableRawComponentBalancedDirectBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      (block.IsClosed ∧
        ∃ problem : FiniteRelationMinimalTightProblem.{uI, uI},
          problem.rank < Fintype.card (CanonicalStableRawComponentState
            ends m j k l zero hloop hjk hkl hk0 p hno component) ∧
          ∀ source : block.StateComplement,
            ∀ token : CanonicalStableRawComponentToken
                ends m j k l zero hloop hjk hkl hk0 p hno component,
              CanonicalStableRawComponentIncident
                  ends m j k l zero hloop hjk hkl hk0 p hno component
                    source.1 token ->
                token ∉ finiteEmbeddingBlock block.size block.tokenBlock) ∨
      (block.HasGeometricCrossing ∧
        ∃ continuation : FiniteRelationCrossingContinuation
            (CanonicalStableRawComponentIncident
              ends m j k l zero hloop hjk hkl hk0 p hno component),
          continuation.size = block.size ∧
          let move :=
            StatMech.FrontierA.RelationPartialMatching.HoleState.move
              continuation.natural continuation.natural_incident
          ∃ start stop : Nat, start < stop ∧ stop ≤ block.size + 1 ∧
            (move^[start] continuation.initialHoleState).hole =
              (move^[stop] continuation.initialHoleState).hole ∧
            ∀ a b : Nat, a < b -> b < stop ->
              (move^[a] continuation.initialHoleState).hole ≠
                (move^[b] continuation.initialHoleState).hole) := by
  obtain ⟨block, _hstrict⟩ := hresidual.exists_block
  refine ⟨block, ?_⟩
  rcases block.closed_or_crossing with hclosed |
      ⟨source, token, hincident, hsource, index, htoken⟩
  · left
    exact ⟨hclosed,
      block.exists_smallerComplementMinimalTightProblem hclosed hdeficit⟩
  · right
    let hgeometric := block.geometricCrossing_of_crossing
      source token hincident hsource index htoken
    exact ⟨hgeometric, hgeometric.exists_crossingContinuation⟩


theorem
    CanonicalStableRawTightChargeOrbit.HasRetainedSharedTokenOutput.local_or_directOrbit
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
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    {orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources}
    (houtput : orbit.HasRetainedSharedTokenOutput)
    (herase : ∀ source ∈ sources,
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (sources.erase source) =
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources) :
    orbit.LocalMergerDischarge ∨ orbit.HasDirectOrbitDischarge := by
  rcases houtput.local_or_firstDirectStep herase with hlocal |
      ⟨_houtput, source, _q, _first, second, _hsourceNe, _hfirstSecond,
        _hfirst, _hsecond, hstep⟩
  · exact Or.inl hlocal
  · exact Or.inr ⟨source, second, hstep,
      exists_canonicalStableRawComponentDirect_terminal_or_balancedBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component second⟩


theorem
    CanonicalStableRawTightChargeOrbit.HasFreshInternalChordOutput.local_or_directOrbit
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
    {sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)}
    {orbit : CanonicalStableRawTightChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources}
    (houtput : orbit.HasFreshInternalChordOutput)
    (herase : ∀ source ∈ sources,
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (sources.erase source) =
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources) :
    orbit.LocalMergerDischarge ∨ orbit.HasDirectOrbitDischarge := by
  rcases houtput.local_or_firstDirectStep herase with hlocal |
      ⟨_houtput, q, _r, _first, second, _hqr, _hfirstSecond,
        _hfirst, _hsecond, hstep⟩
  · exact Or.inl hlocal
  · exact Or.inr ⟨orbit.states q, second, hstep,
      exists_canonicalStableRawComponentDirect_terminal_or_balancedBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component second⟩


theorem
    exists_canonicalStableRawComponent_maximalOrbitDischarge_of_deficit
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (hdeficit : Fintype.card (CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) <
        Fintype.card (CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    ∃ sources : Finset (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component),
      sources.Nonempty ∧
      (canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources).card +
          1 = sources.card ∧
      (∀ source ∈ sources,
        canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component
              (sources.erase source) =
          canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∧
      (∀ smaller : Finset (CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component),
        smaller ⊂ sources ->
          smaller.card ≤
            (canonicalStableRawComponentIncidentNeighborhood
              ends m j k l zero hloop hjk hkl hk0 p hno component
                smaller).card) ∧
      ∃ orbit : CanonicalStableRawTightChargeOrbit
          ends m j k l zero hloop hjk hkl hk0 p hno component sources,
        2 ≤ orbit.size ∧
        (orbit.HasRetainedSharedTokenOutput ∨
          orbit.HasFreshInternalChordOutput ∨
          (∃ source : ↑sources,
            ∃ u : CanonicalStableRawExceptionalEdge
                ends m j k l zero hloop hjk hkl hk0 p,
              canonicalStableRawTokenComponent
                    ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧
                canonicalStableRawSourceRank ends m j k l zero p u.source <
                  canonicalStableRawSourceRank ends m j k l zero p
                    source.1.1.source) ∨
          orbit.LocalMergerDischarge) := by
  classical
  obtain ⟨sources, hnonempty, htight, herase, hproper⟩ :=
    exists_canonicalStableRawComponent_minimalIncidentObstruction_of_deficit
      ends m j k l zero hloop hjk hkl hk0 p hno component hdeficit
  obtain ⟨orbit, hsize, hmax⟩ :=
    exists_canonicalStableRawTightComponent_sizeMaximalChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources htight
  exact ⟨sources, hnonempty, htight, herase, hproper, orbit, hsize,
    orbit.maximalSaturationStep_localDischarge hmax herase htight⟩


theorem
    exists_canonicalStableRawComponent_maximalOrbitSharpDischarge_of_deficit
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (hdeficit : Fintype.card (CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) <
        Fintype.card (CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    ∃ sources : Finset (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component),
      sources.Nonempty ∧
      (canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources).card +
          1 = sources.card ∧
      (∀ source ∈ sources,
        canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component
              (sources.erase source) =
          canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∧
      (∀ smaller : Finset (CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component),
        smaller ⊂ sources ->
          smaller.card ≤
            (canonicalStableRawComponentIncidentNeighborhood
              ends m j k l zero hloop hjk hkl hk0 p hno component
                smaller).card) ∧
      ∃ orbit : CanonicalStableRawTightChargeOrbit
          ends m j k l zero hloop hjk hkl hk0 p hno component sources,
        2 ≤ orbit.size ∧
        ((∃ source : ↑sources,
            ∃ u : CanonicalStableRawExceptionalEdge
                ends m j k l zero hloop hjk hkl hk0 p,
              canonicalStableRawTokenComponent
                    ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧
                canonicalStableRawSourceRank ends m j k l zero p u.source <
                  canonicalStableRawSourceRank ends m j k l zero p
                    source.1.1.source) ∨
          orbit.LocalMergerDischarge ∨ orbit.HasDirectOrbitDischarge) := by
  classical
  obtain ⟨sources, hnonempty, htight, herase, hproper⟩ :=
    exists_canonicalStableRawComponent_minimalIncidentObstruction_of_deficit
      ends m j k l zero hloop hjk hkl hk0 p hno component hdeficit
  obtain ⟨orbit, hsize, hmax⟩ :=
    exists_canonicalStableRawTightComponent_sizeMaximalChargeOrbit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources htight
  rcases orbit.maximalSaturationStep_sharp hmax herase htight with
    hretained | hrank | hlocal
  · rcases hretained.local_or_directOrbit herase with hlocal | horbit
    · exact ⟨sources, hnonempty, htight, herase, hproper, orbit, hsize,
        Or.inr (Or.inl hlocal)⟩
    · exact ⟨sources, hnonempty, htight, herase, hproper, orbit, hsize,
        Or.inr (Or.inr horbit)⟩
  · exact ⟨sources, hnonempty, htight, herase, hproper, orbit, hsize,
      Or.inl hrank⟩
  · exact ⟨sources, hnonempty, htight, herase, hproper, orbit, hsize,
      Or.inr (Or.inl hlocal)⟩


theorem
    exists_canonicalStableRawComponent_maximalOrbitResidualDischarge_of_deficit
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    [DecidableEq (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)]
    (hdeficit : Fintype.card (CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) <
        Fintype.card (CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component)) :
    ∃ sources : Finset (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component),
      sources.Nonempty ∧
      (canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources).card +
          1 = sources.card ∧
      (∀ source ∈ sources,
        canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component
              (sources.erase source) =
          canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∧
      (∀ smaller : Finset (CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component),
        smaller ⊂ sources ->
          smaller.card ≤
            (canonicalStableRawComponentIncidentNeighborhood
              ends m j k l zero hloop hjk hkl hk0 p hno component
                smaller).card) ∧
      ∃ orbit : CanonicalStableRawTightChargeOrbit
          ends m j k l zero hloop hjk hkl hk0 p hno component sources,
        2 ≤ orbit.size ∧
        ((∃ source : ↑sources,
            ∃ u : CanonicalStableRawExceptionalEdge
                ends m j k l zero hloop hjk hkl hk0 p,
              canonicalStableRawTokenComponent
                    ends m j k l zero hloop hjk hkl hk0 p hno u = component ∧
                canonicalStableRawSourceRank ends m j k l zero p u.source <
                  canonicalStableRawSourceRank ends m j k l zero p
                    source.1.1.source) ∨
          orbit.LocalMergerDischarge ∨
          Nonempty (CanonicalStableRawComponentRichStrictBlock
            ends m j k l zero hloop hjk hkl hk0 p hno component) ∨
          orbit.HasBalancedResidualDeficit) := by
  obtain ⟨sources, hnonempty, htight, herase, hproper, orbit, hsize,
      hrank | hlocal | hdischarge⟩ :=
    exists_canonicalStableRawComponent_maximalOrbitSharpDischarge_of_deficit
      ends m j k l zero hloop hjk hkl hk0 p hno component hdeficit
  · exact ⟨sources, hnonempty, htight, herase, hproper, orbit, hsize,
      Or.inl hrank⟩
  · exact ⟨sources, hnonempty, htight, herase, hproper, orbit, hsize,
      Or.inr (Or.inl hlocal)⟩
  · rcases hdischarge.richStrict_or_balancedResidual
        hdeficit with hrich | hresidual
    · exact ⟨sources, hnonempty, htight, herase, hproper, orbit, hsize,
        Or.inr (Or.inr (Or.inl hrich))⟩
    · exact ⟨sources, hnonempty, htight, herase, hproper, orbit, hsize,
        Or.inr (Or.inr (Or.inr hresidual))⟩

end StatMech.GrahamGHS.FourColor
