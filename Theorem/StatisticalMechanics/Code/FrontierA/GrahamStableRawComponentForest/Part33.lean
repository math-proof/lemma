/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part33
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

theorem CanonicalStableRawComponentRichIncidenceBlock.extend
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (source : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (token : CanonicalStableRawComponentToken
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hsource : ∀ i, source ≠ block.sources i)
    (htoken : ∀ q, token ≠ block.tokens q)
    (hincident : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component source token) :
    ∃ extended : CanonicalStableRawComponentRichIncidenceBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      extended.size = block.size + 1 := by
  obtain ⟨extendedSources, hsourcePrefix, hsourceLast⟩ :=
    finiteEmbedding_snoc block.size block.sources source hsource
  have htokenPrefixFresh : ∀ i, token ≠ block.tokenPrefix i := by
    intro i
    exact htoken i.castSucc
  obtain ⟨balancedTokens, hbalancedPrefix, hbalancedLast⟩ :=
    finiteEmbedding_snoc block.size block.tokenPrefix token htokenPrefixFresh
  let oldExtra := block.tokens (Fin.last block.size)
  have hextraFresh : ∀ q, oldExtra ≠ balancedTokens q := by
    intro q
    refine Fin.lastCases ?_ (fun i => ?_) q
    · rw [hbalancedLast]
      exact (htoken (Fin.last block.size)).symm
    · rw [hbalancedPrefix]
      intro heq
      exact Fin.castSucc_ne_last i (block.tokens.injective heq.symm)
  obtain ⟨extendedTokens, htokenPrefix, htokenLast⟩ :=
    finiteEmbedding_snoc (block.size + 1) balancedTokens oldExtra hextraFresh
  refine ⟨⟨block.size + 1, by omega, extendedSources, extendedTokens, ?_, ?_⟩,
    rfl⟩
  · intro i
    refine Fin.lastCases ?_ (fun q => ?_) i
    · have hsourceEq : extendedSources (Fin.last block.size) = source :=
        hsourceLast
      have htokenEq : extendedTokens (Fin.last block.size).castSucc = token :=
        (htokenPrefix (Fin.last block.size)).trans hbalancedLast
      rw [hsourceEq, htokenEq]
      exact hincident
    · have hsourceEq : extendedSources q.castSucc = block.sources q :=
        hsourcePrefix q
      have htokenEq : extendedTokens q.castSucc.castSucc =
          block.tokens q.castSucc :=
        (htokenPrefix q.castSucc).trans (hbalancedPrefix q)
      rw [hsourceEq, htokenEq]
      exact block.paired q
  · rw [htokenLast]
    exact block.extra_nonexceptional


end StatMech.GrahamGHS.FourColor
