/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Structure.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part6
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

theorem CanonicalStableRawTightChargeOrbit.extendPair
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
      ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (source : ↑sources)
    (token : ↑(canonicalStableRawComponentIncidentNeighborhood
      ends m j k l zero hloop hjk hkl hk0 p hno component sources))
    (hsource : ∀ i, source ≠ orbit.states i)
    (htoken : ∀ i, token ≠ orbit.tokens i)
    (hincident : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component source.1 token.1)
    (horigin : token = canonicalStableRawComponentTightNaturalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component sources source ∨
        token = canonicalStableRawComponentTightSuccessorToken
          ends m j k l zero hloop hjk hkl hk0 p hno component sources source) :
    ∃ extended : CanonicalStableRawTightChargeOrbit
        ends m j k l zero hloop hjk hkl hk0 p hno component sources,
      extended.size = orbit.size + 1 := by
  obtain ⟨extendedStates, hstatePrefix, hstateLast⟩ :=
    finiteEmbedding_snoc (orbit.size + 1) orbit.states source hsource
  obtain ⟨extendedTokens, htokenPrefix, htokenLast⟩ :=
    finiteEmbedding_snoc orbit.size orbit.tokens token htoken
  refine ⟨⟨orbit.size + 1, extendedStates, extendedTokens, ?_,
    orbit.coreSelf.castSucc, orbit.coreDirect.castSucc,
    orbit.coreThird.castSucc, orbit.coreNatural.castSucc,
    orbit.coreFirst.castSucc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩
  · intro i
    refine Fin.lastCases ?_ (fun q => ?_) i
    · have hsucc : (Fin.last orbit.size).succ =
          Fin.last (orbit.size + 1) := by
        apply Fin.ext
        rfl
      rw [hsucc, hstateLast, htokenLast]
      exact hincident
    · have hsucc : q.castSucc.succ = q.succ.castSucc := by
        apply Fin.ext
        rfl
      rw [hsucc, hstatePrefix, htokenPrefix]
      exact orbit.paired q
  · intro i
    refine Fin.lastCases ?_ (fun q => ?_) i
    · have hsucc : (Fin.last orbit.size).succ =
          Fin.last (orbit.size + 1) := by
        apply Fin.ext
        rfl
      rw [hsucc, hstateLast, htokenLast]
      rcases horigin with hnatural | hsuccessor
      · exact Or.inl hnatural
      · exact Or.inr (Or.inl hsuccessor)
    · have hsucc : q.castSucc.succ = q.succ.castSucc := by
        apply Fin.ext
        rfl
      rw [hsucc, hstatePrefix, htokenPrefix]
      rcases orbit.origin q with hnatural | hsuccessor | hcore
      · exact Or.inl hnatural
      · exact Or.inr (Or.inl hsuccessor)
      · exact Or.inr (Or.inr (congrArg Fin.castSucc hcore))
  · intro heq
    exact orbit.coreSelf_ne_direct (Fin.castSucc_inj.mp heq)
  · intro heq
    exact orbit.coreSelf_ne_third (Fin.castSucc_inj.mp heq)
  · intro heq
    exact orbit.coreDirect_ne_third (Fin.castSucc_inj.mp heq)
  · intro heq
    exact orbit.coreNatural_ne_first (Fin.castSucc_inj.mp heq)
  · rw [hstatePrefix, htokenPrefix]
    exact orbit.self_natural
  · rw [hstatePrefix, htokenPrefix]
    exact orbit.direct_natural
  · rw [hstatePrefix, htokenPrefix]
    exact orbit.self_first
  · rw [hstatePrefix, htokenPrefix]
    exact orbit.third_first


end StatMech.GrahamGHS.FourColor
