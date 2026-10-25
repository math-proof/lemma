/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part47
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

theorem exists_canonicalStableRawComponent_sizeMaximal_closed_or_localized
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (start : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    ∃ block : CanonicalStableRawComponentRichIncidenceBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      (∀ other : CanonicalStableRawComponentRichIncidenceBlock
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        other.size ≤ block.size) ∧
      (block.IsClosed ∨ block.HasLocalizedObstruction) := by
  obtain ⟨block, hmax⟩ :=
    exists_canonicalStableRawComponent_sizeMaximalRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component start
  refine ⟨block, hmax, ?_⟩
  rcases block.closureStep_localized with
    hclosed | ⟨extended, hextended⟩ | hterminal | hdirect | hcollision
  · exact Or.inl hclosed
  · exact False.elim (by
      have hle := hmax extended
      omega)
  · exact Or.inr (Or.inl hterminal)
  · exact Or.inr (Or.inr (Or.inl hdirect))
  · exact Or.inr (Or.inr (Or.inr hcollision))


theorem
    CanonicalStableRawComponentRichIncidenceBlock.HasLocalizedObstruction.extension_or_pivot
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
    (hobstruction : block.HasLocalizedObstruction) :
    (∃ extended : CanonicalStableRawComponentRichIncidenceBlock
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        extended.size = block.size + 1) ∨
      ∃ source : CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        (∀ i, source ≠ block.sources i) ∧
        ∃ index : Fin block.size,
          CanonicalStableRawComponentIncident
            ends m j k l zero hloop hjk hkl hk0 p hno component source
              (block.tokens index.castSucc) := by
  rcases hobstruction with hterminal | hdirect | hcollision
  · obtain ⟨source, hsource, terminal, _hterminal, q, hnatural⟩ := hterminal
    have hnaturalIncident : CanonicalStableRawComponentIncident
        ends m j k l zero hloop hjk hkl hk0 p hno component source
          (canonicalStableRawComponentNaturalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component source) :=
      canonicalStableRawComponentNaturalToken_incident
        ends m j k l zero hloop hjk hkl hk0 p hno component source
    by_cases hq : q = Fin.last block.size
    · rcases block.extendBySuccessor_or_repeat source hsource with
        hextended | ⟨r, hsuccessor⟩
      · exact Or.inl hextended
      · have hr : r ≠ Fin.last block.size := by
          intro hr
          apply canonicalStableRawComponentSuccessorToken_ne_natural
            ends m j k l zero hloop hjk hkl hk0 p hno component source
          exact hsuccessor.trans
            ((congrArg block.tokens (hr.trans hq.symm)).trans hnatural.symm)
        obtain ⟨index, hindex⟩ :=
          exists_fin_castSucc_eq_of_ne_last r hr
        right
        refine ⟨source, hsource, index, ?_⟩
        rw [hindex, ← hsuccessor]
        exact canonicalStableRawComponentSuccessorToken_incident
          ends m j k l zero hloop hjk hkl hk0 p hno component source
    · obtain ⟨index, hindex⟩ :=
        exists_fin_castSucc_eq_of_ne_last q hq
      right
      refine ⟨source, hsource, index, ?_⟩
      rw [hindex, ← hnatural]
      exact hnaturalIncident
  · obtain ⟨source, _direct, _hdirect, hsource, q, r, hqr,
        hnatural, hsuccessor⟩ := hdirect
    obtain ⟨index, hindex | hindex⟩ :=
      exists_fin_castSucc_eq_left_or_right_of_ne q r hqr
    · right
      refine ⟨source, hsource, index, ?_⟩
      rw [hindex, ← hnatural]
      exact canonicalStableRawComponentNaturalToken_incident
        ends m j k l zero hloop hjk hkl hk0 p hno component source
    · right
      refine ⟨source, hsource, index, ?_⟩
      rw [hindex, ← hsuccessor]
      exact canonicalStableRawComponentSuccessorToken_incident
        ends m j k l zero hloop hjk hkl hk0 p hno component source
  · obtain ⟨source, collision, hself, hsource, _q, r, s, hrs,
        _hnatural, hsourceToken, hownerToken⟩ := hcollision
    obtain ⟨index, hindex | hindex⟩ :=
      exists_fin_castSucc_eq_left_or_right_of_ne r s hrs
    · right
      refine ⟨source, hsource, index, ?_⟩
      rw [hindex, ← hsourceToken]
      apply (canonicalStableRawWitnessedStateTokenIncidence_iff
        ends m j k l zero hloop hjk hkl hk0 p _ source.1).2
      rw [hself]
      exact canonicalStableRawReferenceSourceLeftToken_stateTokenIncidence
        ends m j k l zero hloop hjk hkl hk0 p
          collision.1.1.1 collision.1.1.2.2
    · right
      refine ⟨source, hsource, index, ?_⟩
      rw [hindex, ← hownerToken]
      apply (canonicalStableRawWitnessedStateTokenIncidence_iff
        ends m j k l zero hloop hjk hkl hk0 p _ source.1).2
      rw [hself]
      exact canonicalStableRawReferenceOwnerLeftToken_stateTokenIncidence
        ends m j k l zero hloop hjk hkl hk0 p
          collision.1.1.1 collision.1.1.2.2


theorem
    CanonicalStableRawComponentRichIncidenceBlock.HasLocalizedObstruction.pivot_of_sizeMaximal
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
    (hmax : ∀ other : CanonicalStableRawComponentRichIncidenceBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      other.size ≤ block.size)
    (hobstruction : block.HasLocalizedObstruction) :
    ∃ source : CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      ∃ hsource : ∀ i, source ≠ block.sources i,
        ∃ index : Fin block.size,
          ∃ hincident : CanonicalStableRawComponentIncident
            ends m j k l zero hloop hjk hkl hk0 p hno component source
              (block.tokens index.castSucc),
            (∀ other, block.sources index ≠
              (block.pivot source hsource index hincident).sources other) := by
  rcases hobstruction.extension_or_pivot block with
    ⟨extended, hextended⟩ | ⟨source, hsource, index, hincident⟩
  · have hle := hmax extended
    omega
  · exact ⟨source, hsource, index, hincident,
      block.pivot_displaced_fresh source hsource index hincident⟩


theorem
    CanonicalStableRawComponentRichIncidenceBlock.PivotConfiguration.exists_step_of_not_closed
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
    (hmax : ∀ other : CanonicalStableRawComponentRichIncidenceBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      other.size ≤ block.size)
    (config : block.PivotConfiguration)
    (hnotClosed : ¬ config.toBlock.IsClosed) :
    ∃ next : block.PivotConfiguration, config.Step next ∧ next ≠ config := by
  let current := config.toBlock
  have hmaxCurrent : ∀ other : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component,
      other.size ≤ current.size := by
    intro other
    simpa only [current,
      CanonicalStableRawComponentRichIncidenceBlock.PivotConfiguration.toBlock]
      using hmax other
  have hobstruction : current.HasLocalizedObstruction := by
    rcases current.closureStep_localized with
      hclosed | ⟨extended, hextended⟩ | hterminal | hdirect | hcollision
    · exact False.elim (hnotClosed hclosed)
    · have hle := hmax extended
      dsimp only [current,
        CanonicalStableRawComponentRichIncidenceBlock.PivotConfiguration.toBlock]
        at hextended
      exact False.elim (by omega)
    · exact Or.inl hterminal
    · exact Or.inr (Or.inl hdirect)
    · exact Or.inr (Or.inr hcollision)
  obtain ⟨source, hsource, index, hincident, _hdisplaced⟩ :=
    hobstruction.pivot_of_sizeMaximal current hmaxCurrent
  let pivoted := current.pivot source hsource index hincident
  let next : block.PivotConfiguration := ⟨pivoted.sources, pivoted.paired⟩
  refine ⟨next, ?_, ?_⟩
  · exact ⟨source, hsource, index, hincident, rfl⟩
  · intro heq
    have hvalue := congrArg
      (fun candidate : block.PivotConfiguration => candidate.1 index) heq
    apply hsource index
    exact (finiteEmbedding_replaceAt_same
      config.1 source hsource index).symm.trans hvalue


theorem
    CanonicalStableRawComponentRichIncidenceBlock.PivotConfiguration.Step.outputClassification
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {block : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component}
    {current next : block.PivotConfiguration}
    (hstep : current.Step next) :
    ∃ source : CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      ∃ hsource : ∀ i, source ≠ current.1 i,
        ∃ index : Fin block.size,
          next.1 = finiteEmbedding_replaceAt
              current.1 source hsource index ∧
          ((∃ u : CanonicalStableRawExceptionalEdge
                ends m j k l zero hloop hjk hkl hk0 p,
              u.target = canonicalStableRawLeftTokenTarget
                  ends m j k l zero hloop hjk hkl hk0 p
                    (block.tokens index.castSucc).1 ∧
              CanonicalStableRawOwnerStableOutput
                  ends m j k l zero hloop hjk hkl hk0 p source.1 u ∧
              canonicalStableRawTokenComponent
                  ends m j k l zero hloop hjk hkl hk0 p hno u = component) ∨
            ∃ u : CanonicalStableRawExceptionalEdge
                ends m j k l zero hloop hjk hkl hk0 p,
              u.target = canonicalStableRawLeftTokenTarget
                  ends m j k l zero hloop hjk hkl hk0 p
                    (block.tokens index.castSucc).1 ∧
              CanonicalStableRawOwnerAdvancingOutput
                  ends m j k l zero hloop hjk hkl hk0 p source.1 u ∧
              canonicalStableRawTokenComponent
                  ends m j k l zero hloop hjk hkl hk0 p hno u = component) := by
  obtain ⟨source, hsource, index, hincident, hnext⟩ := hstep
  have holdIncident : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component
        (current.1 index) (block.tokens index.castSucc) := current.2 index
  have hclassification :=
    canonicalStableRawWitnessedStateTokenIncidence_sharedTokenClassification
      ends m j k l zero hloop hjk hkl hk0 p hno
        (block.tokens index.castSucc).1 source.1 (current.1 index).1
          hincident holdIncident
  refine ⟨source, hsource, index, hnext, ?_⟩
  rcases hclassification with heq | ⟨u, htarget, hstable, hcomponent, _⟩ |
      ⟨u, htarget, hadvancing, hcomponent, _⟩
  · exact False.elim (hsource index (Subtype.ext heq))
  · exact Or.inl ⟨u, htarget, hstable, hcomponent.trans source.2⟩
  · exact Or.inr ⟨u, htarget, hadvancing, hcomponent.trans source.2⟩


theorem
    CanonicalStableRawComponentRichIncidenceBlock.exists_rankSumMaximalPivotConfiguration
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    (block : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component) :
    ∃ best : block.PivotConfiguration,
      ∀ other : block.PivotConfiguration, other.rankSum ≤ best.rankSum := by
  classical
  letI : Finite block.PivotConfiguration := Finite.of_injective
    (fun config : block.PivotConfiguration => config.1)
    (by
      intro first second heq
      exact Subtype.ext heq)
  letI : Fintype block.PivotConfiguration := Fintype.ofFinite _
  letI : Nonempty block.PivotConfiguration := ⟨block.basePivotConfiguration⟩
  exact exists_fintype_score_maximal
    CanonicalStableRawComponentRichIncidenceBlock.PivotConfiguration.rankSum


theorem
    CanonicalStableRawComponentRichIncidenceBlock.PivotConfiguration.Step.enteringRank_le_displaced_of_rankSumMaximal
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
    {hjk : j ≠ k} {hkl : k ≠ l} {hk0 : k ≠ zero}
    {p : Finset I × Finset I}
    {hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p}
    {component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p)}
    {block : CanonicalStableRawComponentRichIncidenceBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component}
    {current next : block.PivotConfiguration}
    (hmax : ∀ other : block.PivotConfiguration,
      other.rankSum ≤ current.rankSum)
    (hstep : current.Step next) :
    ∃ source : CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      ∃ index : Fin block.size,
        canonicalStableRawSourceRank ends m j k l zero p source.1.source ≤
          canonicalStableRawSourceRank ends m j k l zero p
            (current.1 index).1.source := by
  classical
  obtain ⟨source, hsource, index, _hincident, hnext⟩ := hstep
  let oldRank := fun i : Fin block.size =>
    canonicalStableRawSourceRank ends m j k l zero p
      (current.1 i).1.source
  let newRank := fun i : Fin block.size =>
    canonicalStableRawSourceRank ends m j k l zero p
      (next.1 i).1.source
  let rest := ∑ i ∈ (Finset.univ.erase index), oldRank i
  have hnewIndex : newRank index =
      canonicalStableRawSourceRank ends m j k l zero p source.1.source := by
    dsimp only [newRank]
    rw [hnext, finiteEmbedding_replaceAt_same]
  have hrest : (∑ i ∈ (Finset.univ.erase index), newRank i) = rest := by
    apply Finset.sum_congr rfl
    intro i hi
    have hine : i ≠ index := Finset.ne_of_mem_erase hi
    dsimp only [newRank, oldRank]
    rw [hnext, finiteEmbedding_replaceAt_ne
      current.1 source hsource index i hine]
  have holdSum : current.rankSum = rest + oldRank index := by
    change (∑ i, oldRank i) = rest + oldRank index
    simpa only [rest] using
      (Finset.sum_erase_add Finset.univ oldRank
        (Finset.mem_univ index)).symm
  have hnewSum : next.rankSum = rest +
      canonicalStableRawSourceRank ends m j k l zero p source.1.source := by
    change (∑ i, newRank i) = rest +
      canonicalStableRawSourceRank ends m j k l zero p source.1.source
    calc
      (∑ i, newRank i) =
          (∑ i ∈ Finset.univ.erase index, newRank i) + newRank index :=
        (Finset.sum_erase_add Finset.univ newRank
          (Finset.mem_univ index)).symm
      _ = rest + newRank index := by rw [hrest]
      _ = rest + canonicalStableRawSourceRank
          ends m j k l zero p source.1.source := by rw [hnewIndex]
  have hle := hmax next
  rw [holdSum, hnewSum] at hle
  have hrank : canonicalStableRawSourceRank
      ends m j k l zero p source.1.source ≤ oldRank index := by
    omega
  exact ⟨source, index, by simpa only [oldRank] using hrank⟩


theorem
    CanonicalStableRawComponentRichIncidenceBlock.closedConfiguration_or_pivotCycle
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
    (hmax : ∀ other : CanonicalStableRawComponentRichIncidenceBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      other.size ≤ block.size) :
    (∃ config : block.PivotConfiguration, config.toBlock.IsClosed) ∨
      ∃ size : Nat, 1 < size ∧
        ∃ cycle : Fin size ↪ block.PivotConfiguration,
          ∃ σ : Equiv.Perm (Fin size),
      ∀ i, (cycle i).Step (cycle (σ i)) := by
  classical
  letI : Finite block.PivotConfiguration := Finite.of_injective
    (fun config : block.PivotConfiguration => config.1)
    (by
      intro first second heq
      exact Subtype.ext heq)
  letI : Fintype block.PivotConfiguration := Fintype.ofFinite _
  by_cases hclosed : ∃ config : block.PivotConfiguration,
      config.toBlock.IsClosed
  · exact Or.inl hclosed
  · have hnotClosed : ∀ config : block.PivotConfiguration,
        ¬ config.toBlock.IsClosed := by
      intro config hconfig
      exact hclosed ⟨config, hconfig⟩
    let next : block.PivotConfiguration -> block.PivotConfiguration :=
      fun config => Classical.choose
        (config.exists_step_of_not_closed block hmax (hnotClosed config))
    have hnextStep : ∀ config : block.PivotConfiguration,
        config.Step (next config) := by
      intro config
      exact (Classical.choose_spec
        (config.exists_step_of_not_closed block hmax
          (hnotClosed config))).1
    have hnextNe : ∀ config : block.PivotConfiguration,
        next config ≠ config := by
      intro config
      exact (Classical.choose_spec
        (config.exists_step_of_not_closed block hmax
          (hnotClosed config))).2
    obtain ⟨size, hsize, cycle, σ, hcycle⟩ :=
      exists_function_cycleEmbedding next block.basePivotConfiguration
    have hsizeTwo : 1 < size := by
      have hsizeNe : size ≠ 1 := by
        intro hsizeOne
        have hnonempty : Nonempty (Fin size) := Fin.pos_iff_nonempty.mp hsize
        let i : Fin size := hnonempty.some
        have hsigma : σ i = i := by
          apply Fin.ext
          have hsigmaBound := (σ i).2
          have hiBound := i.2
          omega
        apply hnextNe (cycle i)
        calc
          next (cycle i) = cycle (σ i) := (hcycle i).symm
          _ = cycle i := congrArg cycle hsigma
      omega
    right
    refine ⟨size, hsizeTwo, cycle, σ, ?_⟩
    intro i
    rw [hcycle i]
    exact hnextStep (cycle i)


theorem
    canonicalStableRawComponent_referenceOwner_eq_selfOwnerReroute_of_sourceNormalized
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (state : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hself : state.1 = collision.1.1.1)
    (hnormalized :
      canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component collision =
        canonicalStableRawComponentNaturalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component state) :
    (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component collision).1 =
      canonicalStableRawSelfOwnerRerouteLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno
          collision.1.1.1 collision.1.1.2.2 := by
  have hraw := congrArg Subtype.val hnormalized
  change canonicalStableRawReferenceSourceLeftToken
      ends m j k l zero hloop hjk hkl hk0 p
        collision.1.1.1 collision.1.1.2.2 =
    canonicalStableRawStateLeftToken
      ends m j k l zero hloop hjk hkl hk0 p hno state.1 at hraw
  rw [hself] at hraw
  unfold canonicalStableRawStateLeftToken at hraw
  rw [dif_pos collision.1.1.2.2] at hraw
  exact canonicalStableRawReferenceOwnerLeftToken_eq_selfOwnerReroute
    ends m j k l zero hloop hjk hkl hk0 p hno
      collision.1.1.1 collision.1.1.2.2 hraw


theorem
    canonicalStableRawComponent_referenceOwner_eq_successor_of_sourceNormalized
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hno : CanonicalStableRawNoOpposingCuts
      ends m j k l zero hloop hjk hkl hk0 p)
    (component : Set (CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p))
    (state : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hself : state.1 = collision.1.1.1)
    (hnormalized :
      canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component collision =
        canonicalStableRawComponentNaturalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component state) :
    canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component collision =
      canonicalStableRawComponentSuccessorToken
        ends m j k l zero hloop hjk hkl hk0 p hno component state := by
  apply Subtype.ext
  have howner :=
    canonicalStableRawComponent_referenceOwner_eq_selfOwnerReroute_of_sourceNormalized
      ends m j k l zero hloop hjk hkl hk0 p hno component state collision
        hself hnormalized
  have hstateSelf : state.1.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p state.1.source := by
    rw [hself]
    exact collision.1.1.2.2
  unfold canonicalStableRawComponentSuccessorToken
  rw [dif_pos hstateSelf]
  simpa only [hself] using howner


theorem canonicalStableRawComponent_sourceNormalized_terminal_or_advancing
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
    (external : ↑sources)
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hself : external.1.1 = collision.1.1.1)
    (hnormalized :
      canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component collision =
        canonicalStableRawComponentNaturalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component external.1) :
    (∃ terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨
      CanonicalStableRawOwnerAdvancingStep
        ends m j k l zero hloop hjk hkl hk0 p hno collision.1.1.1 := by
  rcases canonicalStableRawComponentCrossCollision_stable_or_advancing
      ends m j k l zero hloop hjk hkl hk0 p hno component collision with
    hstable | hadvancing
  · left
    let owner := canonicalStableRawComponentReferenceOwnerCollisionEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component collision
    have hownerMem : owner ∈ canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources :=
      canonicalStableRawComponent_referenceOwnerCollision_mem_tightNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources
          external collision hself
    have hownerEq : owner.1 = canonicalStableRawSelfOwnerRerouteLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno
          collision.1.1.1 collision.1.1.2.2 :=
      canonicalStableRawComponent_referenceOwner_eq_selfOwnerReroute_of_sourceNormalized
        ends m j k l zero hloop hjk hkl hk0 p hno component external.1
          collision hself hnormalized
    have hnonexceptional : ¬ CanonicalStableRawLeftTokenIsExceptional
        ends m j k l zero hloop hjk hkl hk0 p owner.1 := by
      rw [hownerEq]
      exact canonicalStableRawSelfOwnerReroute_not_exceptional_of_ownerStable
        ends m j k l zero hloop hjk hkl hk0 p hno
          collision.1.1.1 collision.1.1.2.2 hstable
    exact ⟨⟨owner, hnonexceptional⟩, hownerMem⟩
  · exact Or.inr hadvancing


theorem
    canonicalStableRawComponentTightSuccessorOther_normalizedAdvancingEdge
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
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (herase : ∀ source ∈ sources,
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (sources.erase source) =
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (state : ↑sources)
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hself : state.1.1 = collision.1.1.1)
    (hnormalized :
      canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component collision =
        canonicalStableRawComponentNaturalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component state.1)
    (hadvancing : CanonicalStableRawOwnerAdvancingStep
      ends m j k l zero hloop hjk hkl hk0 p hno collision.1.1.1) :
    let next := canonicalStableRawComponentTightSuccessorOther
      ends m j k l zero hloop hjk hkl hk0 p hno component sources herase
    ∃ direct : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
      canonicalStableRawComponentForestStep
          ends m j k l zero hloop hjk hkl hk0 p hno component state.1 =
        Sum.inl direct ∧
      canonicalStableRawComponentReferenceOwnerCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component collision =
        canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component direct ∧
      CanonicalStableRawComponentIncident
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (next state).1
            (canonicalStableRawComponentDirectEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component direct) ∧
      canonicalStableRawSourceRank ends m j k l zero p direct.1.source <
        canonicalStableRawSourceRank ends m j k l zero p
          collision.1.1.1.source := by
  classical
  dsimp only
  let self := collision.1.1
  let selfState : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component :=
    ⟨self.1, self.2.1⟩
  have hstate : state.1 = selfState := by
    apply Subtype.ext
    exact hself
  let hexceptional :=
    canonicalStableRawComponentSuccessorToken_exceptional_of_advancing
      ends m j k l zero hloop hjk hkl hk0 p hno component self hadvancing
  let direct := canonicalStableRawComponentExceptionalSuccessorDirect
    ends m j k l zero hloop hjk hkl hk0 p hno component
      selfState hexceptional
  have hstepSelf : canonicalStableRawComponentForestStep
        ends m j k l zero hloop hjk hkl hk0 p hno component selfState =
      Sum.inl direct := by
    unfold canonicalStableRawComponentForestStep
    rw [dif_pos hexceptional]
  have hstep : canonicalStableRawComponentForestStep
        ends m j k l zero hloop hjk hkl hk0 p hno component state.1 =
      Sum.inl direct := by
    rw [hstate]
    exact hstepSelf
  have hdirectSuccessor :
      canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component direct =
        canonicalStableRawComponentSuccessorToken
          ends m j k l zero hloop hjk hkl hk0 p hno component selfState :=
    canonicalStableRawComponentExceptionalSuccessorDirect_natural
      ends m j k l zero hloop hjk hkl hk0 p hno component
        selfState hexceptional
  have hownerSuccessor :=
    canonicalStableRawComponent_referenceOwner_eq_successor_of_sourceNormalized
      ends m j k l zero hloop hjk hkl hk0 p hno component state.1
        collision hself hnormalized
  have hownerDirect :
      canonicalStableRawComponentReferenceOwnerCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component collision =
        canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component direct := by
    rw [hstate] at hownerSuccessor
    exact hownerSuccessor.trans hdirectSuccessor.symm
  let next := canonicalStableRawComponentTightSuccessorOther
    ends m j k l zero hloop hjk hkl hk0 p hno component sources herase
  have hnext := canonicalStableRawComponentTightSuccessorOther_incident
    ends m j k l zero hloop hjk hkl hk0 p hno component sources herase state
  have hnextDirect : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component
        (next state).1
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component direct) := by
    change CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component
        (next state).1
        (canonicalStableRawComponentSuccessorToken
          ends m j k l zero hloop hjk hkl hk0 p hno component state.1) at hnext
    rw [hstate, ← hdirectSuccessor] at hnext
    exact hnext
  have hrank : canonicalStableRawSourceRank ends m j k l zero p
        direct.1.source <
      canonicalStableRawSourceRank ends m j k l zero p self.1.source :=
    canonicalStableRawComponentExceptionalSuccessorDirect_rank_lt_of_advancing
      ends m j k l zero hloop hjk hkl hk0 p hno component self hadvancing
  exact ⟨direct, hstep, hownerDirect, hnextDirect, hrank⟩


theorem
    canonicalStableRawComponentTightSuccessorOther_normalizedAdvancingSplit
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
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (herase : ∀ source ∈ sources,
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (sources.erase source) =
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (state : ↑sources)
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hself : state.1.1 = collision.1.1.1)
    (hnormalized :
      canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component collision =
        canonicalStableRawComponentNaturalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component state.1)
    (hadvancing : CanonicalStableRawOwnerAdvancingStep
      ends m j k l zero hloop hjk hkl hk0 p hno collision.1.1.1) :
    let next := canonicalStableRawComponentTightSuccessorOther
      ends m j k l zero hloop hjk hkl hk0 p hno component sources herase
    canonicalStableRawSourceRank ends m j k l zero p (next state).1.1.source <
        canonicalStableRawSourceRank ends m j k l zero p
          collision.1.1.1.source ∨
      ∃ direct : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        CanonicalStableRawOwnerAdvancingOutput
          ends m j k l zero hloop hjk hkl hk0 p (next state).1.1 direct.1 ∧
        Nonempty (StatMech.FrontierA.crossCollision
          (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component)
          (canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component)) ∧
        CanonicalStableRawComponentIncident
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (next state).1
            (canonicalStableRawComponentDirectEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component direct) ∧
        canonicalStableRawSourceRank ends m j k l zero p direct.1.source <
          canonicalStableRawSourceRank ends m j k l zero p
            collision.1.1.1.source := by
  classical
  dsimp only
  let next := canonicalStableRawComponentTightSuccessorOther
    ends m j k l zero hloop hjk hkl hk0 p hno component sources herase
  obtain ⟨direct, _hstep, hownerDirect, hnextDirect, hrank⟩ :=
    canonicalStableRawComponentTightSuccessorOther_normalizedAdvancingEdge
      ends m j k l zero hloop hjk hkl hk0 p hno component sources herase
        state collision hself hnormalized hadvancing
  have htokenSource :
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component direct).1.1 =
        direct.1.source := by
    change (canonicalStableRawStateLeftToken
      ends m j k l zero hloop hjk hkl hk0 p hno direct.1).1 = direct.1.source
    unfold canonicalStableRawStateLeftToken
    rw [dif_neg direct.2.2]
    unfold canonicalStableRawDirectLeftToken
    rfl
  change CanonicalStableRawWitnessedStateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component direct).1
        (next state).1.1 at hnextDirect
  rcases hnextDirect.1.1 with hsource | howner
  · left
    have hdirectSource : direct.1.source = (next state).1.1.source :=
      htokenSource.symm.trans hsource
    rw [← hdirectSource]
    exact hrank
  · right
    have hownerOutput : CanonicalStableRawOwnerAdvancingOutput
        ends m j k l zero hloop hjk hkl hk0 p (next state).1.1 direct.1 := by
      change direct.1.source.1 = canonicalStableRawPreferredRightBase
        ends m j k l zero hloop hjk hkl hk0 p (next state).1.1.target
      exact congrArg Subtype.val (htokenSource.symm.trans howner)
    let second : StatMech.FrontierA.crossCollision
        (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component) :=
      ⟨(collision, direct), hownerDirect⟩
    exact ⟨direct, hownerOutput, ⟨second⟩, hnextDirect, hrank⟩


theorem
    canonicalStableRawComponentTightSuccessorOther_secondCharge_of_normalizedAdvancing_rankNondrop
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
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (herase : ∀ source ∈ sources,
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (sources.erase source) =
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (state : ↑sources)
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hself : state.1.1 = collision.1.1.1)
    (hnormalized :
      canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component collision =
        canonicalStableRawComponentNaturalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component state.1)
    (hadvancing : CanonicalStableRawOwnerAdvancingStep
      ends m j k l zero hloop hjk hkl hk0 p hno collision.1.1.1)
    (hnondrop :
      let next := canonicalStableRawComponentTightSuccessorOther
        ends m j k l zero hloop hjk hkl hk0 p hno component sources herase
      ¬ canonicalStableRawSourceRank ends m j k l zero p
            (next state).1.1.source <
          canonicalStableRawSourceRank ends m j k l zero p
            collision.1.1.1.source) :
    let next := canonicalStableRawComponentTightSuccessorOther
      ends m j k l zero hloop hjk hkl hk0 p hno component sources herase
    ∃ direct : CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component,
      CanonicalStableRawOwnerAdvancingOutput
          ends m j k l zero hloop hjk hkl hk0 p (next state).1.1 direct.1 ∧
      Nonempty (StatMech.FrontierA.crossCollision
        (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)) ∧
      CanonicalStableRawComponentIncident
        ends m j k l zero hloop hjk hkl hk0 p hno component
          (next state).1
          (canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component direct) ∧
      canonicalStableRawSourceRank ends m j k l zero p direct.1.source <
        canonicalStableRawSourceRank ends m j k l zero p
          collision.1.1.1.source := by
  dsimp only at hnondrop ⊢
  rcases
      canonicalStableRawComponentTightSuccessorOther_normalizedAdvancingSplit
        ends m j k l zero hloop hjk hkl hk0 p hno component sources herase
          state collision hself hnormalized hadvancing with
    hdrop | hexit
  · exact False.elim (hnondrop hdrop)
  · exact hexit


theorem canonicalStableRawComponent_tightState_terminal_or_crossCollision_or_direct
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
    (∃ terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨
      (∃ collision : StatMech.FrontierA.crossCollision
          (canonicalStableRawComponentSelfEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component)
          (canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component),
        state.1.1 = collision.1.1.1 ∧
        canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component
              collision.1.2 ∈
          canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨
      ∃ direct : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        state.1.1 = direct.1 := by
  classical
  let token := canonicalStableRawComponentNaturalToken
    ends m j k l zero hloop hjk hkl hk0 p hno component state.1
  have htokenMem : token ∈ canonicalStableRawComponentIncidentNeighborhood
      ends m j k l zero hloop hjk hkl hk0 p hno component sources :=
    (canonicalStableRawComponentTightNaturalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component sources state).2
  by_cases hself : state.1.1.target.1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p state.1.1.source
  · let self : CanonicalStableRawComponentSelfState
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
      ⟨state.1.1, state.1.2, hself⟩
    by_cases hexceptional : CanonicalStableRawLeftTokenIsExceptional
        ends m j k l zero hloop hjk hkl hk0 p token.1
    · let exceptionalToken : CanonicalStableRawComponentExceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component :=
        ⟨token, hexceptional⟩
      let direct : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component :=
        (canonicalStableRawComponentDirectStateEquivExceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component).symm
            exceptionalToken
      have hdirectToken :
          canonicalStableRawComponentDirectEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component direct =
            token := by
        exact congrArg Subtype.val
          ((canonicalStableRawComponentDirectStateEquivExceptionalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component).apply_symm_apply
              exceptionalToken)
      have hselfToken :
          canonicalStableRawComponentSelfEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component self =
            token := by
        apply Subtype.ext
        change canonicalStableRawStateLeftToken
            ends m j k l zero hloop hjk hkl hk0 p hno self.1 =
          canonicalStableRawStateLeftToken
            ends m j k l zero hloop hjk hkl hk0 p hno state.1.1
        rfl
      let collision : StatMech.FrontierA.crossCollision
          (canonicalStableRawComponentSelfEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component)
          (canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component) :=
        ⟨(self, direct), hselfToken.trans hdirectToken.symm⟩
      exact Or.inr (Or.inl ⟨collision, rfl, hdirectToken ▸ htokenMem⟩)
    · let terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component :=
        ⟨token, hexceptional⟩
      exact Or.inl ⟨terminal, htokenMem⟩
  · let direct : CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
      ⟨state.1.1, state.1.2, hself⟩
    exact Or.inr (Or.inr ⟨direct, rfl⟩)


theorem
    canonicalStableRawComponent_tightCrossCollision_localDischarge
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
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (herase : ∀ source ∈ sources,
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (sources.erase source) =
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (state : ↑sources)
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hself : state.1.1 = collision.1.1.1) :
    (∃ terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨
      Nonempty (Fin 3 ↪
        ↑(canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources)) ∨
      ∃ second : StatMech.FrontierA.crossCollision
          (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component)
          (canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component),
        canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component second.1.2 ∈
          canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component sources := by
  classical
  let naturalToken := canonicalStableRawComponentTightNaturalToken
    ends m j k l zero hloop hjk hkl hk0 p hno component sources state
  let sourceToken :
      ↑(canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources) :=
    ⟨canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component collision,
      canonicalStableRawComponent_referenceSourceCollision_mem_tightNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources
          state collision hself⟩
  let ownerToken :
      ↑(canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources) :=
    ⟨canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component collision,
      canonicalStableRawComponent_referenceOwnerCollision_mem_tightNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources
          state collision hself⟩
  by_cases hnormalizedTight : sourceToken = naturalToken
  · have hnormalized :
        canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component collision =
          canonicalStableRawComponentNaturalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component state.1 :=
      congrArg Subtype.val hnormalizedTight
    rcases canonicalStableRawComponent_sourceNormalized_terminal_or_advancing
        ends m j k l zero hloop hjk hkl hk0 p hno component sources
          state collision hself hnormalized with
      hterminal | hadvancing
    · exact Or.inl hterminal
    · obtain ⟨direct, _hstep, hownerDirect, hincident, _hrank⟩ :=
        canonicalStableRawComponentTightSuccessorOther_normalizedAdvancingEdge
          ends m j k l zero hloop hjk hkl hk0 p hno component sources herase
            state collision hself hnormalized hadvancing
      let second : StatMech.FrontierA.crossCollision
          (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component)
          (canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component) :=
        ⟨(collision, direct), hownerDirect⟩
      right
      right
      refine ⟨second, ?_⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _,
        (canonicalStableRawComponentTightSuccessorOther
          ends m j k l zero hloop hjk hkl hk0 p hno component
            sources herase state).1,
        (canonicalStableRawComponentTightSuccessorOther
          ends m j k l zero hloop hjk hkl hk0 p hno component
            sources herase state).2,
        hincident⟩
  · have hsourceOwner : sourceToken ≠ ownerToken := by
      intro heq
      apply canonicalStableRawComponent_referenceSourceCollision_ne_ownerCollision
        ends m j k l zero hloop hjk hkl hk0 p hno component collision
      exact congrArg Subtype.val heq
    have hnatural : naturalToken.1 =
        canonicalStableRawComponentSelfEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component collision.1.1 := by
      apply Subtype.ext
      change canonicalStableRawStateLeftToken
          ends m j k l zero hloop hjk hkl hk0 p hno state.1.1 =
        canonicalStableRawStateLeftToken
          ends m j k l zero hloop hjk hkl hk0 p hno collision.1.1.1
      rw [hself]
    have hnaturalOwner : naturalToken ≠ ownerToken := by
      intro heq
      apply canonicalStableRawComponentReferenceOwnerCollisionEmbedding_ne_self
        ends m j k l zero hloop hjk hkl hk0 p hno component
          collision collision.1.1
      exact (congrArg Subtype.val heq).symm.trans hnatural
    exact Or.inr (Or.inl
      (finiteEmbedding_three_of_pairwise_ne sourceToken naturalToken ownerToken
        hnormalizedTight hsourceOwner hnaturalOwner))


theorem canonicalStableRawComponent_distinctTightStates_localDischarge
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
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (herase : ∀ source ∈ sources,
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (sources.erase source) =
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (x y : ↑sources) (hne : x ≠ y) :
    (∃ terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨
      Nonempty (Fin 3 ↪
        ↑(canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources)) ∨
      (∃ second : StatMech.FrontierA.crossCollision
          (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component)
          (canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component),
        canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component second.1.2 ∈
          canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨
      ∃ first second : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        first ≠ second ∧ x.1.1 = first.1 ∧ y.1.1 = second.1 := by
  classical
  rcases canonicalStableRawComponent_tightState_terminal_or_crossCollision_or_direct
      ends m j k l zero hloop hjk hkl hk0 p hno component sources x with
    hterminal | ⟨collision, hself, _hdirectMem⟩ | ⟨first, hfirst⟩
  · exact Or.inl hterminal
  · rcases canonicalStableRawComponent_tightCrossCollision_localDischarge
        ends m j k l zero hloop hjk hkl hk0 p hno component sources herase
          x collision hself with hterminal | hthree | hsecond
    · exact Or.inl hterminal
    · exact Or.inr (Or.inl hthree)
    · exact Or.inr (Or.inr (Or.inl hsecond))
  · rcases canonicalStableRawComponent_tightState_terminal_or_crossCollision_or_direct
        ends m j k l zero hloop hjk hkl hk0 p hno component sources y with
      hterminal | ⟨collision, hself, _hdirectMem⟩ | ⟨second, hsecond⟩
    · exact Or.inl hterminal
    · rcases canonicalStableRawComponent_tightCrossCollision_localDischarge
          ends m j k l zero hloop hjk hkl hk0 p hno component sources herase
            y collision hself with hterminal | hthree | hsecondCharge
      · exact Or.inl hterminal
      · exact Or.inr (Or.inl hthree)
      · exact Or.inr (Or.inr (Or.inl hsecondCharge))
    · refine Or.inr (Or.inr (Or.inr ⟨first, second, ?_, hfirst, hsecond⟩))
      intro heq
      apply hne
      apply Subtype.ext
      apply Subtype.ext
      exact hfirst.trans ((congrArg
        (fun direct : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component => direct.1)
            heq).trans hsecond.symm)


theorem
    exists_canonicalStableRawComponent_tightSuccessorCycle_localDischarge
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
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (herase : ∀ source ∈ sources,
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (sources.erase source) =
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (source : CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hsource : source ∈ sources)
    (htight : (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 =
      sources.card)
    (hproper : ∀ smaller : Finset (CanonicalStableRawComponentState
        ends m j k l zero hloop hjk hkl hk0 p hno component),
      smaller ⊂ sources ->
        smaller.card ≤
          (canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component
              smaller).card) :
    (∃ terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨
      ∃ size : Nat, 0 < size ∧
        ∃ cycle : Fin size ↪ ↑sources,
          ∃ directs : Fin size ↪ CanonicalStableRawComponentDirectState
              ends m j k l zero hloop hjk hkl hk0 p hno component,
            ∃ tokens : Fin size ↪
                ↑(canonicalStableRawComponentIncidentNeighborhood
                  ends m j k l zero hloop hjk hkl hk0 p hno component sources),
              ∃ external : ↑sources,
                (∀ q, external ≠ cycle q) ∧
                (∀ i,
                  canonicalStableRawComponentDirectEmbedding
                      ends m j k l zero hloop hjk hkl hk0 p hno component
                        (directs i) = (tokens i).1) ∧
                (Nonempty (Fin (size + 1) ↪
                    ↑(canonicalStableRawComponentIncidentNeighborhood
                      ends m j k l zero hloop hjk hkl hk0 p hno component
                        sources)) ∨
                  (∃ i, external.1.1 = (directs i).1) ∨
                  (∃ terminal : CanonicalStableRawComponentNonexceptionalToken
                        ends m j k l zero hloop hjk hkl hk0 p hno component,
                      terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood
                        ends m j k l zero hloop hjk hkl hk0 p hno component
                          sources) ∨
                  Nonempty (Fin 3 ↪
                    ↑(canonicalStableRawComponentIncidentNeighborhood
                      ends m j k l zero hloop hjk hkl hk0 p hno component
                        sources)) ∨
                  ∃ second : StatMech.FrontierA.crossCollision
                      (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
                        ends m j k l zero hloop hjk hkl hk0 p hno component)
                      (canonicalStableRawComponentDirectEmbedding
                        ends m j k l zero hloop hjk hkl hk0 p hno component),
                    canonicalStableRawComponentDirectEmbedding
                        ends m j k l zero hloop hjk hkl hk0 p hno component
                          second.1.2 ∈
                      canonicalStableRawComponentIncidentNeighborhood
                        ends m j k l zero hloop hjk hkl hk0 p hno component
                          sources) := by
  classical
  rcases exists_canonicalStableRawComponent_tightSuccessorCycle_externalDischarge
      ends m j k l zero hloop hjk hkl hk0 p hno component
        sources source hsource htight hproper with
    hterminal | ⟨size, hsize, cycle, directs, tokens, external,
      hexternal, hdirect, hboundary⟩
  · exact Or.inl hterminal
  · right
    refine ⟨size, hsize, cycle, directs, tokens, external,
      hexternal, hdirect, ?_⟩
    rcases hboundary with hfresh | heq | ⟨collision, hself⟩
    · exact Or.inl hfresh
    · exact Or.inr (Or.inl heq)
    · rcases canonicalStableRawComponent_tightCrossCollision_localDischarge
          ends m j k l zero hloop hjk hkl hk0 p hno component sources herase
            external collision hself with
        hterminal | hthree | hsecond
      · exact Or.inr (Or.inr (Or.inl hterminal))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hthree)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr hsecond)))


theorem
    exists_canonicalStableRawComponent_minimalRankNondropDischarge_of_deficit
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
      ∃ herase : ∀ source ∈ sources,
        canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component
              (sources.erase source) =
          canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component sources,
        sources.Nonempty ∧
        (canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component
              sources).card + 1 = sources.card ∧
        (∀ smaller : Finset (CanonicalStableRawComponentState
            ends m j k l zero hloop hjk hkl hk0 p hno component),
          smaller ⊂ sources ->
            smaller.card ≤
              (canonicalStableRawComponentIncidentNeighborhood
                ends m j k l zero hloop hjk hkl hk0 p hno component
                  smaller).card) ∧
        ∃ state : ↑sources,
          (let next := canonicalStableRawComponentTightSuccessorOther
            ends m j k l zero hloop hjk hkl hk0 p hno component sources herase
          ¬ canonicalStableRawSourceRank ends m j k l zero p
                (next state).1.1.source <
              canonicalStableRawSourceRank ends m j k l zero p
                state.1.1.source) ∧
          ((∃ terminal : CanonicalStableRawComponentNonexceptionalToken
                ends m j k l zero hloop hjk hkl hk0 p hno component,
              terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood
                  ends m j k l zero hloop hjk hkl hk0 p hno component sources ∧
              ∃ size : Nat, 0 < size ∧
                Nonempty (Fin size ↪
                  CanonicalStableRawComponentDirectState
                    ends m j k l zero hloop hjk hkl hk0 p hno component) ∧
                Nonempty (Fin (size + 1) ↪
                  CanonicalStableRawComponentToken
                    ends m j k l zero hloop hjk hkl hk0 p hno component)) ∨
            (∃ collision : StatMech.FrontierA.crossCollision
                (canonicalStableRawComponentSelfEmbedding
                  ends m j k l zero hloop hjk hkl hk0 p hno component)
                (canonicalStableRawComponentDirectEmbedding
                  ends m j k l zero hloop hjk hkl hk0 p hno component),
              state.1.1 = collision.1.1.1 ∧
              canonicalStableRawComponentDirectEmbedding
                    ends m j k l zero hloop hjk hkl hk0 p hno component
                      collision.1.2 ∈
                canonicalStableRawComponentIncidentNeighborhood
                  ends m j k l zero hloop hjk hkl hk0 p hno component
                    sources ∧
              Nonempty (Fin 3 ↪
                ↑(canonicalStableRawComponentIncidentNeighborhood
                  ends m j k l zero hloop hjk hkl hk0 p hno component
                    sources)) ∧
              (let Direct := CanonicalStableRawComponentDirectState
                  ends m j k l zero hloop hjk hkl hk0 p hno component
               let Token := CanonicalStableRawComponentToken
                  ends m j k l zero hloop hjk hkl hk0 p hno component
               let advance := canonicalStableRawComponentDirectForestAdvance
                  ends m j k l zero hloop hjk hkl hk0 p hno component
               (∃ n ≤ Nat.card Direct,
                  ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
                      ends m j k l zero hloop hjk hkl hk0 p hno component,
                    canonicalStableRawComponentForestStep
                        ends m j k l zero hloop hjk hkl hk0 p hno component
                          ⟨(advance^[n] collision.1.2).1,
                            (advance^[n] collision.1.2).2.1⟩ =
                      Sum.inr terminal) ∨
                ∃ size : Nat, 0 < size ∧
                  Nonempty (Fin size ↪ Direct) ∧
                  Nonempty (Fin size ↪ Token))) ∨
            (∃ second : StatMech.FrontierA.crossCollision
                (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
                  ends m j k l zero hloop hjk hkl hk0 p hno component)
                (canonicalStableRawComponentDirectEmbedding
                  ends m j k l zero hloop hjk hkl hk0 p hno component),
              canonicalStableRawComponentDirectEmbedding
                  ends m j k l zero hloop hjk hkl hk0 p hno component
                    second.1.2 ∈
                canonicalStableRawComponentIncidentNeighborhood
                  ends m j k l zero hloop hjk hkl hk0 p hno component
                    sources ∧
              ∃ size : Nat, 0 < size ∧
                Nonempty (Fin size ↪
                  CanonicalStableRawComponentDirectState
                    ends m j k l zero hloop hjk hkl hk0 p hno component) ∧
                Nonempty (Fin (size + 1) ↪
                  CanonicalStableRawComponentToken
                    ends m j k l zero hloop hjk hkl hk0 p hno component)) ∨
            ∃ direct : CanonicalStableRawComponentDirectState
                ends m j k l zero hloop hjk hkl hk0 p hno component,
              state.1.1 = direct.1 ∧
              (let Direct := CanonicalStableRawComponentDirectState
                  ends m j k l zero hloop hjk hkl hk0 p hno component
               let Token := CanonicalStableRawComponentToken
                  ends m j k l zero hloop hjk hkl hk0 p hno component
               let advance := canonicalStableRawComponentDirectForestAdvance
                  ends m j k l zero hloop hjk hkl hk0 p hno component
               (∃ n ≤ Nat.card Direct,
                  ∃ terminal : CanonicalStableRawComponentNonexceptionalToken
                      ends m j k l zero hloop hjk hkl hk0 p hno component,
                    canonicalStableRawComponentForestStep
                        ends m j k l zero hloop hjk hkl hk0 p hno component
                          ⟨(advance^[n] direct).1,
                            (advance^[n] direct).2.1⟩ = Sum.inr terminal) ∨
                ∃ size : Nat, 0 < size ∧
                  Nonempty (Fin size ↪ Direct) ∧
                  Nonempty (Fin size ↪ Token))) := by
  classical
  obtain ⟨sources, herase, hnonempty, htight, hproper, state, hnondrop⟩ :=
    exists_canonicalStableRawComponent_minimalTightRankNondrop_of_deficit
      ends m j k l zero hloop hjk hkl hk0 p hno component hdeficit
  refine ⟨sources, herase, hnonempty, htight, hproper, state, hnondrop, ?_⟩
  have strictOfTerminal
      (terminal : CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) :
      ∃ size : Nat, 0 < size ∧
        Nonempty (Fin size ↪ CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component) ∧
        Nonempty (Fin (size + 1) ↪ CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) := by
    have hdirectGt := canonicalStableRawComponent_direct_card_gt_self_of_deficit
      ends m j k l zero hloop hjk hkl hk0 p hno component hdeficit
    have hdirectPos : 0 < Nat.card (CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component) := by
      omega
    let start : CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
      (Nat.card_pos_iff.mp hdirectPos).1.some
    exact exists_canonicalStableRawComponentDirect_strictTokenBlock_of_available
      ends m j k l zero hloop hjk hkl hk0 p hno component start terminal
  rcases canonicalStableRawComponent_tightState_terminal_or_crossCollision_or_direct
      ends m j k l zero hloop hjk hkl hk0 p hno component sources state with
    hterminal | hcollision | hdirect
  · obtain ⟨terminal, hterminalMem⟩ := hterminal
    exact Or.inl ⟨terminal, hterminalMem, strictOfTerminal terminal⟩
  · obtain ⟨collision, hself, hdirectMem⟩ := hcollision
    rcases canonicalStableRawComponent_tightCrossCollision_localDischarge
        ends m j k l zero hloop hjk hkl hk0 p hno component sources herase
          state collision hself with
      hterminal | hthree | hsecond
    · obtain ⟨terminal, hterminalMem⟩ := hterminal
      exact Or.inl ⟨terminal, hterminalMem, strictOfTerminal terminal⟩
    · refine Or.inr (Or.inl
        ⟨collision, hself, hdirectMem, hthree, ?_⟩)
      exact exists_canonicalStableRawComponentDirect_terminal_or_balancedBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component collision.1.2
    · obtain ⟨second, hsecondMem⟩ := hsecond
      refine Or.inr (Or.inr (Or.inl
        ⟨second, hsecondMem, ?_⟩))
      exact exists_canonicalStableRawComponentSecondCollision_strictTokenBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component second
  · obtain ⟨direct, hstateDirect⟩ := hdirect
    refine Or.inr (Or.inr (Or.inr
      ⟨direct, hstateDirect, ?_⟩))
    exact exists_canonicalStableRawComponentDirect_terminal_or_balancedBlock
      ends m j k l zero hloop hjk hkl hk0 p hno component direct


theorem canonicalStableRawComponent_tightCrossCollision_twoAlternateTokenEmbedding
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
    (external : ↑sources)
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hself : external.1.1 = collision.1.1.1) :
    Nonempty (Fin 2 ↪
      ↑(canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources)) := by
  let sourceToken :
      ↑(canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources) :=
    ⟨canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component collision,
      canonicalStableRawComponent_referenceSourceCollision_mem_tightNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources
          external collision hself⟩
  let ownerToken :
      ↑(canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources) :=
    ⟨canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component collision,
      canonicalStableRawComponent_referenceOwnerCollision_mem_tightNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources
          external collision hself⟩
  let block : Fin 1 ↪
      ↑(canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources) :=
    ⟨fun _ => sourceToken, fun x y _ => Subsingleton.elim x y⟩
  have hfresh : ∀ i, ownerToken ≠ block i := by
    intro i heq
    apply canonicalStableRawComponent_referenceSourceCollision_ne_ownerCollision
      ends m j k l zero hloop hjk hkl hk0 p hno component collision
    exact congrArg Subtype.val heq.symm
  simpa only [Nat.reduceAdd] using
    (finiteEmbedding_add_fresh 1 block ownerToken hfresh)


theorem
    canonicalStableRawComponent_tightCrossCollision_sourceNormalized_or_threeTokens
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
    (external : ↑sources)
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hself : external.1.1 = collision.1.1.1) :
    canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component collision =
        canonicalStableRawComponentNaturalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component external.1 ∨
      Nonempty (Fin 3 ↪
        ↑(canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources)) := by
  classical
  let naturalToken := canonicalStableRawComponentTightNaturalToken
    ends m j k l zero hloop hjk hkl hk0 p hno component sources external
  let sourceToken :
      ↑(canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources) :=
    ⟨canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component collision,
      canonicalStableRawComponent_referenceSourceCollision_mem_tightNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources
          external collision hself⟩
  let ownerToken :
      ↑(canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources) :=
    ⟨canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component collision,
      canonicalStableRawComponent_referenceOwnerCollision_mem_tightNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources
          external collision hself⟩
  by_cases hnormalized : sourceToken = naturalToken
  · left
    exact congrArg Subtype.val hnormalized
  · right
    have hsourceOwner : sourceToken ≠ ownerToken := by
      intro heq
      apply canonicalStableRawComponent_referenceSourceCollision_ne_ownerCollision
        ends m j k l zero hloop hjk hkl hk0 p hno component collision
      exact congrArg Subtype.val heq
    have hnatural : naturalToken.1 =
        canonicalStableRawComponentSelfEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component collision.1.1 := by
      apply Subtype.ext
      change canonicalStableRawStateLeftToken
          ends m j k l zero hloop hjk hkl hk0 p hno external.1.1 =
        canonicalStableRawStateLeftToken
          ends m j k l zero hloop hjk hkl hk0 p hno collision.1.1.1
      rw [hself]
    have hnaturalOwner : naturalToken ≠ ownerToken := by
      intro heq
      apply canonicalStableRawComponentReferenceOwnerCollisionEmbedding_ne_self
        ends m j k l zero hloop hjk hkl hk0 p hno component
          collision collision.1.1
      exact (congrArg Subtype.val heq).symm.trans hnatural
    exact finiteEmbedding_three_of_pairwise_ne sourceToken naturalToken ownerToken
      hnormalized hsourceOwner hnaturalOwner


theorem
    canonicalStableRawComponent_tightCrossCollision_terminal_or_advancing_or_threeTokens
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
    (external : ↑sources)
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hself : external.1.1 = collision.1.1.1) :
    (∃ terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨
      CanonicalStableRawOwnerAdvancingStep
          ends m j k l zero hloop hjk hkl hk0 p hno collision.1.1.1 ∨
        Nonempty (Fin 3 ↪
          ↑(canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component sources)) := by
  rcases
      canonicalStableRawComponent_tightCrossCollision_sourceNormalized_or_threeTokens
        ends m j k l zero hloop hjk hkl hk0 p hno component sources
          external collision hself with
    hnormalized | hthree
  · rcases canonicalStableRawComponent_sourceNormalized_terminal_or_advancing
        ends m j k l zero hloop hjk hkl hk0 p hno component sources
          external collision hself hnormalized with
      hterminal | hadvancing
    · exact Or.inl hterminal
    · exact Or.inr (Or.inl hadvancing)
  · exact Or.inr (Or.inr hthree)


theorem
    canonicalStableRawComponent_tightCrossCollision_terminal_or_strictBlock_or_second
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
    (size : Nat)
    (directs : Fin size ↪ CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (tokens : Fin size ↪
      ↑(canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources))
    (hdirect : ∀ i,
      canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component (directs i) =
        (tokens i).1)
    (external : ↑sources)
    (collision : StatMech.FrontierA.crossCollision
      (canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component)
      (canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component))
    (hself : external.1.1 = collision.1.1.1) :
    (∃ terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨
      Nonempty (Fin (size + 1) ↪
        ↑(canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources)) ∨
      Nonempty (StatMech.FrontierA.crossCollision
        (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)) := by
  classical
  let TightToken := ↑(canonicalStableRawComponentIncidentNeighborhood
    ends m j k l zero hloop hjk hkl hk0 p hno component sources)
  let first := canonicalStableRawComponentReferenceOwnerCollisionEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component collision
  have hfirst : first ∈ canonicalStableRawComponentIncidentNeighborhood
      ends m j k l zero hloop hjk hkl hk0 p hno component sources :=
    canonicalStableRawComponent_referenceOwnerCollision_mem_tightNeighborhood
      ends m j k l zero hloop hjk hkl hk0 p hno component
        sources external collision hself
  let tightFirst : TightToken := ⟨first, hfirst⟩
  by_cases hexceptional : CanonicalStableRawLeftTokenIsExceptional
      ends m j k l zero hloop hjk hkl hk0 p first.1
  · by_cases hfresh : ∀ i, tightFirst ≠ tokens i
    · exact Or.inr (Or.inl
        (finiteEmbedding_add_fresh size tokens tightFirst hfresh))
    · push_neg at hfresh
      obtain ⟨i, hi⟩ := hfresh
      let second : StatMech.FrontierA.crossCollision
          (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component)
          (canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component) :=
        ⟨(collision, directs i), by
          change first = canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component (directs i)
          exact (congrArg Subtype.val hi).trans (hdirect i).symm⟩
      exact Or.inr (Or.inr ⟨second⟩)
  · let terminal : CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
      ⟨first, hexceptional⟩
    exact Or.inl ⟨terminal, hfirst⟩


theorem canonicalStableRawComponentTightHoleMoveAcross_classification
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
    (state : StatMech.FrontierA.RelationPartialMatching.HoleState
      (fun (tightState : ↑sources)
          (tightToken : ↑(canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component sources)) =>
        CanonicalStableRawComponentIncident
          ends m j k l zero hloop hjk hkl hk0 p hno component
            tightState.1 tightToken.1))
    (token : ↑(canonicalStableRawComponentIncidentNeighborhood
      ends m j k l zero hloop hjk hkl hk0 p hno component sources))
    (hincident : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component
        state.hole.1 token.1) :
    let moved := state.moveAcross token hincident
    state.hole.1 ≠ moved.hole.1 ∧
      ∃ u : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p,
        u.target = canonicalStableRawLeftTokenTarget
          ends m j k l zero hloop hjk hkl hk0 p token.1 ∧
        (CanonicalStableRawOwnerStableOutput
            ends m j k l zero hloop hjk hkl hk0 p state.hole.1 u ∨
          CanonicalStableRawOwnerAdvancingOutput
            ends m j k l zero hloop hjk hkl hk0 p state.hole.1 u) ∧
        canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
  classical
  dsimp only
  let moved := state.moveAcross token hincident
  have hne : state.hole ≠ moved.hole :=
    state.hole_ne_moveAcross_hole token hincident
  have hneRaw : state.hole.1 ≠ moved.hole.1 := by
    intro heq
    exact hne (Subtype.ext heq)
  have hnext : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component
        moved.hole.1 token.1 :=
    state.matching.related
      (state.matching_apply_moveAcross_hole token hincident)
  have hclassification :=
    canonicalStableRawWitnessedStateTokenIncidence_sharedTokenClassification
      ends m j k l zero hloop hjk hkl hk0 p hno
        token.1 state.hole.1 moved.hole.1 hincident hnext
  refine ⟨hneRaw, ?_⟩
  rcases hclassification with heq | hstable | hadvancing
  · exact False.elim (hneRaw (Subtype.ext heq))
  · exact ⟨hstable.choose, hstable.choose_spec.1,
      Or.inl hstable.choose_spec.2.1,
      hstable.choose_spec.2.2.1.trans state.hole.1.2⟩
  · exact ⟨hadvancing.choose, hadvancing.choose_spec.1,
      Or.inr hadvancing.choose_spec.2.1,
      hadvancing.choose_spec.2.2.1.trans state.hole.1.2⟩


theorem canonicalStableRawComponentTightHoleMove_classification
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
    (state : StatMech.FrontierA.RelationPartialMatching.HoleState
      (fun (tightState : ↑sources)
          (tightToken : ↑(canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component sources)) =>
        CanonicalStableRawComponentIncident
          ends m j k l zero hloop hjk hkl hk0 p hno component
            tightState.1 tightToken.1)) :
    let natural := canonicalStableRawComponentTightNaturalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component sources
    let hnatural := canonicalStableRawComponentTightNaturalToken_incident
      ends m j k l zero hloop hjk hkl hk0 p hno component sources
    let moved := state.move natural hnatural
    state.hole.1 ≠ moved.hole.1 ∧
      ∃ u : CanonicalStableRawExceptionalEdge
          ends m j k l zero hloop hjk hkl hk0 p,
        u.target = canonicalStableRawLeftTokenTarget
          ends m j k l zero hloop hjk hkl hk0 p
            (natural state.hole).1.1 ∧
        (CanonicalStableRawOwnerStableOutput
            ends m j k l zero hloop hjk hkl hk0 p state.hole.1.1 u ∨
          CanonicalStableRawOwnerAdvancingOutput
            ends m j k l zero hloop hjk hkl hk0 p state.hole.1.1 u) ∧
        canonicalStableRawTokenComponent
            ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
  classical
  dsimp only
  let natural := canonicalStableRawComponentTightNaturalToken
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
  let hnatural := canonicalStableRawComponentTightNaturalToken_incident
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
  let moved := state.move natural hnatural
  have hne : state.hole ≠ moved.hole :=
    state.hole_ne_move_hole natural hnatural
  have hneRaw : state.hole.1 ≠ moved.hole.1 := by
    intro heq
    exact hne (Subtype.ext heq)
  have hcurrent : CanonicalStableRawWitnessedStateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p
        (natural state.hole).1.1 state.hole.1.1 :=
    hnatural state.hole
  have hnext : CanonicalStableRawWitnessedStateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p
        (natural state.hole).1.1 moved.hole.1.1 := by
    exact state.matching.related
      (state.matching_apply_move_hole natural hnatural)
  have hclassification :=
    canonicalStableRawWitnessedStateTokenIncidence_sharedTokenClassification
      ends m j k l zero hloop hjk hkl hk0 p hno
        (natural state.hole).1.1 state.hole.1.1 moved.hole.1.1
          hcurrent hnext
  refine ⟨hneRaw, ?_⟩
  rcases hclassification with heq | hstable | hadvancing
  · exact False.elim (hneRaw (Subtype.ext heq))
  · exact ⟨hstable.choose, hstable.choose_spec.1,
      Or.inl hstable.choose_spec.2.1,
      hstable.choose_spec.2.2.1.trans state.hole.1.2⟩
  · exact ⟨hadvancing.choose, hadvancing.choose_spec.1,
      Or.inr hadvancing.choose_spec.2.1,
      hadvancing.choose_spec.2.2.1.trans state.hole.1.2⟩


theorem exists_canonicalStableRawTightComponentSuccessorCollision
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
    (htight : (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 =
      sources.card) :
    let TightToken := ↑(canonicalStableRawComponentIncidentNeighborhood
      ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    let incident : ↑sources -> TightToken -> Prop := fun state token =>
      CanonicalStableRawComponentIncident
        ends m j k l zero hloop hjk hkl hk0 p hno component
          state.1 token.1
    let successor := canonicalStableRawComponentTightSuccessorToken
      ends m j k l zero hloop hjk hkl hk0 p hno component sources
    let hsuccessor := canonicalStableRawComponentTightSuccessorToken_incident
      ends m j k l zero hloop hjk hkl hk0 p hno component sources
    ∃ state : StatMech.FrontierA.RelationPartialMatching.HoleState incident,
      state.hole.1 ≠ (state.move successor hsuccessor).hole.1 ∧
        successor state.hole =
          successor (state.move successor hsuccessor).hole := by
  classical
  dsimp only
  let TightState := ↑sources
  let TightToken := ↑(canonicalStableRawComponentIncidentNeighborhood
    ends m j k l zero hloop hjk hkl hk0 p hno component sources)
  let incident : TightState -> TightToken -> Prop := fun state token =>
    CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component state.1 token.1
  let successor := canonicalStableRawComponentTightSuccessorToken
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
  let hsuccessor := canonicalStableRawComponentTightSuccessorToken_incident
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
  have hcard : Fintype.card TightToken < Fintype.card TightState := by
    simpa only [TightToken, TightState, Fintype.card_coe] using
      (show (canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources).card <
        sources.card by omega)
  obtain ⟨state, hne, heq⟩ :=
    StatMech.FrontierA.RelationPartialMatching.exists_maximalNatural_holeState_collision
      incident successor hsuccessor hcard
  refine ⟨state, ?_, heq⟩
  intro hraw
  exact hne (Subtype.ext hraw)


theorem canonicalStableRawComponentForestStep_eq_of_tightSuccessorToken_eq
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
    (x y : ↑sources)
    (hxy : canonicalStableRawComponentTightSuccessorToken
        ends m j k l zero hloop hjk hkl hk0 p hno component sources x =
      canonicalStableRawComponentTightSuccessorToken
        ends m j k l zero hloop hjk hkl hk0 p hno component sources y) :
    canonicalStableRawComponentForestStep
        ends m j k l zero hloop hjk hkl hk0 p hno component x.1 =
      canonicalStableRawComponentForestStep
        ends m j k l zero hloop hjk hkl hk0 p hno component y.1 := by
  let tokenEquiv := canonicalStableRawComponentDirectSumNonexceptionalEquivToken
    ends m j k l zero hloop hjk hkl hk0 p hno component
  apply tokenEquiv.injective
  have hx := canonicalStableRawComponentForestStep_token
    ends m j k l zero hloop hjk hkl hk0 p hno component x.1
  have hy := canonicalStableRawComponentForestStep_token
    ends m j k l zero hloop hjk hkl hk0 p hno component y.1
  have htoken : canonicalStableRawComponentSuccessorToken
        ends m j k l zero hloop hjk hkl hk0 p hno component x.1 =
      canonicalStableRawComponentSuccessorToken
        ends m j k l zero hloop hjk hkl hk0 p hno component y.1 :=
    congrArg Subtype.val hxy
  have hx' : tokenEquiv (canonicalStableRawComponentForestStep
        ends m j k l zero hloop hjk hkl hk0 p hno component x.1) =
      canonicalStableRawComponentSuccessorToken
        ends m j k l zero hloop hjk hkl hk0 p hno component x.1 := by
    cases hstep : canonicalStableRawComponentForestStep
        ends m j k l zero hloop hjk hkl hk0 p hno component x.1 with
    | inl direct =>
        rw [hstep] at hx
        simpa [tokenEquiv,
          canonicalStableRawComponentDirectSumNonexceptionalEquivToken] using hx
    | inr terminal =>
        rw [hstep] at hx
        simpa [tokenEquiv,
          canonicalStableRawComponentDirectSumNonexceptionalEquivToken] using hx
  have hy' : tokenEquiv (canonicalStableRawComponentForestStep
        ends m j k l zero hloop hjk hkl hk0 p hno component y.1) =
      canonicalStableRawComponentSuccessorToken
        ends m j k l zero hloop hjk hkl hk0 p hno component y.1 := by
    cases hstep : canonicalStableRawComponentForestStep
        ends m j k l zero hloop hjk hkl hk0 p hno component y.1 with
    | inl direct =>
        rw [hstep] at hy
        simpa [tokenEquiv,
          canonicalStableRawComponentDirectSumNonexceptionalEquivToken] using hy
    | inr terminal =>
        rw [hstep] at hy
        simpa [tokenEquiv,
          canonicalStableRawComponentDirectSumNonexceptionalEquivToken] using hy
  exact hx'.trans (htoken.trans hy'.symm)


theorem canonicalStableRawComponentForestStepMerger_of_alternatingPathRepeat
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
    (size : Nat) (path : Fin (size + 1) ↪ ↑sources)
    (tokens : Fin size ↪
      ↑(canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources))
    (htransition : ∀ i, tokens i =
      canonicalStableRawComponentTightSuccessorToken
        ends m j k l zero hloop hjk hkl hk0 p hno component sources
          (path i.castSucc))
    (index : Fin size)
    (hrepeat :
      canonicalStableRawComponentTightSuccessorToken
          ends m j k l zero hloop hjk hkl hk0 p hno component sources
            (path (Fin.last size)) =
        tokens index) :
    (path (Fin.last size)).1 ≠ (path index.castSucc).1 ∧
      canonicalStableRawComponentForestStep
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (path (Fin.last size)).1 =
        canonicalStableRawComponentForestStep
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (path index.castSucc).1 := by
  have hstatesNe : path (Fin.last size) ≠ path index.castSucc := by
    intro heq
    exact Fin.castSucc_ne_last index (path.injective heq).symm
  refine ⟨fun hraw => hstatesNe (Subtype.ext hraw), ?_⟩
  apply canonicalStableRawComponentForestStep_eq_of_tightSuccessorToken_eq
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
  exact hrepeat.trans (htransition index)


theorem canonicalStableRawComponentForestStepMerger_localizedOutput
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
    (x y : ↑sources)
    (hmerge : canonicalStableRawComponentForestStep
        ends m j k l zero hloop hjk hkl hk0 p hno component x.1 =
      canonicalStableRawComponentForestStep
        ends m j k l zero hloop hjk hkl hk0 p hno component y.1) :
    (∃ terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources ∧
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component x.1 =
          Sum.inr terminal ∧
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component y.1 =
          Sum.inr terminal) ∨
      ∃ direct : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component direct ∈
          canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component sources ∧
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component x.1 =
          Sum.inl direct ∧
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component y.1 =
          Sum.inl direct := by
  cases hx : canonicalStableRawComponentForestStep
      ends m j k l zero hloop hjk hkl hk0 p hno component x.1 with
  | inl direct =>
      have hy : canonicalStableRawComponentForestStep
          ends m j k l zero hloop hjk hkl hk0 p hno component y.1 =
          Sum.inl direct := hmerge.symm.trans hx
      right
      refine ⟨direct, ?_, rfl, hy⟩
      have htoken := canonicalStableRawComponentForestStep_token
        ends m j k l zero hloop hjk hkl hk0 p hno component x.1
      rw [hx] at htoken
      have htoken' : canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component direct =
          canonicalStableRawComponentSuccessorToken
            ends m j k l zero hloop hjk hkl hk0 p hno component x.1 := by
        simpa only using htoken
      rw [htoken']
      exact (canonicalStableRawComponentTightSuccessorToken
        ends m j k l zero hloop hjk hkl hk0 p hno component sources x).2
  | inr terminal =>
      have hy : canonicalStableRawComponentForestStep
          ends m j k l zero hloop hjk hkl hk0 p hno component y.1 =
          Sum.inr terminal := hmerge.symm.trans hx
      left
      refine ⟨terminal, ?_, rfl, hy⟩
      have htoken := canonicalStableRawComponentForestStep_token
        ends m j k l zero hloop hjk hkl hk0 p hno component x.1
      rw [hx] at htoken
      have htoken' : terminal.1 =
          canonicalStableRawComponentSuccessorToken
            ends m j k l zero hloop hjk hkl hk0 p hno component x.1 := by
        simpa only using htoken
      rw [htoken']
      exact (canonicalStableRawComponentTightSuccessorToken
        ends m j k l zero hloop hjk hkl hk0 p hno component sources x).2


theorem
    canonicalStableRawComponentForestStepMerger_threeTokens_of_distinctDirect
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
    (x y : ↑sources)
    (output first second : CanonicalStableRawComponentDirectState
      ends m j k l zero hloop hjk hkl hk0 p hno component)
    (hfirstNeSecond : first ≠ second)
    (hfirst : x.1.1 = first.1) (hsecond : y.1.1 = second.1)
    (hx : canonicalStableRawComponentForestStep
        ends m j k l zero hloop hjk hkl hk0 p hno component x.1 =
      Sum.inl output)
    (hy : canonicalStableRawComponentForestStep
        ends m j k l zero hloop hjk hkl hk0 p hno component y.1 =
      Sum.inl output) :
    Nonempty (Fin 3 ↪
      ↑(canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources)) := by
  let firstNatural := canonicalStableRawComponentTightNaturalToken
    ends m j k l zero hloop hjk hkl hk0 p hno component sources x
  let secondNatural := canonicalStableRawComponentTightNaturalToken
    ends m j k l zero hloop hjk hkl hk0 p hno component sources y
  let commonSuccessor := canonicalStableRawComponentTightSuccessorToken
    ends m j k l zero hloop hjk hkl hk0 p hno component sources x
  have hfirstNatural : firstNatural.1 =
      canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component first := by
    apply Subtype.ext
    change canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno x.1.1 =
      canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno first.1
    rw [hfirst]
  have hsecondNatural : secondNatural.1 =
      canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component second := by
    apply Subtype.ext
    change canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno y.1.1 =
      canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno second.1
    rw [hsecond]
  have hcommonX : commonSuccessor.1 =
      canonicalStableRawComponentDirectEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component output := by
    have htoken := canonicalStableRawComponentForestStep_token
      ends m j k l zero hloop hjk hkl hk0 p hno component x.1
    rw [hx] at htoken
    exact htoken.symm
  have hcommonY : commonSuccessor.1 =
      canonicalStableRawComponentSuccessorToken
        ends m j k l zero hloop hjk hkl hk0 p hno component y.1 := by
    have hyToken := canonicalStableRawComponentForestStep_token
      ends m j k l zero hloop hjk hkl hk0 p hno component y.1
    rw [hy] at hyToken
    exact hcommonX.trans hyToken
  have hfirstSecond : firstNatural ≠ secondNatural := by
    intro heq
    apply hfirstNeSecond
    apply (canonicalStableRawComponentDirectEmbedding
      ends m j k l zero hloop hjk hkl hk0 p hno component).injective
    exact hfirstNatural.symm.trans
      ((congrArg Subtype.val heq).trans hsecondNatural)
  have hfirstCommon : firstNatural ≠ commonSuccessor := by
    intro heq
    apply canonicalStableRawComponentSuccessorToken_ne_natural
      ends m j k l zero hloop hjk hkl hk0 p hno component x.1
    exact (congrArg Subtype.val heq).symm
  have hsecondCommon : secondNatural ≠ commonSuccessor := by
    intro heq
    apply canonicalStableRawComponentSuccessorToken_ne_natural
      ends m j k l zero hloop hjk hkl hk0 p hno component y.1
    exact hcommonY.symm.trans (congrArg Subtype.val heq).symm
  exact finiteEmbedding_three_of_pairwise_ne
    firstNatural secondNatural commonSuccessor
      hfirstSecond hfirstCommon hsecondCommon


theorem canonicalStableRawComponentForestStepMerger_localDischarge
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
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (herase : ∀ source ∈ sources,
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (sources.erase source) =
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (x y : ↑sources) (hne : x ≠ y)
    (hmerge : canonicalStableRawComponentForestStep
        ends m j k l zero hloop hjk hkl hk0 p hno component x.1 =
      canonicalStableRawComponentForestStep
        ends m j k l zero hloop hjk hkl hk0 p hno component y.1) :
    (∃ terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨
      Nonempty (Fin 3 ↪
        ↑(canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources)) ∨
      ∃ second : StatMech.FrontierA.crossCollision
          (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component)
          (canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component),
        canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component second.1.2 ∈
          canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component sources := by
  rcases canonicalStableRawComponentForestStepMerger_localizedOutput
      ends m j k l zero hloop hjk hkl hk0 p hno component sources x y hmerge with
    ⟨terminal, hterminal, _hx, _hy⟩ |
      ⟨output, _houtput, hx, hy⟩
  · exact Or.inl ⟨terminal, hterminal⟩
  · rcases canonicalStableRawComponent_distinctTightStates_localDischarge
        ends m j k l zero hloop hjk hkl hk0 p hno component sources herase
          x y hne with hterminal | hthree | hsecond |
            ⟨first, second, hfirstNeSecond, hfirst, hsecond⟩
    · exact Or.inl hterminal
    · exact Or.inr (Or.inl hthree)
    · exact Or.inr (Or.inr hsecond)
    · exact Or.inr (Or.inl
        (canonicalStableRawComponentForestStepMerger_threeTokens_of_distinctDirect
          ends m j k l zero hloop hjk hkl hk0 p hno component sources
            x y output first second hfirstNeSecond hfirst hsecond hx hy))


theorem exists_canonicalStableRawTightComponentForestStepMerger
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
    (htight : (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 =
      sources.card) :
    ∃ x y : ↑sources,
      x.1 ≠ y.1 ∧
        canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component x.1 =
          canonicalStableRawComponentForestStep
            ends m j k l zero hloop hjk hkl hk0 p hno component y.1 := by
  classical
  let successor := canonicalStableRawComponentTightSuccessorToken
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
  let hsuccessor := canonicalStableRawComponentTightSuccessorToken_incident
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
  obtain ⟨state, hne, htoken⟩ :=
    exists_canonicalStableRawTightComponentSuccessorCollision
      ends m j k l zero hloop hjk hkl hk0 p hno component sources htight
  refine ⟨state.hole, (state.move successor hsuccessor).hole, hne, ?_⟩
  exact canonicalStableRawComponentForestStep_eq_of_tightSuccessorToken_eq
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
      state.hole (state.move successor hsuccessor).hole htoken


theorem exists_canonicalStableRawTightComponent_localDischarge
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
    (sources : Finset (CanonicalStableRawComponentState
      ends m j k l zero hloop hjk hkl hk0 p hno component))
    (herase : ∀ source ∈ sources,
      canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component
            (sources.erase source) =
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    (htight : (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 =
      sources.card) :
    (∃ terminal : CanonicalStableRawComponentNonexceptionalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component,
        terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨
      Nonempty (Fin 3 ↪
        ↑(canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources)) ∨
      ∃ second : StatMech.FrontierA.crossCollision
          (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component)
          (canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component),
        canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component second.1.2 ∈
          canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component sources := by
  obtain ⟨x, y, hne, hmerge⟩ :=
    exists_canonicalStableRawTightComponentForestStepMerger
      ends m j k l zero hloop hjk hkl hk0 p hno component sources htight
  apply canonicalStableRawComponentForestStepMerger_localDischarge
    ends m j k l zero hloop hjk hkl hk0 p hno component sources herase x y
  · intro hxy
    exact hne (congrArg Subtype.val hxy)
  · exact hmerge


theorem exists_canonicalStableRawComponent_localDischarge_of_deficit
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
      ((∃ terminal : CanonicalStableRawComponentNonexceptionalToken
            ends m j k l zero hloop hjk hkl hk0 p hno component,
          terminal.1 ∈ canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨
        Nonempty (Fin 3 ↪
          ↑(canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component sources)) ∨
        ∃ second : StatMech.FrontierA.crossCollision
            (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component)
            (canonicalStableRawComponentDirectEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component),
          canonicalStableRawComponentDirectEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component second.1.2 ∈
            canonicalStableRawComponentIncidentNeighborhood
              ends m j k l zero hloop hjk hkl hk0 p hno component sources) := by
  classical
  obtain ⟨sources, hnonempty, htight, herase, hproper⟩ :=
    exists_canonicalStableRawComponent_minimalIncidentObstruction_of_deficit
      ends m j k l zero hloop hjk hkl hk0 p hno component hdeficit
  refine ⟨sources, hnonempty, htight, herase, hproper, ?_⟩
  exact exists_canonicalStableRawTightComponent_localDischarge
    ends m j k l zero hloop hjk hkl hk0 p hno component sources herase htight


theorem exists_canonicalStableRawComponent_strictBlock_or_fourTightSources_of_deficit
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
    (∃ size : Nat, 0 < size ∧
      Nonempty (Fin size ↪ CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component) ∧
      Nonempty (Fin (size + 1) ↪ CanonicalStableRawComponentToken
        ends m j k l zero hloop hjk hkl hk0 p hno component)) ∨
      ∃ sources : Finset (CanonicalStableRawComponentState
          ends m j k l zero hloop hjk hkl hk0 p hno component),
        Nonempty (Fin 4 ↪ ↑sources) := by
  classical
  obtain ⟨sources, hnonempty, htight, herase, hproper, hdischarge⟩ :=
    exists_canonicalStableRawComponent_localDischarge_of_deficit
      ends m j k l zero hloop hjk hkl hk0 p hno component hdeficit
  have strictOfTerminal
      (terminal : CanonicalStableRawComponentNonexceptionalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component) :
      ∃ size : Nat, 0 < size ∧
        Nonempty (Fin size ↪ CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component) ∧
        Nonempty (Fin (size + 1) ↪ CanonicalStableRawComponentToken
          ends m j k l zero hloop hjk hkl hk0 p hno component) := by
    have hdirectGt := canonicalStableRawComponent_direct_card_gt_self_of_deficit
      ends m j k l zero hloop hjk hkl hk0 p hno component hdeficit
    have hdirectPos : 0 < Nat.card (CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component) := by
      omega
    let start : CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
      (Nat.card_pos_iff.mp hdirectPos).1.some
    exact exists_canonicalStableRawComponentDirect_strictTokenBlock_of_available
      ends m j k l zero hloop hjk hkl hk0 p hno component start terminal
  rcases hdischarge with ⟨terminal, _hterminalMem⟩ | hthree |
      ⟨second, _hsecondMem⟩
  · exact Or.inl (strictOfTerminal terminal)
  · right
    let source := hnonempty.choose
    have hsource : source ∈ sources := hnonempty.choose_spec
    exact ⟨sources,
      exists_canonicalStableRawComponent_fourSourceEmbedding_of_threeTightTokens
        ends m j k l zero hloop hjk hkl hk0 p hno component sources
          source hsource htight hproper hthree⟩
  · exact Or.inl
      (exists_canonicalStableRawComponentSecondCollision_strictTokenBlock
        ends m j k l zero hloop hjk hkl hk0 p hno component second)


theorem exists_canonicalStableRawTightComponentCrossCollision
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
    (htight : (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 =
      sources.card) :
    let TightToken := ↑(canonicalStableRawComponentIncidentNeighborhood
      ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    let incident : ↑sources -> TightToken -> Prop := fun state token =>
      CanonicalStableRawComponentIncident
        ends m j k l zero hloop hjk hkl hk0 p hno component
          state.1 token.1
    let natural := canonicalStableRawComponentTightNaturalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component sources
    let hnatural := canonicalStableRawComponentTightNaturalToken_incident
      ends m j k l zero hloop hjk hkl hk0 p hno component sources
    ∃ state : StatMech.FrontierA.RelationPartialMatching.HoleState incident,
      ∃ collision : StatMech.FrontierA.crossCollision
          (canonicalStableRawComponentSelfEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component)
          (canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component),
        state.hole.1.1 = collision.1.1.1 ∧
          (state.move natural hnatural).hole.1.1 = collision.1.2.1 := by
  classical
  dsimp only
  let TightState := ↑sources
  let TightToken := ↑(canonicalStableRawComponentIncidentNeighborhood
    ends m j k l zero hloop hjk hkl hk0 p hno component sources)
  let incident : TightState -> TightToken -> Prop := fun state token =>
    CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component state.1 token.1
  let natural := canonicalStableRawComponentTightNaturalToken
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
  let hnatural := canonicalStableRawComponentTightNaturalToken_incident
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
  have hcard : Fintype.card TightToken < Fintype.card TightState := by
    simpa only [TightToken, TightState, Fintype.card_coe] using
      (show (canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources).card <
        sources.card by omega)
  obtain ⟨state, hholes, htoken⟩ :=
    StatMech.FrontierA.RelationPartialMatching.exists_maximalNatural_holeState_collision
      incident natural hnatural hcard
  have hrawToken : canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno state.hole.1.1 =
      canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno
          (state.move natural hnatural).hole.1.1 := by
    exact congrArg (fun token : TightToken => token.1.1) htoken
  rcases canonicalStableRawStateLeftToken_eq_imp
      ends m j k l zero hloop hjk hkl hk0 p hno
        state.hole.1.1 (state.move natural hnatural).hole.1.1 hrawToken with
    heq | hforward | hreverse
  · exact False.elim (hholes (Subtype.ext (Subtype.ext heq)))
  · let self : CanonicalStableRawComponentSelfState
          ends m j k l zero hloop hjk hkl hk0 p hno component :=
        ⟨state.hole.1.1, state.hole.1.2, hforward.1⟩
    let direct : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component :=
        ⟨(state.move natural hnatural).hole.1.1,
          (state.move natural hnatural).hole.1.2, hforward.2.1⟩
    let collision : StatMech.FrontierA.crossCollision
        (canonicalStableRawComponentSelfEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component) :=
      ⟨(self, direct), by
        apply Subtype.ext
        exact hrawToken⟩
    exact ⟨state, collision, rfl, rfl⟩
  · let self : CanonicalStableRawComponentSelfState
          ends m j k l zero hloop hjk hkl hk0 p hno component :=
        ⟨(state.move natural hnatural).hole.1.1,
          (state.move natural hnatural).hole.1.2, hreverse.1⟩
    let direct : CanonicalStableRawComponentDirectState
          ends m j k l zero hloop hjk hkl hk0 p hno component :=
        ⟨state.hole.1.1, state.hole.1.2, hreverse.2.1⟩
    let collision : StatMech.FrontierA.crossCollision
        (canonicalStableRawComponentSelfEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component) :=
      ⟨(self, direct), by
        apply Subtype.ext
        exact hrawToken.symm⟩
    have hback := state.move_move_hole_eq_of_natural_eq
      natural hnatural htoken
    refine ⟨state.move natural hnatural, collision, rfl, ?_⟩
    exact congrArg (fun tightState : TightState => tightState.1.1) hback


theorem exists_canonicalStableRawTightComponent_twoAlternateTokenEmbedding
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
    (htight : (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 =
      sources.card) :
    Nonempty (Fin 2 ↪
      ↑(canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources)) := by
  classical
  obtain ⟨state, collision, hself, _hdirect⟩ :=
    exists_canonicalStableRawTightComponentCrossCollision
      ends m j k l zero hloop hjk hkl hk0 p hno component sources htight
  exact canonicalStableRawComponent_tightCrossCollision_twoAlternateTokenEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
      state.hole collision hself


theorem
    exists_canonicalStableRawTightComponent_sourceNormalized_or_four_le_card
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
    (htight : (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 =
      sources.card) :
    (∃ state : ↑sources,
      ∃ collision : StatMech.FrontierA.crossCollision
          (canonicalStableRawComponentSelfEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component)
          (canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component),
        state.1.1 = collision.1.1.1 ∧
          canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component collision =
            canonicalStableRawComponentNaturalToken
              ends m j k l zero hloop hjk hkl hk0 p hno component state.1) ∨
      4 ≤ sources.card := by
  classical
  obtain ⟨state, collision, hself, _hdirect⟩ :=
    exists_canonicalStableRawTightComponentCrossCollision
      ends m j k l zero hloop hjk hkl hk0 p hno component sources htight
  rcases
      canonicalStableRawComponent_tightCrossCollision_sourceNormalized_or_threeTokens
        ends m j k l zero hloop hjk hkl hk0 p hno component sources
          state.hole collision hself with
    hnormalized | htokens
  · exact Or.inl ⟨state.hole, collision, hself, hnormalized⟩
  · right
    obtain ⟨tokens⟩ := htokens
    have hcard : 3 ≤
        (canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources).card := by
      simpa only [Fintype.card_fin, Fintype.card_coe] using
        Fintype.card_le_of_injective tokens tokens.injective
    omega


theorem exists_canonicalStableRawTightComponentFirstChargeOccupant
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
    (htight : (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 =
      sources.card) :
    let TightToken := ↑(canonicalStableRawComponentIncidentNeighborhood
      ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    let incident : ↑sources -> TightToken -> Prop := fun state token =>
      CanonicalStableRawComponentIncident
        ends m j k l zero hloop hjk hkl hk0 p hno component
          state.1 token.1
    let natural := canonicalStableRawComponentTightNaturalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component sources
    let hnatural := canonicalStableRawComponentTightNaturalToken_incident
      ends m j k l zero hloop hjk hkl hk0 p hno component sources
    ∃ state : StatMech.FrontierA.RelationPartialMatching.HoleState incident,
      ∃ collision : StatMech.FrontierA.crossCollision
          (canonicalStableRawComponentSelfEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component)
          (canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component),
      ∃ third : ↑sources,
        state.hole.1.1 = collision.1.1.1 ∧
        (state.move natural hnatural).hole.1.1 = collision.1.2.1 ∧
        third ≠ state.hole ∧
        third ≠ (state.move natural hnatural).hole ∧
        CanonicalStableRawComponentIncident
            ends m j k l zero hloop hjk hkl hk0 p hno component third.1
              (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
                ends m j k l zero hloop hjk hkl hk0 p hno component
                  collision) ∧
        ∃ u : CanonicalStableRawExceptionalEdge
            ends m j k l zero hloop hjk hkl hk0 p,
          u.target = canonicalStableRawLeftTokenTarget
              ends m j k l zero hloop hjk hkl hk0 p
                (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
                  ends m j k l zero hloop hjk hkl hk0 p hno component
                    collision).1 ∧
          (CanonicalStableRawOwnerStableOutput
              ends m j k l zero hloop hjk hkl hk0 p state.hole.1.1 u ∨
            CanonicalStableRawOwnerAdvancingOutput
              ends m j k l zero hloop hjk hkl hk0 p state.hole.1.1 u) ∧
          canonicalStableRawTokenComponent
              ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
  classical
  dsimp only
  let TightState := ↑sources
  let neighborhood := canonicalStableRawComponentIncidentNeighborhood
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
  let TightToken := ↑neighborhood
  let incident : TightState -> TightToken -> Prop := fun state token =>
    CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component state.1 token.1
  let natural := canonicalStableRawComponentTightNaturalToken
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
  let hnatural := canonicalStableRawComponentTightNaturalToken_incident
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
  let first := canonicalStableRawComponentReferenceOwnerCollisionEmbedding
    ends m j k l zero hloop hjk hkl hk0 p hno component
  obtain ⟨state, collision, hself, hdirect⟩ :=
    exists_canonicalStableRawTightComponentCrossCollision
      ends m j k l zero hloop hjk hkl hk0 p hno component sources htight
  have hfirstIncident : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component
        state.hole.1 (first collision) := by
    apply (canonicalStableRawWitnessedStateTokenIncidence_iff
      ends m j k l zero hloop hjk hkl hk0 p
        (first collision).1 state.hole.1.1).2
    rw [hself]
    exact canonicalStableRawReferenceOwnerLeftToken_stateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p
        collision.1.1.1 collision.1.1.2.2
  let firstTight : TightToken :=
    ⟨first collision, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, state.hole.1, state.hole.2, hfirstIncident⟩⟩
  obtain ⟨third, hthird⟩ :=
    state.maximum.saturates_target_of_unmatched
      state.hole state.hole_unmatched firstTight hfirstIncident
  have hthirdNeHole : third ≠ state.hole := by
    intro heq
    subst third
    exact state.hole_unmatched
      ((StatMech.FrontierA.RelationPartialMatching.mem_support_iff
        state.matching state.hole).2 ⟨firstTight, hthird⟩)
  have hthirdNeDirect : third ≠ (state.move natural hnatural).hole := by
    intro heq
    have hfirstNaturalTight : firstTight = natural state.hole := by
      apply Option.some.inj
      exact hthird.symm.trans
        (heq ▸ state.matching_apply_move_hole natural hnatural)
    have hfirstNatural : first collision =
        canonicalStableRawComponentNaturalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component
            state.hole.1 := by
      exact congrArg (fun token : TightToken => token.1) hfirstNaturalTight
    apply canonicalStableRawComponentReferenceOwnerCollisionEmbedding_ne_self
      ends m j k l zero hloop hjk hkl hk0 p hno component
        collision collision.1.1
    calc
      first collision = canonicalStableRawComponentNaturalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component
            state.hole.1 := hfirstNatural
      _ = canonicalStableRawComponentSelfEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component
            collision.1.1 := by
        apply Subtype.ext
        change canonicalStableRawStateLeftToken
            ends m j k l zero hloop hjk hkl hk0 p hno state.hole.1.1 =
          canonicalStableRawStateLeftToken
            ends m j k l zero hloop hjk hkl hk0 p hno collision.1.1.1
        rw [hself]
  have hthirdIncident : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component
        third.1 (first collision) := state.matching.related hthird
  have hclassification :=
    canonicalStableRawWitnessedStateTokenIncidence_sharedTokenClassification
      ends m j k l zero hloop hjk hkl hk0 p hno
        (first collision).1 state.hole.1.1 third.1.1
          hfirstIncident hthirdIncident
  have houtput : ∃ u : CanonicalStableRawExceptionalEdge
      ends m j k l zero hloop hjk hkl hk0 p,
      u.target = canonicalStableRawLeftTokenTarget
          ends m j k l zero hloop hjk hkl hk0 p (first collision).1 ∧
      (CanonicalStableRawOwnerStableOutput
          ends m j k l zero hloop hjk hkl hk0 p state.hole.1.1 u ∨
        CanonicalStableRawOwnerAdvancingOutput
          ends m j k l zero hloop hjk hkl hk0 p state.hole.1.1 u) ∧
      canonicalStableRawTokenComponent
          ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
    rcases hclassification with heq | hstable | hadvancing
    · exact False.elim (hthirdNeHole
        (Subtype.ext (Subtype.ext heq)).symm)
    · exact ⟨hstable.choose, hstable.choose_spec.1,
        Or.inl hstable.choose_spec.2.1,
        hstable.choose_spec.2.2.1.trans state.hole.1.2⟩
    · exact ⟨hadvancing.choose, hadvancing.choose_spec.1,
        Or.inr hadvancing.choose_spec.2.1,
        hadvancing.choose_spec.2.2.1.trans state.hole.1.2⟩
  exact ⟨state, collision, third, hself, hdirect,
    hthirdNeHole, hthirdNeDirect, hthirdIncident, houtput⟩


theorem exists_canonicalStableRawTightComponentFirstChargeCollisionSplit
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
    (htight : (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 =
      sources.card) :
    (∃ collision : StatMech.FrontierA.crossCollision
          (canonicalStableRawComponentSelfEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component)
          (canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component),
        ∃ direct : CanonicalStableRawComponentDirectState
            ends m j k l zero hloop hjk hkl hk0 p hno component,
          canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component collision =
            canonicalStableRawComponentDirectEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component direct ∧
          canonicalStableRawComponentDirectEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component
                collision.1.2 ∈
            canonicalStableRawComponentIncidentNeighborhood
              ends m j k l zero hloop hjk hkl hk0 p hno component sources ∧
          canonicalStableRawComponentDirectEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component direct ∈
            canonicalStableRawComponentIncidentNeighborhood
              ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨
      ∃ collision : StatMech.FrontierA.crossCollision
          (canonicalStableRawComponentSelfEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component)
          (canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component),
        ∃ direct : CanonicalStableRawComponentDirectState
            ends m j k l zero hloop hjk hkl hk0 p hno component,
          canonicalStableRawComponentReferenceOwnerCollisionEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component collision =
            canonicalStableRawComponentDirectEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component direct ∧
          canonicalStableRawComponentDirectEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component
                collision.1.2 ∈
            canonicalStableRawComponentIncidentNeighborhood
              ends m j k l zero hloop hjk hkl hk0 p hno component sources ∧
          canonicalStableRawComponentDirectEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component direct ∈
            canonicalStableRawComponentIncidentNeighborhood
              ends m j k l zero hloop hjk hkl hk0 p hno component sources := by
  classical
  obtain ⟨state, collision, _third, hself, _hdirect,
      _hthirdNeHole, _hthirdNeDirect, _hthirdIncident,
      u, huTarget, hkind, huComponent⟩ :=
    exists_canonicalStableRawTightComponentFirstChargeOccupant
      ends m j k l zero hloop hjk hkl hk0 p hno component sources htight
  have hnaturalMem : canonicalStableRawComponentNaturalToken
        ends m j k l zero hloop hjk hkl hk0 p hno component state.hole.1 ∈
      canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, state.hole.1, state.hole.2,
      canonicalStableRawComponentNaturalToken_incident
        ends m j k l zero hloop hjk hkl hk0 p hno component state.hole.1⟩
  have hcollisionNatural :
      canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component collision.1.2 =
        canonicalStableRawComponentNaturalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component state.hole.1 := by
    calc
      canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component collision.1.2 =
        canonicalStableRawComponentSelfEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component collision.1.1 :=
            collision.2.symm
      _ = canonicalStableRawComponentNaturalToken
          ends m j k l zero hloop hjk hkl hk0 p hno component state.hole.1 := by
        apply Subtype.ext
        change canonicalStableRawStateLeftToken
            ends m j k l zero hloop hjk hkl hk0 p hno collision.1.1.1 =
          canonicalStableRawStateLeftToken
            ends m j k l zero hloop hjk hkl hk0 p hno state.hole.1.1
        rw [hself]
  have hcollisionTokenMem :
      canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component collision.1.2 ∈
        canonicalStableRawComponentIncidentNeighborhood
          ends m j k l zero hloop hjk hkl hk0 p hno component sources := by
    rw [hcollisionNatural]
    exact hnaturalMem
  have huTargetRaw : u.target.1 =
      (canonicalStableRawReferenceOwnerAlternateData
        ends m j k l zero hloop hjk hkl hk0 p
          collision.1.1.1 collision.1.1.2.2).target :=
    calc
      u.target.1 = (canonicalStableRawLeftTokenTarget
          ends m j k l zero hloop hjk hkl hk0 p
            (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component
                collision).1).1 := congrArg Subtype.val huTarget
      _ = (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component
            collision).1.2.1 := rfl
      _ = (canonicalStableRawReferenceOwnerAlternateData
          ends m j k l zero hloop hjk hkl hk0 p
            collision.1.1.1 collision.1.1.2.2).target :=
        canonicalStableRawReferenceOwnerLeftToken_target
          ends m j k l zero hloop hjk hkl hk0 p
            collision.1.1.1 collision.1.1.2.2
  rw [hself] at hkind
  rcases hkind with hstable | hadvancing
  · obtain ⟨huDirect, hkey⟩ :=
      canonicalStableRawOwnerStableOutput_directKey_eq_referenceSource
        ends m j k l zero hloop hjk hkl hk0 p
          collision.1.1.1 u collision.1.1.2.2 huTargetRaw hstable
    let direct : CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
      ⟨u, huComponent, huDirect⟩
    have htoken :
        canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component collision =
          canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component direct := by
      apply (canonicalStableRawComponentTokenKeyEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component).injective
      change canonicalStableRawLeftTokenKey
          ends m j k l zero hloop hjk hkl hk0 p
            (canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component
                collision).1 =
        canonicalStableRawLeftTokenKey
          ends m j k l zero hloop hjk hkl hk0 p
            (canonicalStableRawComponentDirectEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component direct).1
      change canonicalStableRawLeftTokenKey
          ends m j k l zero hloop hjk hkl hk0 p
            (canonicalStableRawReferenceSourceLeftToken
              ends m j k l zero hloop hjk hkl hk0 p
                collision.1.1.1 collision.1.1.2.2) =
        canonicalStableRawLeftTokenKey
          ends m j k l zero hloop hjk hkl hk0 p
            (canonicalStableRawStateLeftToken
              ends m j k l zero hloop hjk hkl hk0 p hno u)
      unfold canonicalStableRawStateLeftToken
      rw [dif_neg huDirect]
      change (collision.1.1.1.source,
          (canonicalStableRawReferenceOwnerAlternateData
            ends m j k l zero hloop hjk hkl hk0 p
              collision.1.1.1 collision.1.1.2.2).target) =
        (u.source, u.target.1)
      exact hkey
    have hsourceIncident : CanonicalStableRawComponentIncident
        ends m j k l zero hloop hjk hkl hk0 p hno component state.hole.1
          (canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component collision) := by
      apply (canonicalStableRawWitnessedStateTokenIncidence_iff
        ends m j k l zero hloop hjk hkl hk0 p _ _).2
      rw [hself]
      exact canonicalStableRawReferenceSourceLeftToken_stateTokenIncidence
        ends m j k l zero hloop hjk hkl hk0 p
          collision.1.1.1 collision.1.1.2.2
    refine Or.inl ⟨collision, direct, htoken, hcollisionTokenMem, ?_⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, state.hole.1, state.hole.2,
      htoken ▸ hsourceIncident⟩
  · obtain ⟨huDirect, hkey⟩ :=
      canonicalStableRawOwnerAdvancingOutput_directKey_eq_referenceOwner
        ends m j k l zero hloop hjk hkl hk0 p
          collision.1.1.1 u collision.1.1.2.2 huTargetRaw hadvancing
    let direct : CanonicalStableRawComponentDirectState
        ends m j k l zero hloop hjk hkl hk0 p hno component :=
      ⟨u, huComponent, huDirect⟩
    have htoken :
        canonicalStableRawComponentReferenceOwnerCollisionEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component collision =
          canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component direct := by
      apply (canonicalStableRawComponentTokenKeyEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component).injective
      change canonicalStableRawLeftTokenKey
          ends m j k l zero hloop hjk hkl hk0 p
            (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component
                collision).1 =
        canonicalStableRawLeftTokenKey
          ends m j k l zero hloop hjk hkl hk0 p
            (canonicalStableRawComponentDirectEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component direct).1
      change canonicalStableRawLeftTokenKey
          ends m j k l zero hloop hjk hkl hk0 p
            (canonicalStableRawReferenceOwnerLeftToken
              ends m j k l zero hloop hjk hkl hk0 p
                collision.1.1.1 collision.1.1.2.2) =
        canonicalStableRawLeftTokenKey
          ends m j k l zero hloop hjk hkl hk0 p
            (canonicalStableRawStateLeftToken
              ends m j k l zero hloop hjk hkl hk0 p hno u)
      unfold canonicalStableRawStateLeftToken
      rw [dif_neg huDirect]
      change (canonicalStableRawReferenceOwner
            ends m j k l zero hloop hjk hkl hk0 p collision.1.1.1,
          (canonicalStableRawReferenceOwnerAlternateData
            ends m j k l zero hloop hjk hkl hk0 p
              collision.1.1.1 collision.1.1.2.2).target) =
        (u.source, u.target.1)
      exact hkey
    have hownerIncident : CanonicalStableRawComponentIncident
        ends m j k l zero hloop hjk hkl hk0 p hno component state.hole.1
          (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component collision) := by
      apply (canonicalStableRawWitnessedStateTokenIncidence_iff
        ends m j k l zero hloop hjk hkl hk0 p _ _).2
      rw [hself]
      exact canonicalStableRawReferenceOwnerLeftToken_stateTokenIncidence
        ends m j k l zero hloop hjk hkl hk0 p
          collision.1.1.1 collision.1.1.2.2
    refine Or.inr ⟨collision, direct, htoken, hcollisionTokenMem, ?_⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, state.hole.1, state.hole.2,
      htoken ▸ hownerIncident⟩


theorem
    exists_canonicalStableRawTightComponent_distinctDirectTokens_or_sourceNormalized
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
    (htight : (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 =
      sources.card) :
    (∃ collision : StatMech.FrontierA.crossCollision
          (canonicalStableRawComponentSelfEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component)
          (canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component),
        ∃ direct : CanonicalStableRawComponentDirectState
            ends m j k l zero hloop hjk hkl hk0 p hno component,
          direct ≠ collision.1.2 ∧
          canonicalStableRawComponentDirectEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component
                collision.1.2 ∈
            canonicalStableRawComponentIncidentNeighborhood
              ends m j k l zero hloop hjk hkl hk0 p hno component sources ∧
          canonicalStableRawComponentDirectEmbedding
              ends m j k l zero hloop hjk hkl hk0 p hno component direct ∈
            canonicalStableRawComponentIncidentNeighborhood
              ends m j k l zero hloop hjk hkl hk0 p hno component sources) ∨
      ∃ collision : StatMech.FrontierA.crossCollision
          (canonicalStableRawComponentSelfEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component)
          (canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component),
        canonicalStableRawComponentReferenceSourceFirstCollisionEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component collision =
          canonicalStableRawComponentSelfEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component collision.1.1 ∧
        canonicalStableRawComponentSelfEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component collision.1.1 ∈
          canonicalStableRawComponentIncidentNeighborhood
            ends m j k l zero hloop hjk hkl hk0 p hno component sources := by
  rcases exists_canonicalStableRawTightComponentFirstChargeCollisionSplit
      ends m j k l zero hloop hjk hkl hk0 p hno component sources htight with
    ⟨collision, direct, htoken, holdMem, hnewMem⟩ |
      ⟨collision, direct, htoken, holdMem, hnewMem⟩
  · by_cases hdistinct : direct ≠ collision.1.2
    · exact Or.inl ⟨collision, direct, hdistinct, holdMem, hnewMem⟩
    · have heq : direct = collision.1.2 := Classical.not_not.mp hdistinct
      right
      refine ⟨collision, ?_, ?_⟩
      · exact htoken.trans ((congrArg
          (canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component)
          heq).trans collision.2.symm)
      · rw [collision.2]
        exact holdMem
  · have hdistinct : direct ≠ collision.1.2 := by
      intro heq
      apply canonicalStableRawComponentReferenceOwnerCollisionEmbedding_ne_self
        ends m j k l zero hloop hjk hkl hk0 p hno component
          collision collision.1.1
      exact htoken.trans ((congrArg
        (canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component)
        heq).trans collision.2.symm)
    exact Or.inl ⟨collision, direct, hdistinct, holdMem, hnewMem⟩


theorem exists_canonicalStableRawTightComponent_threeStateTwoTokenPeelData
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
    (htight : (canonicalStableRawComponentIncidentNeighborhood
        ends m j k l zero hloop hjk hkl hk0 p hno component sources).card + 1 =
      sources.card) :
    let TightToken := ↑(canonicalStableRawComponentIncidentNeighborhood
      ends m j k l zero hloop hjk hkl hk0 p hno component sources)
    let incident : ↑sources -> TightToken -> Prop := fun state token =>
      CanonicalStableRawComponentIncident
        ends m j k l zero hloop hjk hkl hk0 p hno component state.1 token.1
    let natural := canonicalStableRawComponentTightNaturalToken
      ends m j k l zero hloop hjk hkl hk0 p hno component sources
    let hnatural := canonicalStableRawComponentTightNaturalToken_incident
      ends m j k l zero hloop hjk hkl hk0 p hno component sources
    ∃ state : StatMech.FrontierA.RelationPartialMatching.HoleState incident,
      ∃ collision : StatMech.FrontierA.crossCollision
          (canonicalStableRawComponentSelfEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component)
          (canonicalStableRawComponentDirectEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component),
        ∃ third : ↑sources, ∃ first : TightToken,
          state.hole.1.1 = collision.1.1.1 ∧
          (state.move natural hnatural).hole.1.1 = collision.1.2.1 ∧
          third ≠ state.hole ∧
          third ≠ (state.move natural hnatural).hole ∧
          state.hole ≠ (state.move natural hnatural).hole ∧
          first.1 = canonicalStableRawComponentReferenceOwnerCollisionEmbedding
            ends m j k l zero hloop hjk hkl hk0 p hno component collision ∧
          natural state.hole ≠ first ∧
          incident state.hole (natural state.hole) ∧
          incident (state.move natural hnatural).hole (natural state.hole) ∧
          incident state.hole first ∧ incident third first := by
  classical
  dsimp only
  let TightState := ↑sources
  let neighborhood := canonicalStableRawComponentIncidentNeighborhood
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
  let TightToken := ↑neighborhood
  let incident : TightState -> TightToken -> Prop := fun state token =>
    CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component state.1 token.1
  let natural := canonicalStableRawComponentTightNaturalToken
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
  let hnatural := canonicalStableRawComponentTightNaturalToken_incident
    ends m j k l zero hloop hjk hkl hk0 p hno component sources
  obtain ⟨state, collision, third, hself, hdirect,
      hthirdNeHole, hthirdNeDirect, hthirdIncident, _u, _huTarget,
      _hkind, _huComponent⟩ :=
    exists_canonicalStableRawTightComponentFirstChargeOccupant
      ends m j k l zero hloop hjk hkl hk0 p hno component sources htight
  have hfirstIncident : CanonicalStableRawComponentIncident
      ends m j k l zero hloop hjk hkl hk0 p hno component state.hole.1
        (canonicalStableRawComponentReferenceOwnerCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component collision) := by
    apply (canonicalStableRawWitnessedStateTokenIncidence_iff
      ends m j k l zero hloop hjk hkl hk0 p _ state.hole.1.1).2
    rw [hself]
    exact canonicalStableRawReferenceOwnerLeftToken_stateTokenIncidence
      ends m j k l zero hloop hjk hkl hk0 p
        collision.1.1.1 collision.1.1.2.2
  let first : TightToken :=
    ⟨canonicalStableRawComponentReferenceOwnerCollisionEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component collision,
      Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, state.hole.1, state.hole.2, hfirstIncident⟩⟩
  have hnaturalSelf : (natural state.hole).1 =
      canonicalStableRawComponentSelfEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hno component collision.1.1 := by
    apply Subtype.ext
    change canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno state.hole.1.1 =
      canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno collision.1.1.1
    rw [hself]
  have hnaturalDirect :
      (natural (state.move natural hnatural).hole).1 =
        canonicalStableRawComponentDirectEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component
            collision.1.2 := by
    apply Subtype.ext
    change canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno
          (state.move natural hnatural).hole.1.1 =
      canonicalStableRawStateLeftToken
        ends m j k l zero hloop hjk hkl hk0 p hno collision.1.2.1
    rw [hdirect]
  have hnaturalEq : natural state.hole =
      natural (state.move natural hnatural).hole := by
    apply Subtype.ext
    exact hnaturalSelf.trans (collision.2.trans hnaturalDirect.symm)
  have hfirstNe : natural state.hole ≠ first := by
    intro heq
    apply canonicalStableRawComponentReferenceOwnerCollisionEmbedding_ne_self
      ends m j k l zero hloop hjk hkl hk0 p hno component
        collision collision.1.1
    calc
      canonicalStableRawComponentReferenceOwnerCollisionEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component collision =
        first.1 := rfl
      _ = (natural state.hole).1 := congrArg Subtype.val heq.symm
      _ = canonicalStableRawComponentSelfEmbedding
          ends m j k l zero hloop hjk hkl hk0 p hno component
            collision.1.1 := hnaturalSelf
  refine ⟨state, collision, third, first, hself, hdirect,
    hthirdNeHole, hthirdNeDirect,
    state.hole_ne_move_hole natural hnatural, rfl, hfirstNe,
    hnatural state.hole, ?_, hfirstIncident, ?_⟩
  · change incident (state.move natural hnatural).hole (natural state.hole)
    rw [hnaturalEq]
    exact hnatural (state.move natural hnatural).hole
  · exact hthirdIncident


end StatMech.GrahamGHS.FourColor
