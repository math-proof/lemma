/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCluster.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneExclusion.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRectanglePreference.Part4
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalErgodicity.Part3
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAxisSwap.Part3
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAxisNegation.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneCluster.Part7
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


theorem PeriodicGraph.finiteSetEscapeWithin_measurableSet
    (P : PeriodicGraph V) (A : Set V) (L : Finset V) (n : Nat) :
    MeasurableSet (P.finiteSetEscapeWithin A L n) :=
  L.measurableSet_biUnion fun x _hx =>
    P.clusterWithinSetEscape_measurableSet A x n

omit [Countable V] in


theorem PeriodicGraph.iInter_finiteSetEscapeWithin
    (P : PeriodicGraph V) (A : Set V) (L : Finset V) :
    (⋂ n : Nat, P.finiteSetEscapeWithin A L n) =
      P.setHitsInfiniteWithin A (L : Set V) := by
  classical
  ext omega
  constructor
  · intro hescape
    by_contra hnot
    have hfinite (x : V) (hx : x ∈ L) :
        ¬(P.clusterWithinSet omega A x).Infinite := by
      intro hinfinite
      apply hnot
      exact ⟨x, by simpa using hx, hinfinite⟩
    have hexists (x : V) (hx : x ∈ L) : ∃ n : Nat,
        omega ∉ P.clusterWithinSetEscape A x n := by
      by_contra hall
      push Not at hall
      apply hfinite x hx
      rw [P.clusterWithinSet_infinite_iff_orbitBox_escape]
      intro n
      have hn := hall n
      obtain ⟨y, hyOutside, hyConnect⟩ := by
        simpa only [PeriodicGraph.clusterWithinSetEscape,
          Set.mem_iUnion] using hn
      exact ⟨y, hyOutside, hyConnect⟩
    let cutoff : V → Nat := fun x =>
      if hx : x ∈ L then (hexists x hx).choose else 0
    have hcutoff (x : V) (hx : x ∈ L) :
        omega ∉ P.clusterWithinSetEscape A x (cutoff x) := by
      simpa [cutoff, hx] using (hexists x hx).choose_spec
    let N : Nat := ∑ x ∈ L, cutoff x
    have hN := Set.mem_iInter.1 hescape N
    simp only [PeriodicGraph.finiteSetEscapeWithin, Set.mem_iUnion] at hN
    obtain ⟨x, hx, hxEscape⟩ := hN
    have hle : cutoff x ≤ N := by
      dsimp only [N]
      exact Finset.single_le_sum
        (fun y _hy => Nat.zero_le (cutoff y)) hx
    exact hcutoff x hx
      (P.clusterWithinSetEscape_antitone A x hle hxEscape)
  · rintro ⟨x, hxL, hinfinite⟩
    rw [Set.mem_iInter]
    intro n
    simp only [PeriodicGraph.finiteSetEscapeWithin, Set.mem_iUnion]
    refine ⟨x, by simpa using hxL, ?_⟩
    rw [P.clusterWithinSet_infinite_iff_orbitBox_escape] at hinfinite
    obtain ⟨y, hyOutside, hyConnect⟩ := hinfinite n
    simp only [PeriodicGraph.clusterWithinSetEscape, Set.mem_iUnion]
    exact ⟨y, hyOutside, hyConnect⟩

omit [Countable V] in
theorem PeriodicGraph.finiteSetEscapeWithin_antitone
    (P : PeriodicGraph V) (A : Set V) (L : Finset V) :
    Antitone (P.finiteSetEscapeWithin A L) := by
  intro n N hnN omega homega
  simp only [PeriodicGraph.finiteSetEscapeWithin, Set.mem_iUnion] at homega ⊢
  obtain ⟨x, hx, hxEscape⟩ := homega
  exact ⟨x, hx, P.clusterWithinSetEscape_antitone A x hnN hxEscape⟩


theorem PeriodicGraph.finiteSetEscapeWithin_measureReal_tendsto
    (P : PeriodicGraph V)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (A : Set V) (L : Finset V) :
    Tendsto (fun n => mu.real (P.finiteSetEscapeWithin A L n))
      atTop (nhds (mu.real (P.setHitsInfiniteWithin A (L : Set V)))) := by
  have hmeasure : Tendsto
      (fun n : Nat => mu (P.finiteSetEscapeWithin A L n)) atTop
      (nhds (mu (⋂ n : Nat, P.finiteSetEscapeWithin A L n))) :=
    tendsto_measure_iInter_atTop
      (fun n => (P.finiteSetEscapeWithin_measurableSet A L n).nullMeasurableSet)
      (P.finiteSetEscapeWithin_antitone A L)
      ⟨0, measure_ne_top mu _⟩
  rw [P.iInter_finiteSetEscapeWithin A L] at hmeasure
  exact (ENNReal.tendsto_toReal (measure_ne_top mu _)).comp hmeasure


theorem PeriodicPlaneEmbedding.rightHalfPlane_finiteSetEscape_measureReal_tendsto_zero
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (r : Real) (L : Finset V)
    (hL : (L : Set V) ⊆ E.rightHalfPlaneVertices r)
    (hnoInfinite : mu (E.rightHalfPlaneHasInfiniteCluster r) = 0) :
    Tendsto (fun n => mu.real
      (P.finiteSetEscapeWithin (E.rightHalfPlaneVertices r) L n))
      atTop (nhds 0) := by
  have hsingle (x : V) (hx : x ∈ L) : Tendsto (fun n => mu.real
      (P.clusterWithinSetEscape (E.rightHalfPlaneVertices r) x n))
      atTop (nhds 0) :=
    E.rightHalfPlane_vertexEscape_measureReal_tendsto_zero
      mu r x (hL (by simpa using hx)) hnoInfinite
  have hsum : Tendsto (fun n => ∑ x ∈ L, mu.real
      (P.clusterWithinSetEscape (E.rightHalfPlaneVertices r) x n))
      atTop (nhds 0) := by
    simpa using tendsto_finsetSum L (fun x hx => hsingle x hx)
  apply squeeze_zero
  · exact fun _ => measureReal_nonneg
  · intro n
    exact measureReal_biUnion_finset_le L
      (fun x => P.clusterWithinSetEscape
        (E.rightHalfPlaneVertices r) x n)
  · exact hsum


theorem PeriodicPlaneEmbedding.rectSideConnectionEvent_subset_finiteSetEscapeWithin
    (E : PeriodicPlaneEmbedding P)
    {a b c d : Real} {L : Finset V} {side A : Set V} {n : Nat}
    (hrect : E.rectVertices a b c d ⊆ A)
    (hside : side ⊆ (P.orbitBox n : Set V)ᶜ) :
    E.rectSideConnectionEvent a b c d (L : Set V) side ⊆
      P.finiteSetEscapeWithin A L n := by
  rintro omega ⟨x, hxL, _hxInfinite, y, hySide, hxy⟩
  simp only [PeriodicGraph.finiteSetEscapeWithin,
    PeriodicGraph.clusterWithinSetEscape, Set.mem_iUnion]
  refine ⟨x, hxL, y, hside hySide, ?_⟩
  exact P.connectedWithinSet_mono_region hrect x y hxy

theorem PeriodicPlaneEmbedding.rectSideConnection_measureReal_le_finiteSetEscapeWithin
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    {a b c d : Real} {L : Finset V} {side A : Set V} {n : Nat}
    (hrect : E.rectVertices a b c d ⊆ A)
    (hside : side ⊆ (P.orbitBox n : Set V)ᶜ) :
    mu.real (E.rectSideConnectionEvent a b c d (L : Set V) side) ≤
      mu.real (P.finiteSetEscapeWithin A L n) :=
  measureReal_mono
    (E.rectSideConnectionEvent_subset_finiteSetEscapeWithin hrect hside)

end StatMech.FK.PeriodicPlanar
