/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectanglePreference.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAxisSwap.Part3
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRectanglePreference.Part3
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

omit [Countable V] in theorem PeriodicPlaneEmbedding.rectanglePairMergeErrorUnion_mono_sources
    (E : PeriodicPlaneEmbedding P) (a b c d : Real)
    {L R L' R' : Finset V} (hL : L ⊆ L') (hR : R ⊆ R') :
    E.rectanglePairMergeErrorUnion a b c d L R ⊆
      E.rectanglePairMergeErrorUnion a b c d L' R' := by
  intro omega homega
  obtain ⟨x, hxL, y, hyR, hxy⟩ := by
    simpa only [PeriodicPlaneEmbedding.rectanglePairMergeErrorUnion,
      Set.mem_iUnion] using homega
  apply Set.mem_iUnion.2
  exact ⟨x, Set.mem_iUnion.2 ⟨hL hxL, Set.mem_iUnion.2 ⟨y,
    Set.mem_iUnion.2 ⟨hR hyR, hxy⟩⟩⟩⟩

omit [Countable V] in theorem PeriodicGraph.connectedWithinOrbit_subset_connectedWithinSet
    (P : PeriodicGraph V) {A : Set V} {x y : V} {N : Nat}
    (hbox : (P.orbitBox (P.bufferedRadius N) : Set V) ⊆ A) :
    P.connectedWithinOrbit x y N ⊆ P.connectedWithinSet A x y := by
  rintro omega ⟨l, hchain, hlast, hsupport⟩
  exact ⟨l, hchain, hlast, fun v hv => hbox (hsupport v hv)⟩


theorem PeriodicPlaneEmbedding.finiteRectangleJoinedVerticalEvent_measurableSet
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) (L R : Finset V) :
    MeasurableSet (E.finiteRectangleJoinedVerticalEvent a b c d L R) :=
  ((P.infiniteSetConnectionWithin_measurableSet
      (E.rectVertices a b c d) (L : Set V)
      (E.rectBottomBoundaryVertices a b c d)).inter
    (P.infiniteSetConnectionWithin_measurableSet
      (E.rectVertices a b c d) (R : Set V)
      (E.rectTopBoundaryVertices a b c d))).diff
    (E.rectanglePairMergeErrorUnion_measurableSet a b c d L R)


theorem PeriodicPlaneEmbedding.finiteRectangleJoinedVerticalEvent_subset_verticalCrossing
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) (L R : Finset V) :
    E.finiteRectangleJoinedVerticalEvent a b c d L R ⊆
      E.verticalCrossingEvent a b c d := by
  intro omega homega
  obtain ⟨x, hxL, hxinf, xb, hxbBottom, hxxb⟩ := homega.1.1
  obtain ⟨y, hyR, hyinf, yt, hytTop, hyyt⟩ := homega.1.2
  have hxy : omega ∈
      P.connectedWithinSet (E.rectVertices a b c d) x y := by
    by_contra hnot
    apply homega.2
    apply Set.mem_iUnion.2
    refine ⟨x, Set.mem_iUnion.2 ⟨hxL, Set.mem_iUnion.2 ⟨y,
      Set.mem_iUnion.2 ⟨hyR, ?_⟩⟩⟩⟩
    exact ⟨⟨hxinf, hyinf⟩, hnot⟩
  obtain ⟨qxb, hqxb⟩ := P.connectedWithinSet_exists_openSubgraphWalk hxxb
  obtain ⟨qxy, hqxy⟩ := P.connectedWithinSet_exists_openSubgraphWalk hxy
  obtain ⟨qyt, hqyt⟩ := P.connectedWithinSet_exists_openSubgraphWalk hyyt
  let q : (P.openSubgraph omega).Walk xb yt :=
    qxb.reverse.append (qxy.append qyt)
  have hqRect : ∀ v ∈ q.support, v ∈ E.rectVertices a b c d := by
    intro v hv
    dsimp only [q] at hv
    rw [SimpleGraph.Walk.support_append,
      SimpleGraph.Walk.support_reverse] at hv
    rcases List.mem_append.mp hv with hv | hv
    · exact hqxb v (by simpa using hv)
    · rw [SimpleGraph.Walk.support_append] at hv
      rcases List.mem_append.mp (List.mem_of_mem_tail hv) with hv | hv
      · exact hqxy v hv
      · exact hqyt v (List.mem_of_mem_tail hv)
  have hxbRect := hqRect xb q.start_mem_support
  have hytRect := hqRect yt q.end_mem_support
  have hbottom : E.rectBottomBoundary a b c d ⟨xb, hxbRect⟩ := by
    exact hxbBottom.2
  have htop : E.rectTopBoundary a b c d ⟨yt, hytRect⟩ := by
    exact hytTop.2
  have hreach :
      ((P.openSubgraph omega).induce (E.rectVertices a b c d)).Reachable
        ⟨xb, hxbRect⟩ ⟨yt, hytRect⟩ :=
    ⟨q.induce (E.rectVertices a b c d) hqRect⟩
  change E.rectRestrict a b c d omega ∈ E.finiteVerticalCrossing a b c d
  refine ⟨⟨xb, hxbRect⟩, ⟨yt, hytRect⟩, hbottom, htop, ?_⟩
  rw [E.openSub_rectRestrict_eq_induce]
  exact hreach


end StatMech.FK.PeriodicPlanar
