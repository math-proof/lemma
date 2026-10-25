/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectanglePreference.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAxisSwap.Part3
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRectanglePreference.Part3
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


def PeriodicPlaneEmbedding.finiteRectangleJoinedHorizontalEvent
    (E : PeriodicPlaneEmbedding P) (a b c d : Real)
    (L R : Finset V) : Set (ConfigSpace (Sym2 V)) :=
  (P.infiniteSetConnectionWithin (E.rectVertices a b c d) (L : Set V)
      (E.rectLeftBoundaryVertices a b c d) ∩
    P.infiniteSetConnectionWithin (E.rectVertices a b c d) (R : Set V)
      (E.rectRightBoundaryVertices a b c d)) \
    E.rectanglePairMergeErrorUnion a b c d L R

end StatMech.FK.PeriodicPlanar
