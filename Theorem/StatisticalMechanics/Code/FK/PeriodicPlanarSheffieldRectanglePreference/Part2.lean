/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRectanglePreference.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAxisSwap.Part3
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRectanglePreference.Part2
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

theorem PeriodicPlaneEmbedding.rectanglePairMergeErrorUnion_measurableSet
    (E : PeriodicPlaneEmbedding P) (a b c d : Real) (L R : Finset V) :
    MeasurableSet (E.rectanglePairMergeErrorUnion a b c d L R) := by
  unfold PeriodicPlaneEmbedding.rectanglePairMergeErrorUnion
  exact MeasurableSet.iUnion fun x => MeasurableSet.iUnion fun _hx =>
    MeasurableSet.iUnion fun y => MeasurableSet.iUnion fun _hy =>
      ((P.measurableSet_cluster_infinite x).inter
        (P.measurableSet_cluster_infinite y)).diff
          (P.connectedWithinSet_measurableSet
            (E.rectVertices a b c d) x y)

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

theorem PeriodicPlaneEmbedding.rectanglePairMergeErrorUnion_measureReal_mono_sources
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (a b c d : Real) {L R L' R' : Finset V}
    (hL : L ⊆ L') (hR : R ⊆ R') :
    mu.real (E.rectanglePairMergeErrorUnion a b c d L R) ≤
      mu.real (E.rectanglePairMergeErrorUnion a b c d L' R') :=
  measureReal_mono (E.rectanglePairMergeErrorUnion_mono_sources
    a b c d hL hR)

omit [Countable V] in theorem PeriodicGraph.connectedWithinOrbit_subset_connectedWithinSet
    (P : PeriodicGraph V) {A : Set V} {x y : V} {N : Nat}
    (hbox : (P.orbitBox (P.bufferedRadius N) : Set V) ⊆ A) :
    P.connectedWithinOrbit x y N ⊆ P.connectedWithinSet A x y := by
  rintro omega ⟨l, hchain, hlast, hsupport⟩
  exact ⟨l, hchain, hlast, fun v hv => hbox (hsupport v hv)⟩


theorem PeriodicPlaneEmbedding.rectanglePairMergeErrorUnion_subset_pairMergeErrorUnion
    (E : PeriodicPlaneEmbedding P) (a b c d : Real)
    (L R : Finset V) (N : Nat)
    (hbox : (P.orbitBox (P.bufferedRadius N) : Set V) ⊆
      E.rectVertices a b c d) :
    E.rectanglePairMergeErrorUnion a b c d L R ⊆
      P.pairMergeErrorUnion L R N := by
  intro omega homega
  obtain ⟨x, hxL, y, hyR, hinf, hnotRect⟩ := by
    simpa only [PeriodicPlaneEmbedding.rectanglePairMergeErrorUnion,
      Set.mem_iUnion, Set.mem_diff, Set.mem_inter_iff,
      Set.mem_setOf_eq] using homega
  apply Set.mem_iUnion.2
  refine ⟨x, Set.mem_iUnion.2 ⟨hxL, Set.mem_iUnion.2 ⟨y,
    Set.mem_iUnion.2 ⟨hyR, ⟨hinf, ?_⟩⟩⟩⟩⟩
  intro horbit
  exact hnotRect
    (P.connectedWithinOrbit_subset_connectedWithinSet hbox horbit)

theorem PeriodicPlaneEmbedding.rectanglePairMergeErrorUnion_measureReal_le
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsFiniteMeasure mu]
    (a b c d : Real) (L R : Finset V) (N : Nat)
    (hbox : (P.orbitBox (P.bufferedRadius N) : Set V) ⊆
      E.rectVertices a b c d) :
    mu.real (E.rectanglePairMergeErrorUnion a b c d L R) ≤
      mu.real (P.pairMergeErrorUnion L R N) :=
  measureReal_mono
    (E.rectanglePairMergeErrorUnion_subset_pairMergeErrorUnion
      a b c d L R N hbox)


theorem PeriodicPlaneEmbedding.rectanglePairMergeErrorUnion_measureReal_tendsto_zero
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (a b c d : Nat → Real) (L R : Finset V)
    (hbox : ∀ N, (P.orbitBox (P.bufferedRadius N) : Set V) ⊆
      E.rectVertices (a N) (b N) (c N) (d N)) :
    Tendsto (fun N => mu.real
      (E.rectanglePairMergeErrorUnion (a N) (b N) (c N) (d N) L R))
      atTop (nhds 0) := by
  apply squeeze_zero
  · intro N
    exact measureReal_nonneg
  · intro N
    exact E.rectanglePairMergeErrorUnion_measureReal_le
      mu (a N) (b N) (c N) (d N) L R N (hbox N)
  · exact P.pairMergeErrorUnion_real_tendsto_zero mu hunique L R


theorem PeriodicPlaneEmbedding.configTranslate_preimage_rectanglePairMergeErrorUnion_subset
    (E : PeriodicPlaneEmbedding P) (z : Site 2) (a b c d : Real)
    (L R : Finset V) (N : Nat)
    (hbox : (P.shift z '' (P.orbitBox (P.bufferedRadius N) : Set V)) ⊆
      E.rectVertices a b c d) :
    P.configTranslate z ⁻¹'
        E.rectanglePairMergeErrorUnion a b c d
          (L.image (P.shift z)) (R.image (P.shift z)) ⊆
      P.pairMergeErrorUnion L R N := by
  intro omega homega
  change P.configTranslate z omega ∈
    E.rectanglePairMergeErrorUnion a b c d
      (L.image (P.shift z)) (R.image (P.shift z)) at homega
  obtain ⟨xz, hxzL, yz, hyzR, hinf, hnotRect⟩ := by
    simpa only [PeriodicPlaneEmbedding.rectanglePairMergeErrorUnion,
      Set.mem_iUnion, Set.mem_diff, Set.mem_inter_iff,
      Set.mem_setOf_eq] using homega
  obtain ⟨x, hxL, hxxz⟩ := Finset.mem_image.mp hxzL
  obtain ⟨y, hyR, hyyz⟩ := Finset.mem_image.mp hyzR
  subst xz
  subst yz
  have hxinf : (P.cluster omega x).Infinite :=
    (P.cluster_infinite_configTranslate z omega x).mp hinf.1
  have hyinf : (P.cluster omega y).Infinite :=
    (P.cluster_infinite_configTranslate z omega y).mp hinf.2
  apply Set.mem_iUnion.2
  refine ⟨x, Set.mem_iUnion.2 ⟨hxL, Set.mem_iUnion.2 ⟨y,
    Set.mem_iUnion.2 ⟨hyR, ⟨⟨hxinf, hyinf⟩, ?_⟩⟩⟩⟩⟩
  intro horbit
  have hshiftConn : P.configTranslate z omega ∈
      P.connectedWithinSet
        (P.shift z '' (P.orbitBox (P.bufferedRadius N) : Set V))
        (P.shift z x) (P.shift z y) := by
    apply (P.connectedWithinSet_configTranslate z omega
      (P.orbitBox (P.bufferedRadius N) : Set V) x y).2
    exact P.connectedWithinOrbit_subset_connectedWithinSet
      (fun _ h => h) horbit
  exact hnotRect
    (P.connectedWithinSet_mono_region hbox (P.shift z x) (P.shift z y)
      hshiftConn)

theorem PeriodicPlaneEmbedding.translated_rectanglePairMergeErrorUnion_measureReal_le
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (z : Site 2) (a b c d : Real) (L R : Finset V) (N : Nat)
    (hbox : (P.shift z '' (P.orbitBox (P.bufferedRadius N) : Set V)) ⊆
      E.rectVertices a b c d) :
    mu.real (E.rectanglePairMergeErrorUnion a b c d
        (L.image (P.shift z)) (R.image (P.shift z))) ≤
      mu.real (P.pairMergeErrorUnion L R N) := by
  let A := E.rectanglePairMergeErrorUnion a b c d
    (L.image (P.shift z)) (R.image (P.shift z))
  have hmeasure := P.translateEvent_measure_eq mu hTI z
    (E.rectanglePairMergeErrorUnion_measurableSet a b c d
      (L.image (P.shift z)) (R.image (P.shift z)))
  have hreal : mu.real (P.configTranslate z ⁻¹' A) = mu.real A :=
    congrArg ENNReal.toReal hmeasure
  rw [← hreal]
  exact measureReal_mono
    (E.configTranslate_preimage_rectanglePairMergeErrorUnion_subset
      z a b c d L R N hbox)


theorem PeriodicPlaneEmbedding.translated_rectanglePairMergeErrorUnion_measureReal_tendsto_zero
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (z : Nat → Site 2) (a b c d : Nat → Real) (L R : Finset V)
    (hbox : ∀ N,
      (P.shift (z N) '' (P.orbitBox (P.bufferedRadius N) : Set V)) ⊆
        E.rectVertices (a N) (b N) (c N) (d N)) :
    Tendsto (fun N => mu.real
      (E.rectanglePairMergeErrorUnion (a N) (b N) (c N) (d N)
        (L.image (P.shift (z N))) (R.image (P.shift (z N)))))
      atTop (nhds 0) := by
  apply squeeze_zero
  · intro N
    exact measureReal_nonneg
  · intro N
    exact E.translated_rectanglePairMergeErrorUnion_measureReal_le
      mu hTI (z N) (a N) (b N) (c N) (d N) L R N (hbox N)
  · exact P.pairMergeErrorUnion_real_tendsto_zero mu hunique L R


end StatMech.FK.PeriodicPlanar
