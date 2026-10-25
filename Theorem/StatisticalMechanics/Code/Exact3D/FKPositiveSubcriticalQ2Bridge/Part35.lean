/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteIsingFKBridge.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.SurfaceTensionConvexity
import Theorem.StatisticalMechanics.Code.FK.FKUniqPrimitives
import Theorem.StatisticalMechanics.Code.FK.RotationInvariance.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.IsingBoxEncoding.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.MagPercoIdBox.Part3
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneProps.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.SimonLiebFull.Part2
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part36
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem copyDeleteEmbeddingDecrementFinset_preimageErase
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ↥G.edgeFinset → ℕ)
    (i : Sharpness.FluxEdgeCopy.Copy G m)
    (K : Finset (Sharpness.FluxEdgeCopy.Copy G m)) :
    copyDeleteEmbeddingDecrementFinset G m i
        (copyDeletePreimageDecrementEraseFinset G m i K) =
      K.erase i := by
  classical
  ext j
  constructor
  · intro hj
    rw [copyDeleteEmbeddingDecrementFinset,
      copyDeletePreimageDecrementEraseFinset, Finset.mem_map] at hj
    obtain ⟨a, ha, hja⟩ := hj
    rw [Finset.mem_map] at ha
    obtain ⟨b, _hb, hab⟩ := ha
    subst a
    have hright :=
      copyDeleteEmbeddingDecrement_preimage_rightInverse G m i
        (⟨b.1, (Finset.mem_erase.mp b.2).1⟩ :
          {j : Sharpness.FluxEdgeCopy.Copy G m // j ≠ i})
    have hval :
        (copyDeleteEmbeddingDecrement G m i
          (copyDeletePreimageDecrement G m i
            ⟨b.1, (Finset.mem_erase.mp b.2).1⟩)).1 = b.1 :=
      congrArg
        (fun z : {j : Sharpness.FluxEdgeCopy.Copy G m // j ≠ i} => z.1)
        hright
    have hja' :
        (copyDeleteEmbeddingDecrement G m i
          (copyDeletePreimageDecrement G m i
            ⟨b.1, (Finset.mem_erase.mp b.2).1⟩)).1 = j := by
      simpa [copyDeleteEmbeddingDecrementEmbedding] using hja
    have hjb : j = b.1 := hja'.symm.trans hval
    rw [hjb]
    exact b.2
  · intro hj
    rw [copyDeleteEmbeddingDecrementFinset,
      copyDeletePreimageDecrementEraseFinset, Finset.mem_map]
    let b : {x : Sharpness.FluxEdgeCopy.Copy G m // x ∈ K.erase i} :=
      ⟨j, hj⟩
    refine
      ⟨copyDeletePreimageDecrement G m i
        ⟨j, (Finset.mem_erase.mp hj).1⟩, ?_, ?_⟩
    · rw [Finset.mem_map]
      exact ⟨b, Finset.mem_attach _ _, rfl⟩
    · have hright :=
        copyDeleteEmbeddingDecrement_preimage_rightInverse G m i
          (⟨j, (Finset.mem_erase.mp hj).1⟩ :
            {j : Sharpness.FluxEdgeCopy.Copy G m // j ≠ i})
      exact congrArg
        (fun z : {j : Sharpness.FluxEdgeCopy.Copy G m // j ≠ i} => z.1)
        hright


theorem copyDeletePreimageDecrementErase_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ↥G.edgeFinset → ℕ)
    (i : Sharpness.FluxEdgeCopy.Copy G m)
    (K : Finset (Sharpness.FluxEdgeCopy.Copy G m)) :
    (copyDeletePreimageDecrementEraseFinset G m i K).card =
      (K.erase i).card := by
  rw [copyDeletePreimageDecrementEraseFinset, Finset.card_map,
    Finset.card_attach]


theorem copyDeletePreimageDecrementEraseFinset_univ
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ↥G.edgeFinset → ℕ)
    (i : Sharpness.FluxEdgeCopy.Copy G m) :
    copyDeletePreimageDecrementEraseFinset G m i
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)) =
      (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G
        (Function.update m i.1 (m i.1 - 1)))) := by
  classical
  apply Finset.eq_univ_of_forall
  intro a
  rw [copyDeletePreimageDecrementEraseFinset, Finset.mem_map]
  let j : {j : Sharpness.FluxEdgeCopy.Copy G m // j ≠ i} :=
    copyDeleteEmbeddingDecrement G m i a
  let b : {x : Sharpness.FluxEdgeCopy.Copy G m //
      x ∈ (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy G m)).erase i} :=
    ⟨j.1, by
      rw [Finset.mem_erase]
      exact ⟨j.2, Finset.mem_univ _⟩⟩
  refine ⟨b, Finset.mem_attach _ _, ?_⟩
  exact copyDeletePreimageDecrement_embedding_leftInverse G m i a


theorem copyDeletePreimageDecrementErase_sources
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ↥G.edgeFinset → ℕ)
    (i : Sharpness.FluxEdgeCopy.Copy G m)
    (K : Finset (Sharpness.FluxEdgeCopy.Copy G m)) :
    Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM G
          (Function.update m i.1 (m i.1 - 1)))
        (copyDeletePreimageDecrementEraseFinset G m i K) =
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM G m) (K.erase i) := by
  have hmap :=
    copyDeleteEmbeddingDecrement_sources_map G m i
      (copyDeletePreimageDecrementEraseFinset G m i K)
  rw [copyDeleteEmbeddingDecrementFinset_preimageErase] at hmap
  exact hmap.symm


theorem finiteBoundaryGhostBoundaryCrossingCopyCount_le_boundaryGhostMultiplicity
    {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (v : FK.boxVerts 3 n)
    (K : Finset (Sharpness.FluxEdgeCopy.Copy
      (Sharpness.withGhost (FK.boxGraph 3 n)) m)) :
    finiteBoundaryGhostBoundaryCrossingCopyCount m v K ≤
      m ⟨s(some v, none), by
        rw [SimpleGraph.mem_edgeFinset]
        simp [Sharpness.withGhost]⟩ := by
  classical
  let G := Sharpness.withGhost (FK.boxGraph 3 n)
  let eGhost : ↥G.edgeFinset :=
    ⟨s(some v, none), by
      rw [SimpleGraph.mem_edgeFinset]
      simp [G, Sharpness.withGhost]⟩
  have hle :=
    edgeCopy_filter_card_le_multiplicity_sum G m K
      (fun e : ↥G.edgeFinset =>
        some v ∈ e.1 ∧ none ∈ e.1)
  have hsum :
      (∑ e : ↥G.edgeFinset,
        if some v ∈ e.1 ∧ none ∈ e.1 then m e else 0) =
        m eGhost := by
    change
      (∑ e ∈ (Finset.univ : Finset ↥G.edgeFinset),
        if some v ∈ e.1 ∧ none ∈ e.1 then m e else 0) =
        m eGhost
    calc
      (∑ e ∈ (Finset.univ : Finset ↥G.edgeFinset),
        if some v ∈ e.1 ∧ none ∈ e.1 then m e else 0) =
          (if some v ∈ eGhost.1 ∧ none ∈ eGhost.1 then m eGhost else 0) := by
        refine
          Finset.sum_eq_single
            (s := (Finset.univ : Finset ↥G.edgeFinset))
            (f := fun e : ↥G.edgeFinset =>
              if some v ∈ e.1 ∧ none ∈ e.1 then m e else 0)
            eGhost ?_ ?_
        · intro e _he hne
          by_cases hcross : some v ∈ e.1 ∧ none ∈ e.1
          · have heq : e = eGhost := by
              apply Subtype.ext
              exact (Sym2.mem_and_mem_iff (by simp)).mp hcross
            exact False.elim (hne heq)
          · simp [hcross]
        · simp
      _ = m eGhost := by
        simp [eGhost]
  have hleGhost :
      finiteBoundaryGhostBoundaryCrossingCopyCount m v K ≤ m eGhost := by
    simpa [finiteBoundaryGhostBoundaryCrossingCopyCount,
      Sharpness.FluxEdgeCopy.endsM, G] using hle.trans_eq hsum
  simpa [G, eGhost] using hleGhost


theorem finiteBoundaryGhostBoundaryCrossingPairCount_le_sourceSector_card_mul_boundaryGhostMultiplicity
    {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (v : FK.boxVerts 3 n) :
    finiteBoundaryGhostBoundaryCrossingPairCount m v ≤
      (finiteBoundaryGhostSourceSector m).card *
        m ⟨s(some v, none), by
          rw [SimpleGraph.mem_edgeFinset]
          simp [Sharpness.withGhost]⟩ := by
  classical
  unfold finiteBoundaryGhostBoundaryCrossingPairCount
  rw [Finset.card_eq_sum_ones]
  rw [Finset.sum_mul]
  simp only [one_mul]
  refine Finset.sum_le_sum ?_
  intro K _hK
  exact finiteBoundaryGhostBoundaryCrossingCopyCount_le_boundaryGhostMultiplicity
    m v K


theorem finiteBoundaryGhost_collapsedSourceSector_has_boundaryGhostCrossingCopy
    {β H : ℝ} {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (hsector : 0 < (finiteBoundaryGhostSourceSector m).card)
    (hweight :
      Sharpness.weight (Sharpness.withGhost (FK.boxGraph 3 n)) β
        (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
        (Sharpness.ofEdgeFun (Sharpness.withGhost (FK.boxGraph 3 n)) m) ≠ 0) :
    ∃ v : FK.boxVerts 3 n,
      FK.boxBoundary 3 n v ∧
      ∃ K : Finset (Sharpness.FluxEdgeCopy.Copy
        (Sharpness.withGhost (FK.boxGraph 3 n)) m),
        K ∈ finiteBoundaryGhostSourceSector m ∧
        (∃ i ∈ K,
          some v ∈ Sharpness.FluxEdgeCopy.endsM
            (Sharpness.withGhost (FK.boxGraph 3 n)) m i ∧
          none ∈ Sharpness.FluxEdgeCopy.endsM
            (Sharpness.withGhost (FK.boxGraph 3 n)) m i) ∧
        Sharpness.RandomCurrent.connK
          (Sharpness.FluxEdgeCopy.endsM
            (Sharpness.withGhost (FK.boxGraph 3 n)) m) K
          (some (IsingFK.boxOrigin 3 n)) (some v) := by
  classical
  obtain ⟨K, hK⟩ := Finset.card_pos.mp hsector
  have hsrc :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n)) m) K =
        finiteBoundaryGhostOnePointSource 3 n := by
    simpa [finiteBoundaryGhostSourceSector] using hK
  obtain ⟨v, hvbdry, hcross, hconn⟩ :=
    finiteBoundaryGhost_sourceSector_has_boundaryGhostCrossingCopy
      (β := β) (H := H) m K hsrc hweight
  exact ⟨v, hvbdry, K, hK, hcross, hconn⟩


theorem finiteBoundaryGhost_sources_remove_boundaryGhostCopy
    {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (K : Finset (Sharpness.FluxEdgeCopy.Copy
      (Sharpness.withGhost (FK.boxGraph 3 n)) m))
    {v : FK.boxVerts 3 n}
    {i : Sharpness.FluxEdgeCopy.Copy
      (Sharpness.withGhost (FK.boxGraph 3 n)) m}
    (hiK : i ∈ K)
    (hsrc :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n)) m) K =
        finiteBoundaryGhostOnePointSource 3 n)
    (hends :
      Sharpness.FluxEdgeCopy.endsM
        (Sharpness.withGhost (FK.boxGraph 3 n)) m i = s(some v, none)) :
    Sharpness.RandomCurrent.sources
      (Sharpness.FluxEdgeCopy.endsM
        (Sharpness.withGhost (FK.boxGraph 3 n)) m) (K \ {i}) =
      (({some (IsingFK.boxOrigin 3 n)} :
        Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) := by
  classical
  let ends :=
    Sharpness.FluxEdgeCopy.endsM
      (Sharpness.withGhost (FK.boxGraph 3 n)) m
  rw [randomCurrent_sources_sdiff_singleton ends hiK]
  rw [hsrc]
  have hsingle :
      Sharpness.RandomCurrent.sources ends ({i} : Finset _) =
        {some v, none} :=
    randomCurrent_sources_singleton_of_ends_eq ends hends
  rw [hsingle]
  ext x
  rcases x with _ | w
  · simp [finiteBoundaryGhostOnePointSource, Finset.mem_symmDiff]
  · simp [finiteBoundaryGhostOnePointSource, Finset.mem_symmDiff]


theorem finiteBoundaryGhost_sources_insert_boundaryGhostCopy
    {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (K : Finset (Sharpness.FluxEdgeCopy.Copy
      (Sharpness.withGhost (FK.boxGraph 3 n)) m))
    {v : FK.boxVerts 3 n}
    {i : Sharpness.FluxEdgeCopy.Copy
      (Sharpness.withGhost (FK.boxGraph 3 n)) m}
    (hiK : i ∉ K)
    (hsrc :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n)) m) K =
        (({some (IsingFK.boxOrigin 3 n)} :
          Finset (Option (FK.boxVerts 3 n))) ∆ {some v}))
    (hends :
      Sharpness.FluxEdgeCopy.endsM
        (Sharpness.withGhost (FK.boxGraph 3 n)) m i = s(some v, none)) :
    Sharpness.RandomCurrent.sources
      (Sharpness.FluxEdgeCopy.endsM
        (Sharpness.withGhost (FK.boxGraph 3 n)) m) (insert i K) =
      finiteBoundaryGhostOnePointSource 3 n := by
  classical
  let ends :=
    Sharpness.FluxEdgeCopy.endsM
      (Sharpness.withGhost (FK.boxGraph 3 n)) m
  have hinsert : insert i K = K ∆ ({i} : Finset _) := by
    ext j
    by_cases hji : j = i
    · subst j
      simp [hiK, Finset.mem_symmDiff]
    · simp [hji, Finset.mem_symmDiff]
  rw [hinsert]
  rw [Sharpness.RandomCurrent.sources_symmDiff ends K ({i} : Finset _)]
  rw [hsrc]
  have hsingle :
      Sharpness.RandomCurrent.sources ends ({i} : Finset _) =
        {some v, none} :=
    randomCurrent_sources_singleton_of_ends_eq ends hends
  rw [hsingle]
  ext x
  rcases x with _ | w
  · simp [finiteBoundaryGhostOnePointSource, Finset.mem_symmDiff]
  · by_cases hwo : w = IsingFK.boxOrigin 3 n
    · subst w
      by_cases hov : IsingFK.boxOrigin 3 n = v
      · subst v
        simp [finiteBoundaryGhostOnePointSource, Finset.mem_symmDiff]
      · simp [finiteBoundaryGhostOnePointSource, Finset.mem_symmDiff, hov]
    · by_cases hwv : w = v
      · subst w
        simp [finiteBoundaryGhostOnePointSource, Finset.mem_symmDiff, hwo]
      · simp [finiteBoundaryGhostOnePointSource, Finset.mem_symmDiff, hwo, hwv]


theorem finiteBoundaryGhost_sources_remove_boundaryGhostCopy_from_twoPoint
    {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (K : Finset (Sharpness.FluxEdgeCopy.Copy
      (Sharpness.withGhost (FK.boxGraph 3 n)) m))
    {v : FK.boxVerts 3 n}
    {i : Sharpness.FluxEdgeCopy.Copy
      (Sharpness.withGhost (FK.boxGraph 3 n)) m}
    (hiK : i ∈ K)
    (hsrc :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n)) m) K =
        (({some (IsingFK.boxOrigin 3 n)} :
          Finset (Option (FK.boxVerts 3 n))) ∆ {some v}))
    (hends :
      Sharpness.FluxEdgeCopy.endsM
        (Sharpness.withGhost (FK.boxGraph 3 n)) m i = s(some v, none)) :
    Sharpness.RandomCurrent.sources
      (Sharpness.FluxEdgeCopy.endsM
        (Sharpness.withGhost (FK.boxGraph 3 n)) m) (K \ {i}) =
      finiteBoundaryGhostOnePointSource 3 n := by
  classical
  let ends :=
    Sharpness.FluxEdgeCopy.endsM
      (Sharpness.withGhost (FK.boxGraph 3 n)) m
  rw [randomCurrent_sources_sdiff_singleton ends hiK]
  rw [hsrc]
  have hsingle :
      Sharpness.RandomCurrent.sources ends ({i} : Finset _) =
        {some v, none} :=
    randomCurrent_sources_singleton_of_ends_eq ends hends
  rw [hsingle]
  ext x
  rcases x with _ | w
  · simp [finiteBoundaryGhostOnePointSource, Finset.mem_symmDiff]
  · by_cases hwo : w = IsingFK.boxOrigin 3 n
    · subst w
      by_cases hov : IsingFK.boxOrigin 3 n = v
      · subst v
        simp [finiteBoundaryGhostOnePointSource, Finset.mem_symmDiff]
      · simp [finiteBoundaryGhostOnePointSource, Finset.mem_symmDiff, hov]
    · by_cases hwv : w = v
      · subst w
        simp [finiteBoundaryGhostOnePointSource, Finset.mem_symmDiff, hwo]
      · simp [finiteBoundaryGhostOnePointSource, Finset.mem_symmDiff, hwo, hwv]


theorem finiteBoundaryGhost_sources_preimageErase_boundaryGhostCopy
    {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (K : Finset (Sharpness.FluxEdgeCopy.Copy
      (Sharpness.withGhost (FK.boxGraph 3 n)) m))
    {v : FK.boxVerts 3 n}
    {i : Sharpness.FluxEdgeCopy.Copy
      (Sharpness.withGhost (FK.boxGraph 3 n)) m}
    (hiK : i ∈ K)
    (hsrc :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n)) m) K =
        finiteBoundaryGhostOnePointSource 3 n)
    (hends :
      Sharpness.FluxEdgeCopy.endsM
        (Sharpness.withGhost (FK.boxGraph 3 n)) m i = s(some v, none)) :
    Sharpness.RandomCurrent.sources
      (Sharpness.FluxEdgeCopy.endsM
        (Sharpness.withGhost (FK.boxGraph 3 n))
        (Function.update m i.1 (m i.1 - 1)))
      (copyDeletePreimageDecrementEraseFinset
        (Sharpness.withGhost (FK.boxGraph 3 n)) m i K) =
      (({some (IsingFK.boxOrigin 3 n)} :
        Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) := by
  classical
  have htransport :=
    copyDeletePreimageDecrementErase_sources
      (Sharpness.withGhost (FK.boxGraph 3 n)) m i K
  have hold :=
    finiteBoundaryGhost_sources_remove_boundaryGhostCopy
      m K hiK hsrc hends
  rw [htransport]
  simpa [Finset.sdiff_singleton_eq_erase] using hold


theorem finiteBoundaryGhost_sources_preimageErase_boundaryGhostCopy_from_twoPoint
    {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (K : Finset (Sharpness.FluxEdgeCopy.Copy
      (Sharpness.withGhost (FK.boxGraph 3 n)) m))
    {v : FK.boxVerts 3 n}
    {i : Sharpness.FluxEdgeCopy.Copy
      (Sharpness.withGhost (FK.boxGraph 3 n)) m}
    (hiK : i ∈ K)
    (hsrc :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n)) m) K =
        (({some (IsingFK.boxOrigin 3 n)} :
          Finset (Option (FK.boxVerts 3 n))) ∆ {some v}))
    (hends :
      Sharpness.FluxEdgeCopy.endsM
        (Sharpness.withGhost (FK.boxGraph 3 n)) m i = s(some v, none)) :
    Sharpness.RandomCurrent.sources
      (Sharpness.FluxEdgeCopy.endsM
        (Sharpness.withGhost (FK.boxGraph 3 n))
        (Function.update m i.1 (m i.1 - 1)))
      (copyDeletePreimageDecrementEraseFinset
        (Sharpness.withGhost (FK.boxGraph 3 n)) m i K) =
      finiteBoundaryGhostOnePointSource 3 n := by
  classical
  have htransport :=
    copyDeletePreimageDecrementErase_sources
      (Sharpness.withGhost (FK.boxGraph 3 n)) m i K
  have hold :=
    finiteBoundaryGhost_sources_remove_boundaryGhostCopy_from_twoPoint
      m K hiK hsrc hends
  rw [htransport]
  simpa [Finset.sdiff_singleton_eq_erase] using hold


theorem finiteBoundaryGhost_sources_univ_preimageErase_boundaryGhostCopy
    {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    {v : FK.boxVerts 3 n}
    {i : Sharpness.FluxEdgeCopy.Copy
      (Sharpness.withGhost (FK.boxGraph 3 n)) m}
    (hsrc :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n)) m)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
          (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
        finiteBoundaryGhostOnePointSource 3 n)
    (hends :
      Sharpness.FluxEdgeCopy.endsM
        (Sharpness.withGhost (FK.boxGraph 3 n)) m i = s(some v, none)) :
    Sharpness.RandomCurrent.sources
      (Sharpness.FluxEdgeCopy.endsM
        (Sharpness.withGhost (FK.boxGraph 3 n))
        (Function.update m i.1 (m i.1 - 1)))
      (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
        (Sharpness.withGhost (FK.boxGraph 3 n))
        (Function.update m i.1 (m i.1 - 1)))) =
      (({some (IsingFK.boxOrigin 3 n)} :
        Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) := by
  classical
  have htransport :=
    copyDeletePreimageDecrementErase_sources
      (Sharpness.withGhost (FK.boxGraph 3 n)) m i
      (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
        (Sharpness.withGhost (FK.boxGraph 3 n)) m))
  rw [copyDeletePreimageDecrementEraseFinset_univ] at htransport
  rw [htransport]
  have hold :=
    finiteBoundaryGhost_sources_remove_boundaryGhostCopy
      m
      (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
        (Sharpness.withGhost (FK.boxGraph 3 n)) m))
      (Finset.mem_univ i) hsrc hends
  simpa [Finset.sdiff_singleton_eq_erase] using hold


theorem finiteBoundaryGhost_sources_univ_preimageErase_boundaryGhostCopy_eq_fullSource_symmDiff
    {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    {v : FK.boxVerts 3 n}
    {i : Sharpness.FluxEdgeCopy.Copy
      (Sharpness.withGhost (FK.boxGraph 3 n)) m}
    (hends :
      Sharpness.FluxEdgeCopy.endsM
        (Sharpness.withGhost (FK.boxGraph 3 n)) m i = s(some v, none)) :
    Sharpness.RandomCurrent.sources
      (Sharpness.FluxEdgeCopy.endsM
        (Sharpness.withGhost (FK.boxGraph 3 n))
        (Function.update m i.1 (m i.1 - 1)))
      (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
        (Sharpness.withGhost (FK.boxGraph 3 n))
        (Function.update m i.1 (m i.1 - 1)))) =
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n)) m)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
          (Sharpness.withGhost (FK.boxGraph 3 n)) m)) ∆
        ({some v, none} : Finset (Option (FK.boxVerts 3 n))) := by
  classical
  let ends :=
    Sharpness.FluxEdgeCopy.endsM
      (Sharpness.withGhost (FK.boxGraph 3 n)) m
  have htransport :=
    copyDeletePreimageDecrementErase_sources
      (Sharpness.withGhost (FK.boxGraph 3 n)) m i
      (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
        (Sharpness.withGhost (FK.boxGraph 3 n)) m))
  rw [copyDeletePreimageDecrementEraseFinset_univ] at htransport
  rw [htransport]
  have hold :
      Sharpness.RandomCurrent.sources ends
          ((Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
            (Sharpness.withGhost (FK.boxGraph 3 n)) m)).erase i) =
        Sharpness.RandomCurrent.sources ends
          (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
            (Sharpness.withGhost (FK.boxGraph 3 n)) m)) ∆
          Sharpness.RandomCurrent.sources ends ({i} : Finset _) := by
    have hremove :=
      randomCurrent_sources_sdiff_singleton ends
        (K := (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
          (Sharpness.withGhost (FK.boxGraph 3 n)) m)))
        (i := i) (Finset.mem_univ i)
    simpa [Finset.sdiff_singleton_eq_erase] using hremove
  rw [hold]
  have hsingle :
      Sharpness.RandomCurrent.sources ends ({i} : Finset _) =
        ({some v, none} : Finset (Option (FK.boxVerts 3 n))) :=
    randomCurrent_sources_singleton_of_ends_eq ends hends
  rw [hsingle]


theorem finiteBoundaryGhostFullSourceOnePoint_of_decremented_univ_source
    {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    {v : FK.boxVerts 3 n}
    {i : Sharpness.FluxEdgeCopy.Copy
      (Sharpness.withGhost (FK.boxGraph 3 n)) m}
    (hends :
      Sharpness.FluxEdgeCopy.endsM
        (Sharpness.withGhost (FK.boxGraph 3 n)) m i = s(some v, none))
    (hdec :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n))
          (Function.update m i.1 (m i.1 - 1)))
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
          (Sharpness.withGhost (FK.boxGraph 3 n))
          (Function.update m i.1 (m i.1 - 1)))) =
        (({some (IsingFK.boxOrigin 3 n)} :
          Finset (Option (FK.boxVerts 3 n))) ∆ {some v})) :
    finiteBoundaryGhostFullSourceOnePoint n m := by
  classical
  have htransport :=
    copyDeletePreimageDecrementErase_sources
      (Sharpness.withGhost (FK.boxGraph 3 n)) m i
      (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
        (Sharpness.withGhost (FK.boxGraph 3 n)) m))
  rw [copyDeletePreimageDecrementEraseFinset_univ] at htransport
  have hold :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n)) m)
        ((Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
          (Sharpness.withGhost (FK.boxGraph 3 n)) m)).erase i) =
        (({some (IsingFK.boxOrigin 3 n)} :
          Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) :=
    htransport.symm.trans hdec
  have hfull :=
    finiteBoundaryGhost_sources_insert_boundaryGhostCopy
      m
      ((Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
        (Sharpness.withGhost (FK.boxGraph 3 n)) m)).erase i)
      (by simp) hold hends
  simpa [finiteBoundaryGhostFullSourceOnePoint] using hfull


theorem finiteBoundaryGhostBoundaryCrossingSourceSector_exists_removedSource
    {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    {v : FK.boxVerts 3 n}
    {K : Finset (Sharpness.FluxEdgeCopy.Copy
      (Sharpness.withGhost (FK.boxGraph 3 n)) m)}
    (hK : K ∈ finiteBoundaryGhostBoundaryCrossingSourceSector m v) :
    ∃ i ∈ K,
      some v ∈ Sharpness.FluxEdgeCopy.endsM
        (Sharpness.withGhost (FK.boxGraph 3 n)) m i ∧
      none ∈ Sharpness.FluxEdgeCopy.endsM
        (Sharpness.withGhost (FK.boxGraph 3 n)) m i ∧
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n)) m) (K \ {i}) =
        (({some (IsingFK.boxOrigin 3 n)} :
          Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) := by
  classical
  change
      K ∈ (finiteBoundaryGhostSourceSector m).filter
        (fun K =>
          ∃ i ∈ K,
            some v ∈ Sharpness.FluxEdgeCopy.endsM
              (Sharpness.withGhost (FK.boxGraph 3 n)) m i ∧
            none ∈ Sharpness.FluxEdgeCopy.endsM
              (Sharpness.withGhost (FK.boxGraph 3 n)) m i) at hK
  obtain ⟨hKsrc, hcross⟩ := Finset.mem_filter.mp hK
  have hsrc :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n)) m) K =
        finiteBoundaryGhostOnePointSource 3 n := by
    simpa [finiteBoundaryGhostSourceSector] using hKsrc
  obtain ⟨i, hiK, hsome, hnone⟩ := hcross
  have hends :
      Sharpness.FluxEdgeCopy.endsM
        (Sharpness.withGhost (FK.boxGraph 3 n)) m i =
          s(some v, none) := by
    exact (Sym2.mem_and_mem_iff (by simp)).mp ⟨hsome, hnone⟩
  exact
    ⟨i, hiK, hsome, hnone,
      finiteBoundaryGhost_sources_remove_boundaryGhostCopy
        m K hiK hsrc hends⟩


theorem
    finiteBoundaryGhostBoundaryCrossingSourceSector_exists_decrementedRemovedSource
    {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    {v : FK.boxVerts 3 n}
    {K : Finset (Sharpness.FluxEdgeCopy.Copy
      (Sharpness.withGhost (FK.boxGraph 3 n)) m)}
    (hK : K ∈ finiteBoundaryGhostBoundaryCrossingSourceSector m v) :
    ∃ i ∈ K,
      some v ∈ Sharpness.FluxEdgeCopy.endsM
        (Sharpness.withGhost (FK.boxGraph 3 n)) m i ∧
      none ∈ Sharpness.FluxEdgeCopy.endsM
        (Sharpness.withGhost (FK.boxGraph 3 n)) m i ∧
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n))
          (Function.update m i.1 (m i.1 - 1)))
        (copyDeletePreimageDecrementEraseFinset
          (Sharpness.withGhost (FK.boxGraph 3 n)) m i K) =
        (({some (IsingFK.boxOrigin 3 n)} :
          Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) := by
  classical
  change
      K ∈ (finiteBoundaryGhostSourceSector m).filter
        (fun K =>
          ∃ i ∈ K,
            some v ∈ Sharpness.FluxEdgeCopy.endsM
              (Sharpness.withGhost (FK.boxGraph 3 n)) m i ∧
            none ∈ Sharpness.FluxEdgeCopy.endsM
              (Sharpness.withGhost (FK.boxGraph 3 n)) m i) at hK
  obtain ⟨hKsrc, hcross⟩ := Finset.mem_filter.mp hK
  have hsrc :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n)) m) K =
        finiteBoundaryGhostOnePointSource 3 n := by
    simpa [finiteBoundaryGhostSourceSector] using hKsrc
  obtain ⟨i, hiK, hsome, hnone⟩ := hcross
  have hends :
      Sharpness.FluxEdgeCopy.endsM
        (Sharpness.withGhost (FK.boxGraph 3 n)) m i =
          s(some v, none) := by
    exact (Sym2.mem_and_mem_iff (by simp)).mp ⟨hsome, hnone⟩
  exact
    ⟨i, hiK, hsome, hnone,
      finiteBoundaryGhost_sources_preimageErase_boundaryGhostCopy
        m K hiK hsrc hends⟩


theorem finiteBoundaryGhostBoundaryCrossingPairs_decremented_source
    {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (v : FK.boxVerts 3 n)
    {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
      (Sharpness.withGhost (FK.boxGraph 3 n)) m) =>
      Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)}
    (hp : p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v) :
    Sharpness.RandomCurrent.sources
      (Sharpness.FluxEdgeCopy.endsM
        (Sharpness.withGhost (FK.boxGraph 3 n))
        (Function.update m p.2.1 (m p.2.1 - 1)))
      (copyDeletePreimageDecrementEraseFinset
        (Sharpness.withGhost (FK.boxGraph 3 n)) m p.2 p.1) =
      (({some (IsingFK.boxOrigin 3 n)} :
        Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) := by
  classical
  obtain ⟨hKsrc, hiK, hsome, hnone⟩ :=
    (finiteBoundaryGhostBoundaryCrossingPairs_mem m v p).mp hp
  have hsrc :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n)) m) p.1 =
        finiteBoundaryGhostOnePointSource 3 n := by
    simpa [finiteBoundaryGhostSourceSector] using hKsrc
  have hends :
      Sharpness.FluxEdgeCopy.endsM
        (Sharpness.withGhost (FK.boxGraph 3 n)) m p.2 =
          s(some v, none) := by
    exact (Sym2.mem_and_mem_iff (by simp)).mp ⟨hsome, hnone⟩
  exact
    finiteBoundaryGhost_sources_preimageErase_boundaryGhostCopy
      m p.1 hiK hsrc hends


theorem finiteBoundaryGhostBoundaryCrossingPairs_decremented_univ_source
    {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (v : FK.boxVerts 3 n)
    {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
      (Sharpness.withGhost (FK.boxGraph 3 n)) m) =>
      Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)}
    (hp : p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v)
    (hsrc :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n)) m)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
          (Sharpness.withGhost (FK.boxGraph 3 n)) m)) =
        finiteBoundaryGhostOnePointSource 3 n) :
    Sharpness.RandomCurrent.sources
      (Sharpness.FluxEdgeCopy.endsM
        (Sharpness.withGhost (FK.boxGraph 3 n))
        (Function.update m p.2.1 (m p.2.1 - 1)))
      (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
        (Sharpness.withGhost (FK.boxGraph 3 n))
        (Function.update m p.2.1 (m p.2.1 - 1)))) =
      (({some (IsingFK.boxOrigin 3 n)} :
        Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) := by
  classical
  obtain ⟨_hKsrc, _hiK, hsome, hnone⟩ :=
    (finiteBoundaryGhostBoundaryCrossingPairs_mem m v p).mp hp
  have hends :
      Sharpness.FluxEdgeCopy.endsM
        (Sharpness.withGhost (FK.boxGraph 3 n)) m p.2 =
          s(some v, none) := by
    exact (Sym2.mem_and_mem_iff (by simp)).mp ⟨hsome, hnone⟩
  exact
    finiteBoundaryGhost_sources_univ_preimageErase_boundaryGhostCopy
      m hsrc hends


theorem
    finiteBoundaryGhostBoundaryCrossingPairs_decremented_univ_source_eq_fullSource_symmDiff
    {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (v : FK.boxVerts 3 n)
    {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
      (Sharpness.withGhost (FK.boxGraph 3 n)) m) =>
      Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)}
    (hp : p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v) :
    Sharpness.RandomCurrent.sources
      (Sharpness.FluxEdgeCopy.endsM
        (Sharpness.withGhost (FK.boxGraph 3 n))
        (Function.update m p.2.1 (m p.2.1 - 1)))
      (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
        (Sharpness.withGhost (FK.boxGraph 3 n))
        (Function.update m p.2.1 (m p.2.1 - 1)))) =
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n)) m)
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
          (Sharpness.withGhost (FK.boxGraph 3 n)) m)) ∆
        ({some v, none} : Finset (Option (FK.boxVerts 3 n))) := by
  classical
  obtain ⟨_hKsrc, _hiK, hsome, hnone⟩ :=
    (finiteBoundaryGhostBoundaryCrossingPairs_mem m v p).mp hp
  have hends :
      Sharpness.FluxEdgeCopy.endsM
        (Sharpness.withGhost (FK.boxGraph 3 n)) m p.2 =
          s(some v, none) := by
    exact (Sym2.mem_and_mem_iff (by simp)).mp ⟨hsome, hnone⟩
  exact
    finiteBoundaryGhost_sources_univ_preimageErase_boundaryGhostCopy_eq_fullSource_symmDiff
      m hends


theorem
    finiteBoundaryGhostBoundaryCrossingPairs_fullSourceOnePoint_of_decremented_univ_source
    {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (v : FK.boxVerts 3 n)
    {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
      (Sharpness.withGhost (FK.boxGraph 3 n)) m) =>
      Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)}
    (hp : p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v)
    (hdec :
      Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n))
          (Function.update m p.2.1 (m p.2.1 - 1)))
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
          (Sharpness.withGhost (FK.boxGraph 3 n))
          (Function.update m p.2.1 (m p.2.1 - 1)))) =
        (({some (IsingFK.boxOrigin 3 n)} :
          Finset (Option (FK.boxVerts 3 n))) ∆ {some v})) :
    finiteBoundaryGhostFullSourceOnePoint n m := by
  classical
  obtain ⟨_hKsrc, _hiK, hsome, hnone⟩ :=
    (finiteBoundaryGhostBoundaryCrossingPairs_mem m v p).mp hp
  have hends :
      Sharpness.FluxEdgeCopy.endsM
        (Sharpness.withGhost (FK.boxGraph 3 n)) m p.2 =
          s(some v, none) := by
    exact (Sym2.mem_and_mem_iff (by simp)).mp ⟨hsome, hnone⟩
  exact
    finiteBoundaryGhostFullSourceOnePoint_of_decremented_univ_source
      m hends hdec


theorem
    finiteBoundaryGhostBoundaryCrossingPairs_inactive_decremented_univ_source_ne_twoPoint
    {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (v : FK.boxVerts 3 n)
    {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
      (Sharpness.withGhost (FK.boxGraph 3 n)) m) =>
      Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)}
    (hp : p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v)
    (hinactive : ¬ finiteBoundaryGhostFullSourceOnePoint n m) :
    Sharpness.RandomCurrent.sources
        (Sharpness.FluxEdgeCopy.endsM
          (Sharpness.withGhost (FK.boxGraph 3 n))
          (Function.update m p.2.1 (m p.2.1 - 1)))
        (Finset.univ : Finset (Sharpness.FluxEdgeCopy.Copy
          (Sharpness.withGhost (FK.boxGraph 3 n))
          (Function.update m p.2.1 (m p.2.1 - 1)))) ≠
        (({some (IsingFK.boxOrigin 3 n)} :
          Finset (Option (FK.boxVerts 3 n))) ∆ {some v}) := by
  intro hdec
  exact hinactive
    (finiteBoundaryGhostBoundaryCrossingPairs_fullSourceOnePoint_of_decremented_univ_source
      m v hp hdec)


theorem finiteBoundaryGhostBoundaryCrossingPairs_decremented_mem_twoPointSourceSector
    {n : ℕ}
    (m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)
    (v : FK.boxVerts 3 n)
    {p : Sigma (fun _K : Finset (Sharpness.FluxEdgeCopy.Copy
      (Sharpness.withGhost (FK.boxGraph 3 n)) m) =>
      Sharpness.FluxEdgeCopy.Copy (Sharpness.withGhost (FK.boxGraph 3 n)) m)}
    (hp : p ∈ finiteBoundaryGhostBoundaryCrossingPairs m v) :
    copyDeletePreimageDecrementEraseFinset
        (Sharpness.withGhost (FK.boxGraph 3 n)) m p.2 p.1 ∈
      finiteBoundaryGhostTwoPointSourceSector
        (Function.update m p.2.1 (m p.2.1 - 1)) v := by
  rw [finiteBoundaryGhostTwoPointSourceSector_mem]
  exact finiteBoundaryGhostBoundaryCrossingPairs_decremented_source m v hp


end Exact3D
end StatMech
