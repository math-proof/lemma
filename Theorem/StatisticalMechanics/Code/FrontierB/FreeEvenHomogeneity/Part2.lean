/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeEvenHomogeneity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierB.FreeBoxEvenLimit.Part6
import Theorem.StatisticalMechanics.Code.Ising.IsingPlusTIFromPlacement.Part11
import Def.StatisticalMechanics.Code.FrontierB.FreeEvenHomogeneity.Part3
open MeasureTheory Filter Topology
open scoped BigOperators


namespace StatMech.FrontierB

open Ising Lattice Sharpness


theorem freeDomainInclusionEquiv_adj {d : Nat}
    {K L : Finset (Site d)} (hKL : K ⊆ L)
    (x y : freeDomainVertices K) :
    (freeDomainGraph K).Adj x y ↔
      ((freeDomainGraph L).comap
        (Subtype.val : {z : freeDomainVertices L // z.1 ∈ K} ->
          freeDomainVertices L)).Adj
        (freeDomainInclusionEquiv hKL x)
        (freeDomainInclusionEquiv hKL y) := by
  rfl

theorem freeDomainSpinSupport_map_inclusion {d : Nat}
    {K L : Finset (Site d)} (hKL : K ⊆ L)
    (A : Finset (Site d)) (hA : A ⊆ K) :
    ((freeDomainSpinSupport K A).map
      (freeDomainInclusionEquiv hKL).toEmbedding).map
      (Function.Embedding.subtype (fun z : freeDomainVertices L => z.1 ∈ K)) =
        freeDomainSpinSupport L A := by
  ext z
  simp only [Finset.mem_map, freeDomainSpinSupport, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨w, ⟨x, hx, rfl⟩, rfl⟩
    exact hx
  · intro hz
    let x : freeDomainVertices K := ⟨z.1, hA hz⟩
    let w : {z : freeDomainVertices L // z.1 ∈ K} :=
      freeDomainInclusionEquiv hKL x
    refine ⟨w, ⟨x, ?_, rfl⟩, ?_⟩
    · exact hz
    · apply Subtype.ext
      rfl


theorem freeDomain_spinProd_mono {d : Nat}
    {K L : Finset (Site d)} (hKL : K ⊆ L)
    (beta : Real) (hbeta : 0 <= beta)
    (A : Finset (Site d)) (hA : A ⊆ K) :
    isingExpectation (freeDomainGraph K) beta 0
        (spinProd (freeDomainSpinSupport K A)) <=
      isingExpectation (freeDomainGraph L) beta 0
        (spinProd (freeDomainSpinSupport L A)) := by
  let e := freeDomainInclusionEquiv hKL
  calc
    isingExpectation (freeDomainGraph K) beta 0
        (spinProd (freeDomainSpinSupport K A)) =
      isingExpectation
        ((freeDomainGraph L).comap
          (Subtype.val : {z : freeDomainVertices L // z.1 ∈ K} ->
            freeDomainVertices L)) beta 0
        (spinProd ((freeDomainSpinSupport K A).map e.toEmbedding)) := by
      exact isingExpectation_spinProd_relabel (freeDomainGraph K)
        ((freeDomainGraph L).comap
          (Subtype.val : {z : freeDomainVertices L // z.1 ∈ K} ->
            freeDomainVertices L)) e
        (freeDomainInclusionEquiv_adj hKL) beta 0 _
    _ <= isingExpectation (freeDomainGraph L) beta 0
        (spinProd (((freeDomainSpinSupport K A).map e.toEmbedding).map
          (Function.Embedding.subtype
            (fun z : freeDomainVertices L => z.1 ∈ K)))) :=
      isingExpectation_spinProd_induce_le (freeDomainGraph L)
        (fun z : freeDomainVertices L => z.1 ∈ K)
        beta 0 hbeta le_rfl _
    _ = isingExpectation (freeDomainGraph L) beta 0
        (spinProd (freeDomainSpinSupport L A)) := by
      rw [freeDomainSpinSupport_map_inclusion hKL A hA]


end StatMech.FrontierB
