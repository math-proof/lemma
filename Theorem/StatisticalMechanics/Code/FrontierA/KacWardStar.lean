/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardStar.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.EvenSubgraphDecomp
import Theorem.StatisticalMechanics.Code.Lattice.JordanVeblenPeel.Part2
import Def.StatisticalMechanics.Code.FrontierA.KacWardStar
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

open StatMech.Ising


theorem kwEvenPolynomial_eq_one_of_isAcyclic {V : Type} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsAcyclic) (x : Sym2 V -> ℂ) : kwEvenPolynomial G x = 1 := by
  have hfilter : G.edgeFinset.powerset.filter IsEvenSubgraph = {∅} := by
    ext F
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton]
    constructor
    · rintro ⟨hFsub, hFeven⟩
      rw [<- Finset.not_nonempty_iff_eq_empty]
      rintro ⟨e, he⟩
      have hnoDiag : ∀ e ∈ F, ¬ e.IsDiag := by
        intro edge hedge
        exact evenSubgraphs_no_diag (Gd := G) (F := F) hFsub edge hedge
      have hle : subgraphF F ≤ G := subgraphF_le_of_subset (Gd := G) (F := F) hFsub
      have hac : (subgraphF F).IsAcyclic := hG.anti hle
      have hne : (subgraphF F).edgeSet.Nonempty :=
        ⟨e, (mem_edgeSet_subgraphF F hnoDiag e).mpr he⟩
      exact (Lattice.jvp_not_isAcyclic_of_even_nonempty (subgraphF F)
        (subgraphF_even F hnoDiag hFeven) hne) hac
    · rintro rfl
      simp [IsEvenSubgraph, incCount]
  unfold kwEvenPolynomial
  rw [hfilter]
  simp


end StatMech.FrontierA
