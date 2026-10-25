/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusFreeBoundaryComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusEmbedding.Part3
import Theorem.StatisticalMechanics.Code.Ising.GinibreBoundary
import Theorem.StatisticalMechanics.Code.Ising.GHSVertexPartition.Part8
import Theorem.StatisticalMechanics.Code.Sharpness.HighTempPlusBox.Part5
import Theorem.StatisticalMechanics.Code.FrontierB.InhomogeneousFiniteVolumeRelabel.Part2
import Def.StatisticalMechanics.Code.FrontierA.IsingTorusFreeBoundaryComparison.Part4
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising Sharpness Lattice

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem sum_cross_bond_finiteCutMerge_eq_boundaryField
    (S : Finset V) (inside : {v : V // v ∈ S} → Bool)
    (outside : {v : V // v ∉ S} → Bool) :
    (∑ e ∈ finiteCutCrossEdges G S, bond (finiteCutMerge S inside outside) e) =
      ∑ x : {v : V // v ∈ S},
        finiteCutBoundaryField G S outside x * spin inside x := by
  unfold finiteCutBoundaryField
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [ite_mul, zero_mul]
  let P := finiteCutCrossPairs G S
  have hpairs : (∑ y : {v : V // v ∉ S},
      ∑ x : {v : V // v ∈ S},
        if G.Adj x.1 y.1 then spin outside y * spin inside x else 0) =
      ∑ p ∈ P, spin outside p.2 * spin inside p.1 := by
    rw [Finset.sum_comm]
    simp only [P, finiteCutCrossPairs, Finset.sum_filter]
    rw [Finset.sum_product]
  rw [hpairs]
  symm
  apply Finset.sum_bij
      (fun p _ => s(p.1.1, p.2.1))
  · intro p hp
    simp only [P, finiteCutCrossPairs, Finset.mem_filter,
      Finset.mem_product, Finset.mem_univ, true_and] at hp
    exact (mk_mem_finiteCutCrossEdges_iff G S p.1.1 p.2.1).2
      ⟨hp, Or.inl ⟨p.1.2, p.2.2⟩⟩
  · intro p hp q hq hpq
    rw [Sym2.eq_iff] at hpq
    rcases hpq with hpq | hpq
    · exact Prod.ext (Subtype.ext hpq.1) (Subtype.ext hpq.2)
    · exact (q.2.2 (hpq.1 ▸ p.1.2)).elim
  · intro e he
    induction e using Sym2.ind with
    | _ x y =>
      rw [mk_mem_finiteCutCrossEdges_iff] at he
      rcases he.2 with hxy | hxy
      · let p : {v : V // v ∈ S} × {v : V // v ∉ S} :=
          (⟨x, hxy.1⟩, ⟨y, hxy.2⟩)
        refine ⟨p, ?_, rfl⟩
        simp [P, finiteCutCrossPairs, p, he.1]
      · let p : {v : V // v ∈ S} × {v : V // v ∉ S} :=
          (⟨y, hxy.2⟩, ⟨x, hxy.1⟩)
        refine ⟨p, ?_, Sym2.eq_swap⟩
        simp [P, finiteCutCrossPairs, p, he.1.symm]
  · intro p hp
    rw [bond_mk, spin_finiteCutMerge_inside, spin_finiteCutMerge_outside]
    ring


end
end StatMech.FrontierA
