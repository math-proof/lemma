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
import Instance.StatisticalMechanics.Code.FrontierA.IsingTorusFreeBoundaryComparison
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising Sharpness Lattice

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem sum_internal_bond_finiteCutMerge_eq_cutGraph
    (S : Finset V) (inside : {v : V // v ∈ S} → Bool)
    (outside : {v : V // v ∉ S} → Bool) :
    (∑ e ∈ finiteCutInternalEdges G S,
        bond (finiteCutMerge S inside outside) e) =
      ∑ e ∈ (finiteCutGraph G S).edgeFinset, bond inside e := by
  symm
  apply Finset.sum_bij
      (fun e _ => Sym2.map (Subtype.val : {v : V // v ∈ S} → V) e)
  · intro e he
    induction e using Sym2.ind with
    | _ x y =>
      rw [Sym2.map_mk]
      exact (mk_mem_finiteCutInternalEdges_iff G S x.1 y.1).2
        ⟨by simpa [finiteCutGraph] using he, x.2, y.2⟩
  · intro e he f hf hef
    exact Sym2.map.injective Subtype.val_injective hef
  · intro e he
    induction e using Sym2.ind with
    | _ x y =>
      rw [mk_mem_finiteCutInternalEdges_iff] at he
      let e' : Sym2 {v : V // v ∈ S} :=
        s((⟨x, he.2.1⟩ : {v : V // v ∈ S}), ⟨y, he.2.2⟩)
      refine ⟨e', ?_, ?_⟩
      · simpa [e', finiteCutGraph] using he.1
      · simp [e']
  · intro e he
    induction e using Sym2.ind with
    | _ x y =>
      rw [Sym2.map_mk, bond_mk, bond_mk,
        spin_finiteCutMerge_inside, spin_finiteCutMerge_inside]

theorem finiteCutInternalEdges_subset (S : Finset V) :
    finiteCutInternalEdges G S ⊆ G.edgeFinset := by
  intro e he
  exact (Finset.mem_filter.1 he).1

theorem finiteCutExteriorEdges_subset (S : Finset V) :
    finiteCutExteriorEdges G S ⊆ G.edgeFinset := by
  intro e he
  exact (Finset.mem_filter.1 he).1

theorem finiteCutInternalEdges_disjoint_exterior (S : Finset V) :
    Disjoint (finiteCutInternalEdges G S) (finiteCutExteriorEdges G S) := by
  rw [Finset.disjoint_left]
  intro e hi he
  induction e using Sym2.ind with
  | _ x y =>
    have hi' := (mk_mem_finiteCutInternalEdges_iff G S x y).1 hi
    have he' := (mk_mem_finiteCutExteriorEdges_iff G S x y).1 he
    exact he'.2.1 hi'.2.1


theorem sum_bond_eq_internal_add_cross_add_exterior
    (S : Finset V) (sigma : ConfigSpace V) :
    (∑ e ∈ G.edgeFinset, bond sigma e) =
      (∑ e ∈ finiteCutInternalEdges G S, bond sigma e) +
      (∑ e ∈ finiteCutCrossEdges G S, bond sigma e) +
      ∑ e ∈ finiteCutExteriorEdges G S, bond sigma e := by
  let U := finiteCutInternalEdges G S ∪ finiteCutExteriorEdges G S
  have hU : U ⊆ G.edgeFinset := by
    exact Finset.union_subset
      (finiteCutInternalEdges_subset G S)
      (finiteCutExteriorEdges_subset G S)
  have hsplit :
      (∑ e ∈ G.edgeFinset \ U, bond sigma e) +
          ∑ e ∈ U, bond sigma e =
        ∑ e ∈ G.edgeFinset, bond sigma e :=
    Finset.sum_sdiff hU
  have hcross : G.edgeFinset \ U = finiteCutCrossEdges G S := by
    rfl
  have hunion : (∑ e ∈ U, bond sigma e) =
      (∑ e ∈ finiteCutInternalEdges G S, bond sigma e) +
        ∑ e ∈ finiteCutExteriorEdges G S, bond sigma e := by
    exact Finset.sum_union (finiteCutInternalEdges_disjoint_exterior G S)
  rw [hcross, hunion] at hsplit
  linarith


theorem sum_exterior_bond_finiteCutMerge_eq
    (S : Finset V) (inside inside' : {v : V // v ∈ S} → Bool)
    (outside : {v : V // v ∉ S} → Bool) :
    (∑ e ∈ finiteCutExteriorEdges G S,
        bond (finiteCutMerge S inside outside) e) =
      ∑ e ∈ finiteCutExteriorEdges G S,
        bond (finiteCutMerge S inside' outside) e := by
  apply Finset.sum_congr rfl
  intro e he
  induction e using Sym2.ind with
  | _ x y =>
    have he' := (mk_mem_finiteCutExteriorEdges_iff G S x y).1 he
    let x' : {v : V // v ∉ S} := ⟨x, he'.2.1⟩
    let y' : {v : V // v ∉ S} := ⟨y, he'.2.2⟩
    rw [bond_mk, bond_mk]
    change spin (finiteCutMerge S inside outside) x'.1 *
        spin (finiteCutMerge S inside outside) y'.1 =
      spin (finiteCutMerge S inside' outside) x'.1 *
        spin (finiteCutMerge S inside' outside) y'.1
    simp


theorem sum_bond_finiteCutMerge
    (S : Finset V) (inside : {v : V // v ∈ S} → Bool)
    (outside : {v : V // v ∉ S} → Bool) :
    (∑ e ∈ G.edgeFinset, bond (finiteCutMerge S inside outside) e) =
      (∑ e ∈ (finiteCutGraph G S).edgeFinset, bond inside e) +
      (∑ x : {v : V // v ∈ S},
        finiteCutBoundaryField G S outside x * spin inside x) +
      ∑ e ∈ finiteCutExteriorEdges G S,
        bond (finiteCutMerge S inside outside) e := by
  rw [sum_bond_eq_internal_add_cross_add_exterior,
    sum_internal_bond_finiteCutMerge_eq_cutGraph,
    sum_cross_bond_finiteCutMerge_eq_boundaryField]


theorem wJ_finiteCutMerge_factor
    (beta : Real) (S : Finset V)
    (inside : {v : V // v ∈ S} → Bool)
    (outside : {v : V // v ∉ S} → Bool) :
    wJ G.edgeFinset (fun _ => beta) (fun _ => 0)
        (finiteCutMerge S inside outside) =
      Real.exp (beta * (∑ e ∈ finiteCutExteriorEdges G S,
        bond (finiteCutMerge S inside outside) e)) *
      wJ (finiteCutGraph G S).edgeFinset (fun _ => beta)
        (fun x => beta * finiteCutBoundaryField G S outside x) inside := by
  unfold wJ
  simp only [zero_mul, Finset.sum_const_zero, add_zero]
  rw [← Finset.mul_sum, sum_bond_finiteCutMerge]
  rw [← Real.exp_add]
  congr 1
  rw [mul_add, mul_add]
  simp_rw [Finset.mul_sum]
  ring


end
end StatMech.FrontierA
