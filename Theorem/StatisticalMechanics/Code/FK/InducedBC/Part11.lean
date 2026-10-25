/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InducedBC.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.FK.DomainMarkov.Part5
import Theorem.StatisticalMechanics.Code.FK.WiredDominationInner.Part3
import Theorem.StatisticalMechanics.Code.FK.BoxCrossGraph.Part19
import Theorem.StatisticalMechanics.Code.FK.IvProperties
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
import Def.StatisticalMechanics.Code.FK.InducedBC.Part12
open scoped BigOperators
open SimpleGraph

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

open StatMech.Lattice

variable {d : ℕ}


theorem psiShift_pos {d n : ℕ} {ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))} {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) : 0 < psiShift d n ψ p q :=
  mul_pos (psiEdgeFactor_pos hp hp1) (pow_pos hq _)


theorem bcWeight_psiExt (d n : ℕ) {p q : ℝ} (ψ : ConfigSpace (Sym2 (boxVerts d (n+1))))
    (ω : ConfigSpace (Sym2 (boxVerts d n))) :
    bcWeight (boxGraph d (n+1))
        (StatMech.Lattice.boundaryCliqueGraph (boxBoundary d (n+1))) p q (psiExt d n ψ ω)
      = bcWeight (boxGraph d n) (inducedWiring d n ψ) p q ω * psiShift d n ψ p q := by
  rw [bcWeight, numClustersBC_psiExt, edgeProduct_psiExt, bcWeight, psiShift, pow_add]
  ring


theorem inducedBcZ_innerEdgeFinset_psi (d n : ℕ) {p q : ℝ}
    (ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))) :
    inducedBcZ (boxGraph d (n+1))
        (StatMech.Lattice.boundaryCliqueGraph (boxBoundary d (n+1))) p q
        (innerEdgeFinset d n) ψ
      = bcZ (boxGraph d n) (inducedWiring d n ψ) p q * psiShift d n ψ p q := by
  rw [inducedBcZ, condFibre_eq_image_psiExt,
    Finset.sum_image (fun a _ b _ h => by
      have := congrArg (innerRestrict d n) h
      rwa [innerRestrict_psiExt, innerRestrict_psiExt] at this),
    bcZ, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun ω _ => bcWeight_psiExt d n ψ ω)


theorem condBcProb_psiExt_eq_bcProb (d n : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))) (ω : ConfigSpace (Sym2 (boxVerts d n))) :
    condBcProb (boxGraph d (n+1))
        (StatMech.Lattice.boundaryCliqueGraph (boxBoundary d (n+1))) p q
        (innerEdgeFinset d n) ψ (psiExt d n ψ ω)
      = bcProb (boxGraph d n) (inducedWiring d n ψ) p q ω := by
  rw [condBcProb, if_pos (agreesOff_psiExt d n ψ ω), bcWeight_psiExt,
    inducedBcZ_innerEdgeFinset_psi, bcProb,
    mul_div_mul_right _ _ (psiShift_pos hp hp1 hq).ne']


theorem notMem_box_pred_of_adj_outer {d n : ℕ} (hn : 1 ≤ n) {x y : Site d}
    (hx : x ∈ StatMech.Lattice.box d n) (hadj : StatMech.Lattice.NearestNeighbour d x y)
    (hy : y ∉ StatMech.Lattice.box d n) : x ∉ StatMech.Lattice.box d (n - 1) := by
  rw [StatMech.Lattice.mem_box] at hx
  rw [StatMech.Lattice.mem_box] at hy
  simp only [not_forall, not_le] at hy
  obtain ⟨i, hyi⟩ := hy
  unfold StatMech.Lattice.NearestNeighbour at hadj
  have hterm : (x i - y i).natAbs ≤ 1 := by
    have hle : (x i - y i).natAbs ≤ ∑ j, (x j - y j).natAbs :=
      Finset.single_le_sum (f := fun j => (x j - y j).natAbs) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
    rw [hadj] at hle; exact hle
  have h1 : (y i).natAbs ≤ (x i).natAbs + (x i - y i).natAbs := by
    have hsub : (y i) = (x i) - (x i - y i) := by ring
    calc (y i).natAbs = ((x i) - (x i - y i)).natAbs := by rw [← hsub]
      _ ≤ (x i).natAbs + (x i - y i).natAbs := Int.natAbs_sub_le (x i) (x i - y i)
  have hxi : n ≤ (x i).natAbs := by omega
  rw [StatMech.Lattice.mem_box]
  simp only [not_forall, not_le]
  exact ⟨i, by omega⟩


theorem boxBoundary_of_outsideGraph_adj (d n : ℕ) (hn : 1 ≤ n)
    (ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))) {x : boxVerts d n} {z : boxVerts d (n+1)}
    (h : (outsideGraph d n ψ).Adj (boxVertIncl d n x) z) : boxBoundary d n x := by
  have hinx : IsInnerVert d n (boxVertIncl d n x) := isInnerVert_boxVertIncl d n x
  have hnotbdry : ¬ boxBoundary d (n+1) (boxVertIncl d n x) := by
    rw [boxBoundary_succ_iff_not_inner]; exact fun h => h hinx
  rw [outsideGraph_adj] at h
  rcases h with ⟨hadj, hopen, hrange⟩ | ⟨hne, hb1, hb2⟩
  · 
    have hznot : ¬ IsInnerVert d n z := by
      intro hz
      obtain ⟨z', rfl⟩ := (isInnerVert_iff_range d n z).mp hz
      exact hrange ⟨s(x, z'), by rw [innerEdge, Sym2.map_mk]⟩
    have hnn : StatMech.Lattice.NearestNeighbour d (x : Site d) (z : Site d) := by
      have hcp := hadj; rw [boxGraph, SimpleGraph.comap_adj] at hcp; exact hcp
    exact ⟨x.2, notMem_box_pred_of_adj_outer hn x.2 hnn hznot⟩
  · exact absurd hb1 hnotbdry


theorem inducedWiring_only_bdry (d n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n+1))))
    {x y : boxVerts d n} (h : (inducedWiring d n ψ).Adj x y) :
    boxBoundary d n x ∧ boxBoundary d n y := by
  obtain ⟨hne, hreach⟩ := h
  
  have hn : 1 ≤ n := by
    by_contra hlt
    have hn0 : n = 0 := by omega
    apply hne
    apply Subtype.ext
    have hx0 : (x : Site d) ∈ StatMech.Lattice.box d 0 := by rw [← hn0]; exact x.2
    have hy0 : (y : Site d) ∈ StatMech.Lattice.box d 0 := by rw [← hn0]; exact y.2
    rw [StatMech.Lattice.mem_box] at hx0 hy0
    funext i
    have hxi : (x : Site d) i = 0 := by
      have := hx0 i; omega
    have hyi : (y : Site d) i = 0 := by
      have := hy0 i; omega
    rw [hxi, hyi]
  
  
  have hbx : boxBoundary d n x := by
    have hne' : boxVertIncl d n x ≠ boxVertIncl d n y := fun he => hne (boxVertIncl_injective d n he)
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
    rcases hreach.cases_head with heq | ⟨c, hadj, _⟩
    · exact absurd heq hne'
    · exact boxBoundary_of_outsideGraph_adj d n hn ψ hadj
  have hby : boxBoundary d n y := by
    have hreach' : (outsideGraph d n ψ).Reachable (boxVertIncl d n y) (boxVertIncl d n x) :=
      hreach.symm
    have hne' : boxVertIncl d n y ≠ boxVertIncl d n x :=
      fun he => hne (boxVertIncl_injective d n he).symm
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach'
    rcases hreach'.cases_head with heq | ⟨c, hadj, _⟩
    · exact absurd heq hne'
    · exact boxBoundary_of_outsideGraph_adj d n hn ψ hadj
  exact ⟨hbx, hby⟩


theorem inducedWiring_le_wired (d n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))) :
    inducedWiring d n ψ ≤ StatMech.Lattice.boundaryCliqueGraph (boxBoundary d n) := by
  intro x y hxy
  rw [StatMech.Lattice.boundaryCliqueGraph_adj]
  obtain ⟨hbx, hby⟩ := inducedWiring_only_bdry d n ψ hxy
  exact ⟨(inducedWiring d n ψ).ne_of_adj hxy, hbx, hby⟩


theorem condBcProb_psiExt_sum_eq_inducedBox (d n : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (ψ : ConfigSpace (Sym2 (boxVerts d (n+1))))
    (B : Set (ConfigSpace (Sym2 (boxVerts d (n+1))))) :
    (∑ ρ, B.indicator (fun _ => (1:ℝ)) ρ *
        condBcProb (boxGraph d (n+1))
          (StatMech.Lattice.boundaryCliqueGraph (boxBoundary d (n+1))) p q
          (innerEdgeFinset d n) ψ ρ)
      = ∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
          (psiExt d n ψ ⁻¹' B).indicator (fun _ => (1:ℝ)) ω
            * bcProb (boxGraph d n) (inducedWiring d n ψ) p q ω := by
  classical
  
  have hsupp : ∀ ρ ∉ condFibre (innerEdgeFinset d n) ψ,
      B.indicator (fun _ => (1:ℝ)) ρ *
        condBcProb (boxGraph d (n+1))
          (StatMech.Lattice.boundaryCliqueGraph (boxBoundary d (n+1))) p q
          (innerEdgeFinset d n) ψ ρ = 0 := by
    intro ρ hρ
    rw [mem_condFibre] at hρ
    unfold condBcProb
    rw [if_neg hρ, mul_zero]
  rw [← Finset.sum_subset (Finset.subset_univ (condFibre (innerEdgeFinset d n) ψ))
    (fun ρ _ hρ => hsupp ρ hρ)]
  rw [condFibre_eq_image_psiExt]
  rw [Finset.sum_image (fun a _ b _ h => by
    have := congrArg (innerRestrict d n) h
    rwa [innerRestrict_psiExt, innerRestrict_psiExt] at this)]
  apply Finset.sum_congr rfl
  intro ω _
  rw [condBcProb_psiExt_eq_bcProb d n hp hp1 hq ψ ω]
  have hind : B.indicator (fun _ => (1:ℝ)) (psiExt d n ψ ω)
      = (psiExt d n ψ ⁻¹' B).indicator (fun _ => (1:ℝ)) ω := by
    by_cases hω : psiExt d n ψ ω ∈ B
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem (Set.mem_preimage.mpr hω)]
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem (fun h => hω (Set.mem_preimage.mp h))]
  rw [hind]


theorem condBcProb_psiExt_dominated (d n : ℕ)
    (ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (Sym2 (boxVerts d n)))} (hA : IsIncreasing A) :
    (∑ ω, A.indicator (fun _ => (1:ℝ)) ω
        * bcProb (boxGraph d n) (inducedWiring d n ψ) p q ω)
      ≤ ∑ ω, A.indicator (fun _ => (1:ℝ)) ω
          * bcProb (boxGraph d n)
              (StatMech.Lattice.boundaryCliqueGraph (boxBoundary d n)) p q ω :=
  bcProb_mono_bc (boxGraph d n) (inducedWiring d n ψ)
    (StatMech.Lattice.boundaryCliqueGraph (boxBoundary d n))
    (inducedWiring_le_wired d n ψ) hp hp1 hq hA


theorem condBcProb_psiExt_dominated_wired (d n : ℕ)
    (ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (Sym2 (boxVerts d n)))} (hA : IsIncreasing A) :
    (∑ ω, A.indicator (fun _ => (1:ℝ)) ω
        * bcProb (boxGraph d n) (inducedWiring d n ψ) p q ω)
      ≤ ∑ ω, A.indicator (fun _ => (1:ℝ)) ω
          * wiredFkProb (boxGraph d n) (boxBoundary d n) p q ω := by
  refine (condBcProb_psiExt_dominated d n ψ hp hp1 hq hA).trans_eq ?_
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  rw [bcProb_clique_eq_wiredFkProb]

end FK
end StatMech
