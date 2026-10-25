/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeSubsetDomainMarkov.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.ActiveBoundaryEquiv.Part2
import Theorem.StatisticalMechanics.Code.FK.FKDisjointBoxDomainMarkov.Part3
import Def.StatisticalMechanics.Code.FK.EdgeSubsetDomainMarkov.Part6
open Finset SimpleGraph
open scoped BigOperators


namespace StatMech.FK

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem edgeProduct_edgeSubsetFibre
    (K H : SimpleGraph V) [DecidableRel K.Adj]
    [DecidableRel H.Adj] (hKH : K ≤ H)
    (psi : ConfigSpace (Sym2 V)) (p : Real)
    (eta : ConfigSpace K.edgeSet) :
    edgeProduct H p (edgeSubsetFibreConfig K psi eta) =
      edgeSubsetExteriorEdgeFactor K H psi p *
        edgeProduct K p (extendActive K eta) := by
  classical
  let O := H.edgeFinset \ K.edgeFinset
  have hfactor : edgeSubsetExteriorEdgeFactor K H psi p =
      ∏ e ∈ O, if psi e then p else 1 - p := by
    unfold edgeSubsetExteriorEdgeFactor
    apply Finset.prod_congr
    · ext e
      simp [O]
    · intro e he
      rfl
  have hsub : K.edgeFinset ⊆ H.edgeFinset := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ x y =>
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he ⊢
        exact hKH he
  have hedges : H.edgeFinset = K.edgeFinset ∪ O :=
    (Finset.union_sdiff_of_subset hsub).symm
  have hdisj : Disjoint K.edgeFinset O := Finset.disjoint_sdiff
  have hinner :
      (∏ e ∈ K.edgeFinset,
        if edgeSubsetFibreConfig K psi eta e then p else 1 - p) =
      ∏ e ∈ K.edgeFinset,
        if extendActive K eta e then p else 1 - p := by
    apply Finset.prod_congr rfl
    intro e he
    have heSet : e ∈ K.edgeSet := by
      rwa [← SimpleGraph.mem_edgeFinset]
    have hfibre : edgeSubsetFibreConfig K psi eta e = eta ⟨e, heSet⟩ := by
      simp [edgeSubsetFibreConfig, heSet]
    have hactive := extendActive_apply K eta ⟨e, heSet⟩
    rw [hfibre, hactive]
  have houter :
      (∏ e ∈ O,
        if edgeSubsetFibreConfig K psi eta e then p else 1 - p) =
      ∏ e ∈ O, if psi e then p else 1 - p := by
    apply Finset.prod_congr rfl
    intro e he
    have heNot : e ∉ K.edgeSet := by
      have : e ∉ K.edgeFinset := (Finset.mem_sdiff.mp he).2
      simpa [SimpleGraph.mem_edgeFinset] using this
    simp [edgeSubsetFibreConfig, heNot]
  unfold edgeProduct
  rw [hedges, Finset.prod_union hdisj, hinner, houter, hfactor]
  exact mul_comm _ _

theorem bcWeight_edgeSubsetFibre_eq_induced
    (K H B : SimpleGraph V) [DecidableRel K.Adj]
    [DecidableRel H.Adj] [DecidableRel B.Adj]
    (hKH : K ≤ H) (psi : ConfigSpace (Sym2 V)) (p q : Real)
    (eta : ConfigSpace K.edgeSet) :
    bcWeight H B p q (edgeSubsetFibreConfig K psi eta) =
      edgeSubsetExteriorEdgeFactor K H psi p *
        activeBCWeight K (edgeSubsetInducedWiring K H B psi)
          (fun _ => p) q eta := by
  rw [bcWeight, edgeProduct_edgeSubsetFibre K H hKH psi p eta,
    numClustersBC_edgeSubsetFibre_eq_induced K H B hKH psi eta]
  rw [activeBCWeight_const_eq_bcWeight]
  unfold bcWeight
  ring

set_option maxHeartbeats 800000 in

theorem edgeSubset_inducedBcZ_eq
    (K H B : SimpleGraph V) [DecidableRel K.Adj]
    [DecidableRel H.Adj] [DecidableRel B.Adj]
    (hKH : K ≤ H) (psi : ConfigSpace (Sym2 V)) (p q : Real) :
    inducedBcZ H B p q K.edgeFinset psi =
      edgeSubsetExteriorEdgeFactor K H psi p *
        activeBCZ K (edgeSubsetInducedWiring K H B psi)
          (fun _ => p) q := by
  unfold inducedBcZ activeBCZ
  let S := condFibre K.edgeFinset psi
  let weight := fun rho : ConfigSpace (Sym2 V) => bcWeight H B p q rho
  calc
    (∑ rho ∈ S, weight rho) = ∑ rho : {rho // rho ∈ S}, weight rho :=
      Finset.sum_subtype S (fun _ => Iff.rfl) weight
    _ = ∑ eta, weight ((edgeSubsetFibreEquiv K psi) eta) :=
      (Equiv.sum_comp (edgeSubsetFibreEquiv K psi)
        (fun rho => weight rho.1)).symm
    _ = ∑ eta, edgeSubsetExteriorEdgeFactor K H psi p *
        activeBCWeight K (edgeSubsetInducedWiring K H B psi)
          (fun _ => p) q eta := by
      apply Finset.sum_congr rfl
      intro eta _
      exact bcWeight_edgeSubsetFibre_eq_induced
        K H B hKH psi p q eta
    _ = edgeSubsetExteriorEdgeFactor K H psi p *
        ∑ eta, activeBCWeight K (edgeSubsetInducedWiring K H B psi)
          (fun _ => p) q eta := by rw [Finset.mul_sum]


theorem edgeSubsetFibre_condBcProb_eq_activeBCProb
    (K H B : SimpleGraph V) [DecidableRel K.Adj]
    [DecidableRel H.Adj] [DecidableRel B.Adj]
    (hKH : K ≤ H) (psi : ConfigSpace (Sym2 V))
    {p q : Real} (hp : 0 < p) (hp1 : p < 1)
    (eta : ConfigSpace K.edgeSet) :
    condBcProb H B p q K.edgeFinset psi
        (edgeSubsetFibreConfig K psi eta) =
      activeBCProb K (edgeSubsetInducedWiring K H B psi)
        (fun _ => p) q eta := by
  unfold condBcProb activeBCProb
  rw [if_pos (edgeSubsetFibreConfig_agreesOff K psi eta)]
  rw [bcWeight_edgeSubsetFibre_eq_induced K H B hKH psi p q eta,
    edgeSubset_inducedBcZ_eq K H B hKH psi p q]
  exact mul_div_mul_left _ _ (by
    unfold edgeSubsetExteriorEdgeFactor
    apply Finset.prod_ne_zero_iff.mpr
    intro e he
    split
    · exact hp.ne'
    · exact (sub_pos.mpr hp1).ne')


end
end StatMech.FK
