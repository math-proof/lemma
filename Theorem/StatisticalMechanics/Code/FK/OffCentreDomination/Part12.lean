/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OffCentreDomination.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.WiredDominationInner.Part3
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.FK.DomainMarkov.Part5
import Theorem.StatisticalMechanics.Code.FK.IvProperties
import Theorem.StatisticalMechanics.Code.FK.LimitCommutation.Part5
import Theorem.StatisticalMechanics.Code.FK.MonotoneVolumeLimit
import Def.StatisticalMechanics.Code.FK.OffCentreDomination.Part16
open MeasureTheory Filter Topology SimpleGraph Set
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.Lattice


variable {Vin Vout : Type*} [Fintype Vin] [DecidableEq Vin] [Fintype Vout] [DecidableEq Vout]

variable (Gin : SimpleGraph Vin) [DecidableRel Gin.Adj]

variable (Gout : SimpleGraph Vout) [DecidableRel Gout.Adj]

variable (ιV : Vin → Vout)


variable {Gin Gout ιV}

variable (Gin Gout ιV)

variable (bdryOut : Vout → Prop) [DecidablePred bdryOut]


variable {Gin Gout ιV bdryOut}

variable (Gin Gout ιV bdryOut)


variable {Gin Gout ιV bdryOut}

variable (Gin Gout ιV bdryOut)


variable {Gin Gout ιV bdryOut}

variable (Gin Gout ιV bdryOut)


variable {Gin Gout ιV bdryOut}

theorem ocd_outProj_eq_false_of_range (hι : Function.Injective ιV) (ρ : ConfigSpace (Sym2 Vout))
    {e : Sym2 Vout} (he : e ∈ Set.range (ocd_innerEdge ιV)) :
    ocd_outProj ιV ρ e = false := by
  obtain ⟨e', rfl⟩ := he
  unfold ocd_outProj
  rw [ocd_psiExt_innerEdge hι]

theorem ocd_outProj_eq_of_not_range (ρ : ConfigSpace (Sym2 Vout))
    {e : Sym2 Vout} (he : e ∉ Set.range (ocd_innerEdge ιV)) :
    ocd_outProj ιV ρ e = ρ e := by
  unfold ocd_outProj
  rw [ocd_psiExt_eq_psi_of_not_range _ _ he]

theorem ocd_outProj_idem (hι : Function.Injective ιV) (ρ : ConfigSpace (Sym2 Vout)) :
    ocd_outProj ιV (ocd_outProj ιV ρ) = ocd_outProj ιV ρ := by
  funext e
  by_cases hin : e ∈ Set.range (ocd_innerEdge ιV)
  · rw [ocd_outProj_eq_false_of_range hι _ hin, ocd_outProj_eq_false_of_range hι ρ hin]
  · rw [ocd_outProj_eq_of_not_range _ hin]

theorem ocd_filter_outProj_eq_condFibre (hι : Function.Injective ιV) (ψ : ConfigSpace (Sym2 Vout))
    (hψ : ocd_outProj ιV ψ = ψ) :
    Finset.univ.filter (fun ρ => ocd_outProj ιV ρ = ψ)
      = condFibre (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ := by
  ext ρ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_condFibre]
  refine ⟨fun h e he => by
    rw [ocd_mem_innerEdgeFinset] at he
    rw [← ocd_outProj_eq_of_not_range ρ he, h], ?_⟩
  intro h
  have hpr : ocd_outProj ιV ρ = ocd_outProj ιV ψ := by
    funext e
    by_cases hin : e ∈ Set.range (ocd_innerEdge ιV)
    · rw [ocd_outProj_eq_false_of_range hι ρ hin, ocd_outProj_eq_false_of_range hι ψ hin]
    · have he : e ∉ ocd_innerEdgeFinset (Vin := Vin) ιV := by rw [ocd_mem_innerEdgeFinset]; exact hin
      rw [ocd_outProj_eq_of_not_range ρ hin, ocd_outProj_eq_of_not_range ψ hin, h e he]
  rw [hpr, hψ]


theorem ocd_sum_fibreMass_eq_one (hι : Function.Injective ιV) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ∑ ψ ∈ Finset.univ.filter (fun ψ => ocd_outProj ιV ψ = ψ),
        (∑ σ ∈ condFibre (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ,
          bcProb Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q σ) = 1 := by
  classical
  rw [show (∑ ψ ∈ Finset.univ.filter (fun ψ => ocd_outProj ιV ψ = ψ),
        (∑ σ ∈ condFibre (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ,
          bcProb Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q σ))
      = ∑ ψ ∈ Finset.univ.filter (fun ψ => ocd_outProj ιV ψ = ψ),
        (∑ σ ∈ Finset.univ.filter (fun ρ => ocd_outProj ιV ρ = ψ),
          bcProb Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q σ) from ?_]
  · rw [Finset.sum_fiberwise_of_maps_to
        (fun ρ _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, ocd_outProj_idem hι ρ⟩)]
    exact bcProb_sum_eq_one Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) hp hp1 hq
  · apply Finset.sum_congr rfl
    intro ψ hψ
    rw [Finset.mem_filter] at hψ
    rw [ocd_filter_outProj_eq_condFibre hι ψ hψ.2]


theorem ocd_bcProb_decompose (hι : Function.Injective ιV) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (B : Set (ConfigSpace (Sym2 Vout))) :
    (∑ ρ, B.indicator (fun _ => (1:ℝ)) ρ
        * bcProb Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q ρ)
      = ∑ ψ ∈ Finset.univ.filter (fun ψ => ocd_outProj ιV ψ = ψ),
          (∑ σ ∈ condFibre (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ,
            bcProb Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q σ)
          * (∑ ρ, B.indicator (fun _ => (1:ℝ)) ρ
              * condBcProb Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q
                  (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ ρ) := by
  classical
  set C := StatMech.Lattice.boundaryCliqueGraph bdryOut
  set F := ocd_innerEdgeFinset (Vin := Vin) ιV
  rw [← Finset.sum_fiberwise_of_maps_to
      (g := ocd_outProj ιV) (t := Finset.univ.filter (fun ψ => ocd_outProj ιV ψ = ψ))
      (fun ρ _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, ocd_outProj_idem hι ρ⟩)]
  apply Finset.sum_congr rfl
  intro ψ hψ
  rw [Finset.mem_filter] at hψ
  rw [ocd_filter_outProj_eq_condFibre hι ψ hψ.2]
  have hRHS : (∑ ρ, B.indicator (fun _ => (1:ℝ)) ρ * condBcProb Gout C p q F ψ ρ)
      = ∑ ρ ∈ condFibre F ψ, B.indicator (fun _ => (1:ℝ)) ρ * condBcProb Gout C p q F ψ ρ := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro ρ _ hρ
    rw [mem_condFibre] at hρ
    unfold condBcProb
    rw [if_neg hρ, mul_zero]
  rw [hRHS, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [mem_condFibre] at hρ
  have hbc := bcProb_eq_fibreMass_mul_condBcProb Gout C hp hp1 hq F ρ
  have hfib : condFibre F ρ = condFibre F ψ := by
    ext σ
    rw [mem_condFibre, mem_condFibre, agreesOff_congr (agreesOff_symm hρ)]
  rw [hfib] at hbc
  have hcc : condBcProb Gout C p q F ρ ρ = condBcProb Gout C p q F ψ ρ :=
    ocd_condBcProb_congr_dom Gout C p q F ρ ψ ρ (agreesOff_symm hρ)
  rw [hcc] at hbc
  rw [hbc]
  ring


theorem ocd_condBcProb_innerRestrict_le (hι : Function.Injective ιV)
    (hadjm : ocd_AdjMatch Gin Gout ιV) (bdryIn : Vin → Prop) [DecidablePred bdryIn]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (ψ : ConfigSpace (Sym2 Vout))
    (hwire : ocd_inducedWiring Gout ιV bdryOut ψ ≤ StatMech.Lattice.boundaryCliqueGraph bdryIn)
    {A : Set (ConfigSpace (Sym2 Vin))} (hA : IsIncreasing A) :
    (∑ ρ, (ocd_innerRestrict ιV ⁻¹' A).indicator (fun _ => (1:ℝ)) ρ
        * condBcProb Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q
            (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ ρ)
      ≤ ∑ ω, A.indicator (fun _ => (1:ℝ)) ω * wiredFkProb Gin bdryIn p q ω := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  rw [ocd_condBcProb_psiExt_sum_eq_inducedBox hι hadjm hp hp1 hq0 ψ (ocd_innerRestrict ιV ⁻¹' A)]
  have hpre : ocd_psiExt ιV ψ ⁻¹' (ocd_innerRestrict ιV ⁻¹' A) = A := by
    ext ω
    simp only [Set.mem_preimage, ocd_innerRestrict_psiExt hι]
  rw [hpre]
  exact ocd_condBcProb_psiExt_dominated hι hadjm bdryIn hp hp1 hq ψ hwire hA


theorem ocd_wired_inner_dominated_bcProb (hι : Function.Injective ιV)
    (hadjm : ocd_AdjMatch Gin Gout ιV) (bdryIn : Vin → Prop) [DecidablePred bdryIn]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (hwire : ∀ ψ : ConfigSpace (Sym2 Vout),
      ocd_inducedWiring Gout ιV bdryOut ψ ≤ StatMech.Lattice.boundaryCliqueGraph bdryIn)
    {A : Set (ConfigSpace (Sym2 Vin))} (hA : IsIncreasing A) :
    (∑ ρ, (ocd_innerRestrict ιV ⁻¹' A).indicator (fun _ => (1:ℝ)) ρ
        * bcProb Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q ρ)
      ≤ ∑ ω, A.indicator (fun _ => (1:ℝ)) ω * wiredFkProb Gin bdryIn p q ω := by
  have hq0 : 0 < q := lt_of_lt_of_le one_pos hq
  set c := ∑ ω, A.indicator (fun _ => (1:ℝ)) ω * wiredFkProb Gin bdryIn p q ω with hc
  rw [ocd_bcProb_decompose hι hp hp1 hq0 (ocd_innerRestrict ιV ⁻¹' A)]
  calc ∑ ψ ∈ Finset.univ.filter (fun ψ => ocd_outProj ιV ψ = ψ),
          (∑ σ ∈ condFibre (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ,
            bcProb Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q σ)
          * (∑ ρ, (ocd_innerRestrict ιV ⁻¹' A).indicator (fun _ => (1:ℝ)) ρ
              * condBcProb Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q
                  (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ ρ)
        ≤ ∑ ψ ∈ Finset.univ.filter (fun ψ => ocd_outProj ιV ψ = ψ),
            (∑ σ ∈ condFibre (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ,
              bcProb Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q σ) * c := by
          apply Finset.sum_le_sum
          intro ψ _
          apply mul_le_mul_of_nonneg_left
            (ocd_condBcProb_innerRestrict_le hι hadjm bdryIn hp hp1 hq ψ (hwire ψ) hA)
          exact Finset.sum_nonneg (fun σ _ =>
            bcProb_nonneg Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) hp hp1 hq0 σ)
    _ = (∑ ψ ∈ Finset.univ.filter (fun ψ => ocd_outProj ιV ψ = ψ),
            (∑ σ ∈ condFibre (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ,
              bcProb Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q σ)) * c := by
          rw [Finset.sum_mul]
    _ = c := by rw [ocd_sum_fibreMass_eq_one hι hp hp1 hq0, one_mul]


variable {d : ℕ}


theorem ocd_latticeAdjMatch {Sin Sout : Set (Site d)} [Fintype Sin] [Fintype Sout]
    (ιV : {y : Site d // y ∈ Sin} → {y : Site d // y ∈ Sout})
    (hιval : ∀ x, (ιV x : Site d) = (x : Site d)) :
    ocd_AdjMatch (SimpleGraph.comap Subtype.val (hypercubicLattice d))
      (SimpleGraph.comap Subtype.val (hypercubicLattice d)) ιV := by
  intro x y
  rw [SimpleGraph.comap_adj, SimpleGraph.comap_adj, hιval x, hιval y]


end FK
end StatMech
