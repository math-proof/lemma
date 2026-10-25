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
import Instance.StatisticalMechanics.Code.FK.OffCentreDomination.Part8
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

variable {d : ℕ}


variable {Sin Sout : Set (Site d)}

theorem ocd_bdryIn_of_outsideGraph_adj [Fintype Sin] [Fintype Sout]
    (ιV : {y : Site d // y ∈ Sin} → {y : Site d // y ∈ Sout})
    (hιval : ∀ x, (ιV x : Site d) = (x : Site d))
    (bdryOut : {y : Site d // y ∈ Sout} → Prop) [DecidablePred bdryOut]
    (bdryIn : {y : Site d // y ∈ Sin} → Prop) [DecidablePred bdryIn]
    (hmargin : ∀ x : {y : Site d // y ∈ Sin}, ¬ bdryOut (ιV x))
    (hbdryIn : ∀ (x : {y : Site d // y ∈ Sin}) (z : Site d),
      NearestNeighbour d (x : Site d) z → z ∉ Sin → bdryIn x)
    (ψ : ConfigSpace (Sym2 {y : Site d // y ∈ Sout}))
    {x : {y : Site d // y ∈ Sin}} {z : {y : Site d // y ∈ Sout}}
    (h : (ocd_outsideGraph (SimpleGraph.comap Subtype.val (hypercubicLattice d)) ιV bdryOut ψ).Adj
        (ιV x) z) :
    bdryIn x := by
  rw [ocd_outsideGraph_adj] at h
  rcases h with ⟨hadj, hopen, hrange⟩ | ⟨hne, hb1, hb2⟩
  · 
    have hznot : (z : Site d) ∉ Sin := by
      intro hz
      refine hrange ⟨s(x, ⟨(z : Site d), hz⟩), ?_⟩
      rw [ocd_innerEdge_mk]
      have hzeq : ιV ⟨(z : Site d), hz⟩ = z := Subtype.ext (hιval ⟨(z : Site d), hz⟩)
      rw [hzeq]
    have hnn : NearestNeighbour d (x : Site d) (z : Site d) := by
      have hcp := hadj
      rw [SimpleGraph.comap_adj] at hcp
      rw [hιval x] at hcp
      exact hcp
    exact hbdryIn x (z : Site d) hnn hznot
  · exact absurd hb1 (hmargin x)


theorem ocd_latticeInducedWiring_le [Fintype Sin] [Fintype Sout]
    (ιV : {y : Site d // y ∈ Sin} → {y : Site d // y ∈ Sout})
    (hιval : ∀ x, (ιV x : Site d) = (x : Site d)) (hιinj : Function.Injective ιV)
    (bdryOut : {y : Site d // y ∈ Sout} → Prop) [DecidablePred bdryOut]
    (bdryIn : {y : Site d // y ∈ Sin} → Prop) [DecidablePred bdryIn]
    (hmargin : ∀ x : {y : Site d // y ∈ Sin}, ¬ bdryOut (ιV x))
    (hbdryIn : ∀ (x : {y : Site d // y ∈ Sin}) (z : Site d),
      NearestNeighbour d (x : Site d) z → z ∉ Sin → bdryIn x)
    (ψ : ConfigSpace (Sym2 {y : Site d // y ∈ Sout})) :
    ocd_inducedWiring (SimpleGraph.comap Subtype.val (hypercubicLattice d)) ιV bdryOut ψ
      ≤ StatMech.Lattice.boundaryCliqueGraph bdryIn := by
  intro x y hxy
  obtain ⟨hne, hreach⟩ := hxy
  rw [StatMech.Lattice.boundaryCliqueGraph_adj]
  refine ⟨hne, ?_, ?_⟩
  · 
    have hne' : ιV x ≠ ιV y := fun he => hne (hιinj he)
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
    rcases hreach.cases_head with heq | ⟨c, hadj, _⟩
    · exact absurd heq hne'
    · exact ocd_bdryIn_of_outsideGraph_adj ιV hιval bdryOut bdryIn hmargin hbdryIn ψ hadj
  · 
    have hreach' :
        (ocd_outsideGraph (SimpleGraph.comap Subtype.val (hypercubicLattice d)) ιV bdryOut ψ).Reachable
          (ιV y) (ιV x) := hreach.symm
    have hne' : ιV y ≠ ιV x := fun he => hne (hιinj he).symm
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach'
    rcases hreach'.cases_head with heq | ⟨c, hadj, _⟩
    · exact absurd heq hne'
    · exact ocd_bdryIn_of_outsideGraph_adj ιV hιval bdryOut bdryIn hmargin hbdryIn ψ hadj


theorem ocd_latticeWired_inner_dominated [Fintype Sin] [Fintype Sout]
    (ιV : {y : Site d // y ∈ Sin} → {y : Site d // y ∈ Sout})
    (hιval : ∀ x, (ιV x : Site d) = (x : Site d)) (hιinj : Function.Injective ιV)
    (bdryOut : {y : Site d // y ∈ Sout} → Prop) [DecidablePred bdryOut]
    (bdryIn : {y : Site d // y ∈ Sin} → Prop) [DecidablePred bdryIn]
    (hmargin : ∀ x : {y : Site d // y ∈ Sin}, ¬ bdryOut (ιV x))
    (hbdryIn : ∀ (x : {y : Site d // y ∈ Sin}) (z : Site d),
      NearestNeighbour d (x : Site d) z → z ∉ Sin → bdryIn x)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace (Sym2 {y : Site d // y ∈ Sin}))} (hA : IsIncreasing A) :
    (∑ ρ, (ocd_innerRestrict ιV ⁻¹' A).indicator (fun _ => (1:ℝ)) ρ
        * wiredFkProb (SimpleGraph.comap Subtype.val (hypercubicLattice d)) bdryOut p q ρ)
      ≤ ∑ ω, A.indicator (fun _ => (1:ℝ)) ω
          * wiredFkProb (SimpleGraph.comap Subtype.val (hypercubicLattice d)) bdryIn p q ω := by
  have hadjm := ocd_latticeAdjMatch ιV hιval
  have hwire := fun ψ => ocd_latticeInducedWiring_le ιV hιval hιinj bdryOut bdryIn hmargin hbdryIn ψ
  have hdom := ocd_wired_inner_dominated_bcProb hιinj hadjm bdryIn hp hp1 hq hwire hA
  refine le_trans ?_ hdom
  apply le_of_eq
  refine Finset.sum_congr rfl (fun ρ _ => ?_)
  rw [bcProb_clique_eq_wiredFkProb]


theorem ocd_innerRestrict_preimage_multiOpenEvent (hι : Function.Injective ιV)
    (t : Finset (Sym2 Vin)) :
    ocd_innerRestrict ιV ⁻¹' (med_genericMultiOpenEvent t)
      = med_genericMultiOpenEvent (t.image (ocd_innerEdge ιV)) := by
  ext ρ
  simp only [Set.mem_preimage, med_genericMultiOpenEvent, Set.mem_setOf_eq, ocd_innerRestrict,
    Finset.forall_mem_image]


theorem ocd_latticeWired_multiMass_dominated [Fintype Sin] [Fintype Sout]
    (ιV : {y : Site d // y ∈ Sin} → {y : Site d // y ∈ Sout})
    (hιval : ∀ x, (ιV x : Site d) = (x : Site d)) (hιinj : Function.Injective ιV)
    (bdryOut : {y : Site d // y ∈ Sout} → Prop) [DecidablePred bdryOut]
    (bdryIn : {y : Site d // y ∈ Sin} → Prop) [DecidablePred bdryIn]
    (hmargin : ∀ x : {y : Site d // y ∈ Sin}, ¬ bdryOut (ιV x))
    (hbdryIn : ∀ (x : {y : Site d // y ∈ Sin}) (z : Site d),
      NearestNeighbour d (x : Site d) z → z ∉ Sin → bdryIn x)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (t : Finset (Sym2 {y : Site d // y ∈ Sin})) :
    med_multiMassProb
        (wiredFkProb (SimpleGraph.comap Subtype.val (hypercubicLattice d)) bdryOut p q)
        (t.image (ocd_innerEdge ιV))
      ≤ med_multiMassProb
          (wiredFkProb (SimpleGraph.comap Subtype.val (hypercubicLattice d)) bdryIn p q) t := by
  have hdom := ocd_latticeWired_inner_dominated ιV hιval hιinj bdryOut bdryIn hmargin hbdryIn
    hp hp1 hq (A := med_genericMultiOpenEvent t) (med_genericMultiOpenEvent_increasing t)
  rw [ocd_innerRestrict_preimage_multiOpenEvent hιinj t] at hdom
  exact hdom

end FK
end StatMech
