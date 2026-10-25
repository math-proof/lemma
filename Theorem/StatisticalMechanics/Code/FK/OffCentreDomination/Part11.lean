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
import Def.StatisticalMechanics.Code.FK.OffCentreDomination.Part15
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

theorem ocd_psiShift_pos (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    0 < ocd_psiShift Gout ιV bdryOut ψ p q :=
  mul_pos (ocd_psiEdgeFactor_pos hp hp1) (pow_pos hq _)


theorem ocd_bcWeight_psiExt (hι : Function.Injective ιV) (hadjm : ocd_AdjMatch Gin Gout ιV)
    {p q : ℝ} (ψ : ConfigSpace (Sym2 Vout)) (ω : ConfigSpace (Sym2 Vin)) :
    bcWeight Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q (ocd_psiExt ιV ψ ω)
      = bcWeight Gin (ocd_inducedWiring Gout ιV bdryOut ψ) p q ω
          * ocd_psiShift Gout ιV bdryOut ψ p q := by
  rw [bcWeight, ocd_numClustersBC_psiExt hι hadjm, ocd_edgeProduct_psiExt hι hadjm, bcWeight,
    ocd_psiShift, pow_add]
  ring


theorem ocd_inducedBcZ_psi (hι : Function.Injective ιV) (hadjm : ocd_AdjMatch Gin Gout ιV)
    {p q : ℝ} (ψ : ConfigSpace (Sym2 Vout)) :
    inducedBcZ Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q
        (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ
      = bcZ Gin (ocd_inducedWiring Gout ιV bdryOut ψ) p q
          * ocd_psiShift Gout ιV bdryOut ψ p q := by
  rw [inducedBcZ, ocd_condFibre_eq_image_psiExt hι,
    Finset.sum_image (fun a _ b _ h => by
      have := congrArg (ocd_innerRestrict ιV) h
      rwa [ocd_innerRestrict_psiExt hι, ocd_innerRestrict_psiExt hι] at this),
    bcZ, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun ω _ => ocd_bcWeight_psiExt hι hadjm ψ ω)


theorem ocd_condBcProb_psiExt_eq_bcProb (hι : Function.Injective ιV) (hadjm : ocd_AdjMatch Gin Gout ιV)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (ψ : ConfigSpace (Sym2 Vout)) (ω : ConfigSpace (Sym2 Vin)) :
    condBcProb Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q
        (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ (ocd_psiExt ιV ψ ω)
      = bcProb Gin (ocd_inducedWiring Gout ιV bdryOut ψ) p q ω := by
  rw [condBcProb, if_pos (ocd_agreesOff_psiExt ψ ω), ocd_bcWeight_psiExt hι hadjm,
    ocd_inducedBcZ_psi hι hadjm, bcProb,
    mul_div_mul_right _ _ (ocd_psiShift_pos hp hp1 hq).ne']


theorem ocd_condBcProb_psiExt_sum_eq_inducedBox (hι : Function.Injective ιV)
    (hadjm : ocd_AdjMatch Gin Gout ιV) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (ψ : ConfigSpace (Sym2 Vout)) (B : Set (ConfigSpace (Sym2 Vout))) :
    (∑ ρ, B.indicator (fun _ => (1:ℝ)) ρ *
        condBcProb Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q
          (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ ρ)
      = ∑ ω : ConfigSpace (Sym2 Vin),
          (ocd_psiExt ιV ψ ⁻¹' B).indicator (fun _ => (1:ℝ)) ω
            * bcProb Gin (ocd_inducedWiring Gout ιV bdryOut ψ) p q ω := by
  classical
  have hsupp : ∀ ρ ∉ condFibre (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ,
      B.indicator (fun _ => (1:ℝ)) ρ *
        condBcProb Gout (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q
          (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ ρ = 0 := by
    intro ρ hρ
    rw [mem_condFibre] at hρ
    unfold condBcProb
    rw [if_neg hρ, mul_zero]
  rw [← Finset.sum_subset (Finset.subset_univ (condFibre (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ))
    (fun ρ _ hρ => hsupp ρ hρ)]
  rw [ocd_condFibre_eq_image_psiExt hι]
  rw [Finset.sum_image (fun a _ b _ h => by
    have := congrArg (ocd_innerRestrict ιV) h
    rwa [ocd_innerRestrict_psiExt hι, ocd_innerRestrict_psiExt hι] at this)]
  apply Finset.sum_congr rfl
  intro ω _
  rw [ocd_condBcProb_psiExt_eq_bcProb hι hadjm hp hp1 hq ψ ω]
  have hind : B.indicator (fun _ => (1:ℝ)) (ocd_psiExt ιV ψ ω)
      = (ocd_psiExt ιV ψ ⁻¹' B).indicator (fun _ => (1:ℝ)) ω := by
    by_cases hω : ocd_psiExt ιV ψ ω ∈ B
    · rw [Set.indicator_of_mem hω, Set.indicator_of_mem (Set.mem_preimage.mpr hω)]
    · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem (fun h => hω (Set.mem_preimage.mp h))]
  rw [hind]


theorem ocd_condBcProb_psiExt_dominated (hι : Function.Injective ιV)
    (hadjm : ocd_AdjMatch Gin Gout ιV) (bdryIn : Vin → Prop) [DecidablePred bdryIn]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (ψ : ConfigSpace (Sym2 Vout))
    (hwire : ocd_inducedWiring Gout ιV bdryOut ψ ≤ StatMech.Lattice.boundaryCliqueGraph bdryIn)
    {A : Set (ConfigSpace (Sym2 Vin))} (hA : IsIncreasing A) :
    (∑ ω, A.indicator (fun _ => (1:ℝ)) ω
        * bcProb Gin (ocd_inducedWiring Gout ιV bdryOut ψ) p q ω)
      ≤ ∑ ω, A.indicator (fun _ => (1:ℝ)) ω
          * wiredFkProb Gin bdryIn p q ω := by
  refine (bcProb_mono_bc Gin (ocd_inducedWiring Gout ιV bdryOut ψ)
    (StatMech.Lattice.boundaryCliqueGraph bdryIn) hwire hp hp1 hq hA).trans_eq ?_
  exact Finset.sum_congr rfl (fun ω _ => by rw [bcProb_clique_eq_wiredFkProb])


theorem ocd_free_le_inducedBcProb (hι : Function.Injective ιV)
    (hadjm : ocd_AdjMatch Gin Gout ιV)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (ψ : ConfigSpace (Sym2 Vout))
    {A : Set (ConfigSpace (Sym2 Vin))} (hA : IsIncreasing A) :
    (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * fkProb Gin p q ω) ≤
      ∑ ω, A.indicator (fun _ => (1 : ℝ)) ω *
        bcProb Gin (ocd_inducedWiring Gout ιV bdryOut ψ) p q ω := by
  have hmono := bcProb_mono_bc Gin (⊥ : SimpleGraph Vin)
    (ocd_inducedWiring Gout ιV bdryOut ψ) bot_le hp hp1 hq hA
  simpa only [bcProb_bot_eq_fkProb] using hmono


theorem ocd_free_le_condBcProb_innerRestrict
    (hι : Function.Injective ιV)
    (hadjm : ocd_AdjMatch Gin Gout ιV)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (ψ : ConfigSpace (Sym2 Vout))
    {A : Set (ConfigSpace (Sym2 Vin))} (hA : IsIncreasing A) :
    (∑ ω, A.indicator (fun _ => (1 : ℝ)) ω * fkProb Gin p q ω) ≤
      ∑ ρ, (ocd_innerRestrict ιV ⁻¹' A).indicator
          (fun _ => (1 : ℝ)) ρ *
        condBcProb Gout
          (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q
          (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ ρ := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  rw [ocd_condBcProb_psiExt_sum_eq_inducedBox hι hadjm
    hp hp1 hq0 ψ (ocd_innerRestrict ιV ⁻¹' A)]
  have hpre : ocd_psiExt ιV ψ ⁻¹' (ocd_innerRestrict ιV ⁻¹' A) = A := by
    ext ω
    simp only [Set.mem_preimage, ocd_innerRestrict_psiExt hι]
  rw [hpre]
  exact ocd_free_le_inducedBcProb hι hadjm hp hp1 hq ψ hA


theorem ocd_condFibre_congr_dom {V : Type*} [Fintype V] [DecidableEq V]
    {F : Finset (Sym2 V)} {ψ ψ' : ConfigSpace (Sym2 V)} (h : AgreesOff F ψ ψ') :
    condFibre F ψ = condFibre F ψ' := by
  ext σ
  rw [mem_condFibre, mem_condFibre, agreesOff_congr h]


theorem ocd_condBcProb_congr_dom {V : Type*} [Fintype V] [DecidableEq V] (G C : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel C.Adj]
    (p q : ℝ) (F : Finset (Sym2 V)) (ψ ψ' ω : ConfigSpace (Sym2 V)) (h : AgreesOff F ψ ψ') :
    condBcProb G C p q F ψ ω = condBcProb G C p q F ψ' ω := by
  have hcond : AgreesOff F ψ ω ↔ AgreesOff F ψ' ω := by rw [agreesOff_congr h]
  have hfibre : condFibre F ψ = condFibre F ψ' := ocd_condFibre_congr_dom h
  unfold condBcProb inducedBcZ
  rw [hfibre]
  by_cases hω : AgreesOff F ψ ω
  · rw [if_pos hω, if_pos (hcond.mp hω)]
  · rw [if_neg hω, if_neg (fun h' => hω (hcond.mpr h'))]


end FK
end StatMech
