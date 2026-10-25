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
import Instance.StatisticalMechanics.Code.FK.OffCentreDomination.Part6
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

theorem ocd_outsideGraph_le_fullGraph (ω : ConfigSpace (Sym2 Vin)) (ψ : ConfigSpace (Sym2 Vout)) :
    ocd_outsideGraph Gout ιV bdryOut ψ ≤ ocd_fullGraph Gout ιV bdryOut ω ψ := by
  intro x y h
  rw [ocd_fullGraph, SimpleGraph.sup_adj]
  rw [ocd_outsideGraph, SimpleGraph.sup_adj] at h
  rcases h with ⟨hadj, hopen, hr⟩ | hclique
  · left
    rw [openSub_adj]
    exact ⟨hadj, by rw [ocd_psiExt_eq_psi_of_not_range ψ ω hr]; exact hopen⟩
  · exact Or.inr hclique


theorem ocd_psiExt_eq_false_of_range (hι : Function.Injective ιV) (ψ : ConfigSpace (Sym2 Vout))
    (ω : ConfigSpace (Sym2 Vin)) {e : Sym2 Vout} (he : e ∈ Set.range (ocd_innerEdge ιV)) :
    ocd_psiExt ιV ψ ω e = ocd_psiExt ιV (fun _ => false) ω e := by
  obtain ⟨e', rfl⟩ := he
  rw [ocd_psiExt_innerEdge hι, ocd_psiExt_innerEdge hι]


theorem ocd_psiWiredGraph_eq_sup (hι : Function.Injective ιV) (ψ : ConfigSpace (Sym2 Vout))
    (ω : ConfigSpace (Sym2 Vin)) :
    ocd_fullGraph Gout ιV bdryOut ω ψ
      = ocd_innerImageGraph Gout ιV ω ⊔ ocd_outsideGraph Gout ιV bdryOut ψ := by
  ext x y
  rw [ocd_fullGraph, SimpleGraph.sup_adj, openSub_adj, SimpleGraph.sup_adj, ocd_outsideGraph,
    SimpleGraph.sup_adj]
  constructor
  · rintro (⟨hadj, hopen⟩ | hclique)
    · by_cases hr : s(x, y) ∈ Set.range (ocd_innerEdge ιV)
      · refine Or.inl ⟨hadj, ?_, hr⟩
        rw [← ocd_psiExt_eq_false_of_range hι ψ ω hr]; exact hopen
      · refine Or.inr (Or.inl ⟨hadj, ?_, hr⟩)
        rwa [ocd_psiExt_eq_psi_of_not_range ψ ω hr] at hopen
    · exact Or.inr (Or.inr hclique)
  · rintro (⟨hadj, hopen, hr⟩ | ⟨hadj, hopen, hr⟩ | hclique)
    · refine Or.inl ⟨hadj, ?_⟩
      rwa [ocd_psiExt_eq_false_of_range hι ψ ω hr]
    · refine Or.inl ⟨hadj, ?_⟩
      rwa [ocd_psiExt_eq_psi_of_not_range ψ ω hr]
    · exact Or.inr hclique


theorem ocd_innerImageGraph_adj_inner (hι : Function.Injective ιV) (ω : ConfigSpace (Sym2 Vin))
    {u v : Vout} (h : (ocd_innerImageGraph Gout ιV ω).Adj u v) :
    ocd_IsInnerVert ιV u ∧ ocd_IsInnerVert ιV v := by
  obtain ⟨_, _, hr⟩ := h
  obtain ⟨e, he⟩ := hr
  refine Sym2.inductionOn e (fun a b hab => ?_) he
  rw [ocd_innerEdge_mk, Sym2.eq_iff] at hab
  rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨⟨a, h1⟩, ⟨b, h2⟩⟩
  · exact ⟨⟨b, h2⟩, ⟨a, h1⟩⟩


theorem ocd_innerImageGraph_adj_ιV (hι : Function.Injective ιV)
    (hadjm : ocd_AdjMatch Gin Gout ιV) (ω : ConfigSpace (Sym2 Vin)) (x y : Vin) :
    (ocd_innerImageGraph Gout ιV ω).Adj (ιV x) (ιV y) ↔ (openSub Gin ω).Adj x y := by
  have he : s(ιV x, ιV y) = ocd_innerEdge ιV s(x, y) := (ocd_innerEdge_mk ιV x y).symm
  constructor
  · rintro ⟨hadj, hopen, _⟩
    refine ⟨(hadjm x y).mpr hadj, ?_⟩
    rw [he, ocd_psiExt_innerEdge hι] at hopen; exact hopen
  · rintro ⟨hadj, hopen⟩
    refine ⟨(hadjm x y).mp hadj, ?_, ⟨s(x, y), he.symm⟩⟩
    rw [he, ocd_psiExt_innerEdge hι]; exact hopen

theorem ocd_innerGraph_reachable_of_outsideReachable (ω : ConfigSpace (Sym2 Vin))
    (ψ : ConfigSpace (Sym2 Vout)) {x y : Vin}
    (h : (ocd_outsideGraph Gout ιV bdryOut ψ).Reachable (ιV x) (ιV y)) :
    (ocd_innerGraph Gin Gout ιV bdryOut ω ψ).Reachable x y := by
  by_cases hxy : x = y
  · subst hxy; exact SimpleGraph.Reachable.refl x
  · have hadj : (ocd_inducedWiring Gout ιV bdryOut ψ).Adj x y := ⟨hxy, h⟩
    exact (le_sup_right (a := openSub Gin ω) hadj).reachable

theorem ocd_fullGraph_reachable_of_innerGraph (hι : Function.Injective ιV)
    (hadjm : ocd_AdjMatch Gin Gout ιV) (ω : ConfigSpace (Sym2 Vin))
    (ψ : ConfigSpace (Sym2 Vout)) {x y : Vin}
    (h : (ocd_innerGraph Gin Gout ιV bdryOut ω ψ).Reachable x y) :
    (ocd_fullGraph Gout ιV bdryOut ω ψ).Reachable (ιV x) (ιV y) := by
  rw [ocd_psiWiredGraph_eq_sup hι]
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact SimpleGraph.Reachable.refl _
  | @tail u w _ hadj ih =>
      refine ih.trans ?_
      rw [ocd_innerGraph, SimpleGraph.sup_adj] at hadj
      rcases hadj with hopen | hwire
      · exact ((ocd_innerImageGraph_adj_ιV hι hadjm ω u w).mpr hopen).reachable.mono le_sup_left
      · refine hwire.2.mono ?_
        intro a b hab
        rw [SimpleGraph.sup_adj]; right; exact hab

theorem ocd_innerGraph_reachable_of_fullGraph (hι : Function.Injective ιV)
    (hadjm : ocd_AdjMatch Gin Gout ιV) (ω : ConfigSpace (Sym2 Vin))
    (ψ : ConfigSpace (Sym2 Vout)) {x y : Vin}
    (h : (ocd_fullGraph Gout ιV bdryOut ω ψ).Reachable (ιV x) (ιV y)) :
    (ocd_innerGraph Gin Gout ιV bdryOut ω ψ).Reachable x y := by
  rw [ocd_psiWiredGraph_eq_sup hι] at h
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  suffices H : ∀ w : Vout,
      Relation.ReflTransGen (ocd_innerImageGraph Gout ιV ω ⊔ ocd_outsideGraph Gout ιV bdryOut ψ).Adj
        (ιV x) w →
        ∃ x₀ : Vin, (ocd_innerGraph Gin Gout ιV bdryOut ω ψ).Reachable x x₀
          ∧ (ocd_outsideGraph Gout ιV bdryOut ψ).Reachable (ιV x₀) w by
    obtain ⟨x₀, hKx₀, hout⟩ := H (ιV y) h
    exact hKx₀.trans (ocd_innerGraph_reachable_of_outsideReachable ω ψ hout)
  intro w hw
  induction hw with
  | refl => exact ⟨x, SimpleGraph.Reachable.refl x, SimpleGraph.Reachable.refl _⟩
  | @tail u w _ hadj ih =>
      obtain ⟨x₀, hKx₀, hout⟩ := ih
      rw [SimpleGraph.sup_adj] at hadj
      rcases hadj with himg | hoadj
      · obtain ⟨hu, hw⟩ := ocd_innerImageGraph_adj_inner hι ω himg
        obtain ⟨u', rfl⟩ := hu
        obtain ⟨w', rfl⟩ := hw
        have hKu' : (ocd_innerGraph Gin Gout ιV bdryOut ω ψ).Reachable x₀ u' :=
          ocd_innerGraph_reachable_of_outsideReachable ω ψ hout
        have hstep : (ocd_innerGraph Gin Gout ιV bdryOut ω ψ).Adj u' w' :=
          le_sup_left (b := ocd_inducedWiring Gout ιV bdryOut ψ)
            ((ocd_innerImageGraph_adj_ιV hι hadjm ω u' w').mp himg)
        have hKw' : (ocd_innerGraph Gin Gout ιV bdryOut ω ψ).Reachable x w' :=
          ((hKx₀.trans hKu').trans hstep.reachable)
        exact ⟨w', hKw', SimpleGraph.Reachable.refl _⟩
      · exact ⟨x₀, hKx₀, hout.trans hoadj.reachable⟩

theorem ocd_fullGraph_reachable_ιV (hι : Function.Injective ιV)
    (hadjm : ocd_AdjMatch Gin Gout ιV) (ω : ConfigSpace (Sym2 Vin))
    (ψ : ConfigSpace (Sym2 Vout)) (x y : Vin) :
    (ocd_fullGraph Gout ιV bdryOut ω ψ).Reachable (ιV x) (ιV y)
      ↔ (ocd_innerGraph Gin Gout ιV bdryOut ω ψ).Reachable x y :=
  ⟨ocd_innerGraph_reachable_of_fullGraph hι hadjm ω ψ,
    ocd_fullGraph_reachable_of_innerGraph hι hadjm ω ψ⟩


theorem ocd_fullGraph_adj_of_outside (hι : Function.Injective ιV) (ω : ConfigSpace (Sym2 Vin))
    (ψ : ConfigSpace (Sym2 Vout)) {u w : Vout}
    (hu : ¬ ocd_IsInnerVert ιV u) (h : (ocd_fullGraph Gout ιV bdryOut ω ψ).Adj u w) :
    (ocd_outsideGraph Gout ιV bdryOut ψ).Adj u w := by
  rw [ocd_psiWiredGraph_eq_sup hι, SimpleGraph.sup_adj] at h
  rcases h with himg | hout
  · exact absurd (ocd_innerImageGraph_adj_inner hι ω himg).1 hu
  · exact hout

end FK
end StatMech
