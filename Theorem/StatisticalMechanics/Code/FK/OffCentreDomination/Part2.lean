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
import Def.StatisticalMechanics.Code.FK.OffCentreDomination.Part2
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

theorem ocd_mem_innerEdgeFinset {e : Sym2 Vout} :
    e ∈ ocd_innerEdgeFinset (Vin := Vin) ιV ↔ e ∈ Set.range (ocd_innerEdge ιV) := by
  unfold ocd_innerEdgeFinset
  rw [Finset.mem_image]
  simp only [Finset.mem_univ, true_and, Set.mem_range]

theorem ocd_psiExt_innerEdge (hι : Function.Injective ιV) (ψ : ConfigSpace (Sym2 Vout))
    (ω : ConfigSpace (Sym2 Vin)) (e : Sym2 Vin) :
    ocd_psiExt ιV ψ ω (ocd_innerEdge ιV e) = ω e := by
  unfold ocd_psiExt
  have hmem : ocd_innerEdge ιV e ∈ Set.range (ocd_innerEdge ιV) := ⟨e, rfl⟩
  rw [dif_pos hmem]
  congr 1
  exact ocd_innerEdge_injective ιV hι hmem.choose_spec

theorem ocd_psiExt_eq_psi_of_not_range (ψ : ConfigSpace (Sym2 Vout))
    (ω : ConfigSpace (Sym2 Vin)) {e : Sym2 Vout}
    (he : e ∉ Set.range (ocd_innerEdge ιV)) : ocd_psiExt ιV ψ ω e = ψ e := by
  unfold ocd_psiExt; rw [dif_neg he]

theorem ocd_psiExt_innerEdge_pair (hι : Function.Injective ιV) (ψ : ConfigSpace (Sym2 Vout))
    (ω : ConfigSpace (Sym2 Vin)) (x y : Vin) :
    ocd_psiExt ιV ψ ω s(ιV x, ιV y) = ω s(x, y) := by
  have h : s(ιV x, ιV y) = ocd_innerEdge ιV s(x, y) := (ocd_innerEdge_mk ιV x y).symm
  rw [h, ocd_psiExt_innerEdge hι]


@[simp] theorem ocd_innerRestrict_psiExt (hι : Function.Injective ιV) (ψ : ConfigSpace (Sym2 Vout))
    (ω : ConfigSpace (Sym2 Vin)) : ocd_innerRestrict ιV (ocd_psiExt ιV ψ ω) = ω := by
  funext e; rw [ocd_innerRestrict, ocd_psiExt_innerEdge hι]

theorem ocd_agreesOff_psiExt (ψ : ConfigSpace (Sym2 Vout)) (ω : ConfigSpace (Sym2 Vin)) :
    AgreesOff (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ (ocd_psiExt ιV ψ ω) := by
  intro e he
  rw [ocd_mem_innerEdgeFinset] at he
  exact ocd_psiExt_eq_psi_of_not_range ψ ω he

theorem ocd_psiExt_innerRestrict_of_agreesOff (hι : Function.Injective ιV)
    {ψ ρ : ConfigSpace (Sym2 Vout)}
    (hρ : AgreesOff (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ ρ) :
    ocd_psiExt ιV ψ (ocd_innerRestrict ιV ρ) = ρ := by
  funext e
  unfold ocd_psiExt
  split
  · rename_i hmem
    show ocd_innerRestrict ιV ρ hmem.choose = ρ e
    rw [ocd_innerRestrict, hmem.choose_spec]
  · rename_i hmem
    have : e ∉ ocd_innerEdgeFinset (Vin := Vin) ιV := by rw [ocd_mem_innerEdgeFinset]; exact hmem
    exact (hρ e this).symm

theorem ocd_condFibre_eq_image_psiExt (hι : Function.Injective ιV) (ψ : ConfigSpace (Sym2 Vout)) :
    condFibre (ocd_innerEdgeFinset (Vin := Vin) ιV) ψ
      = Finset.univ.image (ocd_psiExt ιV ψ) := by
  ext ρ
  rw [mem_condFibre, Finset.mem_image]
  constructor
  · intro hρ
    exact ⟨ocd_innerRestrict ιV ρ, Finset.mem_univ _,
      ocd_psiExt_innerRestrict_of_agreesOff hι hρ⟩
  · rintro ⟨ω, _, rfl⟩
    exact ocd_agreesOff_psiExt ψ ω


end FK
end StatMech
