/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKDisjointBoxDomainMarkov.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.WiredDominationInner.Part3
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.FK.DomainMarkov.Part5
import Theorem.StatisticalMechanics.Code.Inequalities.FKG
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
import Def.StatisticalMechanics.Code.FK.FKDisjointBoxDomainMarkov
open scoped BigOperators
open SimpleGraph

set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

open ConfigSpace

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

variable (C : SimpleGraph V) [DecidableRel C.Adj]


theorem projOff_idem (F : Finset (Sym2 V)) (ψ : ConfigSpace (Sym2 V)) :
    projOff F (projOff F ψ) = projOff F ψ := by
  funext e; unfold projOff; by_cases h : e ∈ F <;> simp [h]

theorem agreesOff_projOff (F : Finset (Sym2 V)) (ψ : ConfigSpace (Sym2 V)) :
    AgreesOff F (projOff F ψ) ψ := by
  intro e he; unfold projOff; simp [he]

theorem projOff_eq_of_agreesOff {F : Finset (Sym2 V)} {ψ ρ : ConfigSpace (Sym2 V)}
    (h : AgreesOff F ψ ρ) : projOff F ρ = projOff F ψ := by
  funext e; unfold projOff
  by_cases he : e ∈ F
  · simp [he]
  · simp only [he, if_false]; exact (h e he)


theorem filter_projOff_eq_condFibre (F : Finset (Sym2 V)) (ψ : ConfigSpace (Sym2 V))
    (hψ : projOff F ψ = ψ) :
    Finset.univ.filter (fun ρ => projOff F ρ = ψ) = condFibre F ψ := by
  ext ρ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_condFibre]
  constructor
  · intro h e he
    have : projOff F ρ e = ψ e := by rw [h]
    unfold projOff at this; simpa [he] using this
  · intro h
    have : projOff F ρ = projOff F ψ := projOff_eq_of_agreesOff h
    rw [this, hψ]


theorem condFibre_congr_dom' {F : Finset (Sym2 V)} {ψ ψ' : ConfigSpace (Sym2 V)}
    (h : AgreesOff F ψ ψ') : condFibre F ψ = condFibre F ψ' := by
  ext σ; rw [mem_condFibre, mem_condFibre, agreesOff_congr h]


theorem condBcProb_congr_dom' (p q : ℝ) (F : Finset (Sym2 V))
    (ψ ψ' ω : ConfigSpace (Sym2 V)) (h : AgreesOff F ψ ψ') :
    condBcProb G C p q F ψ ω = condBcProb G C p q F ψ' ω := by
  have hcond : AgreesOff F ψ ω ↔ AgreesOff F ψ' ω := by rw [agreesOff_congr h]
  have hfibre : condFibre F ψ = condFibre F ψ' := condFibre_congr_dom' h
  unfold condBcProb inducedBcZ
  rw [hfibre]
  by_cases hω : AgreesOff F ψ ω
  · rw [if_pos hω, if_pos (hcond.mp hω)]
  · rw [if_neg hω, if_neg (fun h' => hω (hcond.mpr h'))]


end FK
end StatMech
