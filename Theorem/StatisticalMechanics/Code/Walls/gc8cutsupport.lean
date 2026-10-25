/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc8cutsupport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part10
import Theorem.StatisticalMechanics.Code.Ising.CurrentWeight.Part2
import Def.StatisticalMechanics.Code.Walls.gc8cutsupport
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option maxHeartbeats 800000


namespace StatMech.Walls

open StatMech.Ising StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem gc8_not_internal_both (S : Finset V) (e : Sym2 V)
    (h1 : acwInternal S e) (h2 : acwInternal Sᶜ e) : False := by
  unfold acwInternal at h1 h2
  induction e with
  | h a b =>
    exact (Finset.mem_compl.1 (h2 a (Sym2.mem_mk_left a b))) (h1 a (Sym2.mem_mk_left a b))


theorem gc8_cut_no_crossing (S : Finset V) (hcut : acwClosedCut G S) (e : Sym2 V)
    (he : e ∈ G.edgeFinset) : ¬ gc8Crosses S e := by
  rintro ⟨⟨u, hue, huS⟩, ⟨v, hve, hvS⟩⟩
  rcases hcut e he with h | h
  · exact hvS (h v hve)
  · exact (Finset.mem_compl.1 (h u hue)) huS


theorem gc8_restrict_internal_vanishes_cross (S : Finset V) (n : Ising.Current V) (e : Sym2 V)
    (hv : ∃ v ∈ e, v ∉ S) :
    acwRestrict (acwInternal S) n e = 0 := by
  unfold acwRestrict acwInternal
  obtain ⟨v, hve, hvS⟩ := hv
  exact if_neg (fun h => hvS (h v hve))


theorem gc8_restrict_external_vanishes_cross (S : Finset V) (n : Ising.Current V) (e : Sym2 V)
    (hu : ∃ u ∈ e, u ∈ S) :
    acwRestrict (acwInternal Sᶜ) n e = 0 := by
  unfold acwRestrict acwInternal
  obtain ⟨u, hue, huS⟩ := hu
  exact if_neg (fun h => (Finset.mem_compl.1 (h u hue)) huS)


theorem gc8_restrict_add (p : Sym2 V → Prop) [DecidablePred p] (n : Ising.Current V) (e : Sym2 V) :
    n e = acwRestrict p n e + acwRestrict (fun e => ¬ p e) n e := by
  unfold acwRestrict
  by_cases h : p e <;> simp [h]


theorem gc8_offS_eq_externalS (S : Finset V) (hcut : acwClosedCut G S) (n : Ising.Current V)
    (e : Sym2 V) (he : e ∈ G.edgeFinset) :
    acwRestrict (fun e => ¬ acwInternal S e) n e = acwRestrict (acwInternal Sᶜ) n e := by
  unfold acwRestrict
  rcases hcut e he with h | h
  · 
    rw [if_neg (by simp [h]),
        if_neg (fun hc => gc8_not_internal_both S e h hc)]
  · 
    rw [if_pos h, if_pos (fun hs => gc8_not_internal_both S e hs h)]


theorem gc8_current_split (S : Finset V) (hcut : acwClosedCut G S) (n : Ising.Current V)
    (e : Sym2 V) (he : e ∈ G.edgeFinset) :
    n e = acwRestrict (acwInternal S) n e + acwRestrict (acwInternal Sᶜ) n e := by
  rw [gc8_restrict_add (acwInternal S) n e, gc8_offS_eq_externalS G S hcut n e he]


theorem gc8_sources_internal_eq (S : Finset V) (hcut : acwClosedCut G S) (n : Ising.Current V) :
    Sharpness.sources G (acwRestrict (acwInternal S) n) = S ∩ Sharpness.sources G n := by
  rw [acw_sources_internal_eq G S hcut n, Finset.inter_comm]


theorem gc8_sources_external_eq (S : Finset V) (hcut : acwClosedCut G S) (n : Ising.Current V) :
    Sharpness.sources G (acwRestrict (acwInternal Sᶜ) n) = Sᶜ ∩ Sharpness.sources G n := by
  rw [acw_sources_external_eq G S hcut n, Finset.inter_comm]


theorem gc8_sources_split (S : Finset V) (hcut : acwClosedCut G S) (n : Ising.Current V) :
    Sharpness.sources G n
        = Sharpness.sources G (acwRestrict (acwInternal S) n)
          ∪ Sharpness.sources G (acwRestrict (acwInternal Sᶜ) n)
      ∧ Disjoint (Sharpness.sources G (acwRestrict (acwInternal S) n))
          (Sharpness.sources G (acwRestrict (acwInternal Sᶜ) n)) :=
  acw_sources_partition G S hcut n


end StatMech.Walls
