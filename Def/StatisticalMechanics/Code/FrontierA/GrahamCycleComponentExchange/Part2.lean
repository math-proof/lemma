/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCycleComponentExchange.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part17
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCycleComponentExchange
open Finset


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]

noncomputable def cyclePairComponentExchangeEmbedding
    (ends : I → Sym2 W) (K L : Finset I) (u v : W)
    (hKL : Disjoint K L) :
    boundarySector ends K ∅ × boundarySector ends L ∅ ↪
      boundarySector ends
          ((K \ edgeComponent ends K u) ∪ edgeComponent ends L v) ∅ ×
        boundarySector ends
          ((L \ edgeComponent ends L v) ∪ edgeComponent ends K u) ∅ := by
  classical
  let A := edgeComponent ends K u
  let B := edgeComponent ends L v
  have hAK : A ⊆ K := by
    intro i hi
    change i ∈ edgeComponent ends K u at hi
    rw [edgeComponent, Finset.mem_filter] at hi
    exact hi.1
  have hBL : B ⊆ L := by
    intro i hi
    change i ∈ edgeComponent ends L v at hi
    rw [edgeComponent, Finset.mem_filter] at hi
    exact hi.1
  let f : boundarySector ends K ∅ × boundarySector ends L ∅ →
      boundarySector ends ((K \ A) ∪ B) ∅ ×
        boundarySector ends ((L \ B) ∪ A) ∅ := fun p => by
    let P := p.1.1
    let Q := p.2.1
    let P' := (P \ A) ∪ (Q ∩ B)
    let Q' := (Q \ B) ∪ (P ∩ A)
    have hPA : sources ends (P \ A) = ∅ := by
      simpa only [A, P] using
        sources_cycle_component_complement p.1.2.1 p.1.2.2 u
    have hQB : sources ends (Q ∩ B) = ∅ := by
      simpa only [B, Q] using sources_cycle_component_part p.2.2.1 p.2.2.2 v
    have hQB' : sources ends (Q \ B) = ∅ := by
      simpa only [B, Q] using
        sources_cycle_component_complement p.2.2.1 p.2.2.2 v
    have hPA' : sources ends (P ∩ A) = ∅ := by
      simpa only [A, P] using sources_cycle_component_part p.1.2.1 p.1.2.2 u
    have hd1 : Disjoint (P \ A) (Q ∩ B) := by
      exact hKL.mono (Finset.sdiff_subset.trans p.1.2.1)
        (Finset.inter_subset_left.trans p.2.2.1)
    have hd2 : Disjoint (Q \ B) (P ∩ A) := by
      exact hKL.symm.mono (Finset.sdiff_subset.trans p.2.2.1)
        (Finset.inter_subset_left.trans p.1.2.1)
    exact
      (⟨P',
        ⟨by
          intro i hi
          rcases Finset.mem_union.mp hi with hi | hi
          · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr
              ⟨p.1.2.1 (Finset.mem_sdiff.mp hi).1, (Finset.mem_sdiff.mp hi).2⟩)
          · exact Finset.mem_union_right _ (Finset.mem_inter.mp hi).2,
          by rw [sources_union_of_disjoint hd1, hPA, hQB]; simp⟩⟩,
       ⟨Q',
        ⟨by
          intro i hi
          rcases Finset.mem_union.mp hi with hi | hi
          · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr
              ⟨p.2.2.1 (Finset.mem_sdiff.mp hi).1, (Finset.mem_sdiff.mp hi).2⟩)
          · exact Finset.mem_union_right _ (Finset.mem_inter.mp hi).2,
          by rw [sources_union_of_disjoint hd2, hQB', hPA']; simp⟩⟩)
  refine ⟨f, ?_⟩
  intro p q hpq
  have hval := congrArg (fun r => (r.1.1, r.2.1)) hpq
  change exchangeCyclePair A B (p.1.1, p.2.1) =
    exchangeCyclePair A B (q.1.1, q.2.1) at hval
  have hp := exchangeCyclePair_leftInverse hKL hAK hBL p.1.2.1 p.2.2.1
  have hq := exchangeCyclePair_leftInverse hKL hAK hBL q.1.2.1 q.2.2.1
  have hinv := congrArg (exchangeCyclePair B A) hval
  rw [hp, hq] at hinv
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg Prod.fst hinv
  · apply Subtype.ext
    exact congrArg Prod.snd hinv


end StatMech.GrahamGHS.FourColor
