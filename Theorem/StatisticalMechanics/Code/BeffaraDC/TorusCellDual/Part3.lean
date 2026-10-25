/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusCellCrossing.Part4
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusDefectComplement.Part2
import Def.StatisticalMechanics.Code.BeffaraDC.TorusCellDual.Part3
open SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.Onsager


theorem torusCellPrimal_mem_openSub_iff (L : ℕ) [Fact (2 < L)]
    (ω : ConfigSpace (Sym2 (ZMod L × ZMod L)))
    {e : Sym2 (ZMod L × ZMod L)}
    (he : e ∈ (onsTorusGraph L).edgeFinset) :
    torusCellPrimalOfDualEdge L e ∈
        (FK.openSub (onsTorusGraph L) ω).edgeSet ↔
      ω (torusCellPrimalOfDualEdge L e) = true := by
  let pe := torusCellPrimalOfDualEdge L e
  have hp : pe ∈ (onsTorusGraph L).edgeFinset := by
    simpa [pe] using torusCellPrimalOfDualEdge_mem L he
  change pe ∈ (FK.openSub (onsTorusGraph L) ω).edgeSet ↔ ω pe = true
  revert hp
  induction pe using Sym2.inductionOn with
  | _ p q =>
      intro hp
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at hp
      rw [SimpleGraph.mem_edgeSet, FK.openSub_adj]
      exact and_iff_right hp


theorem torusCell_openSub_dualConfig (L : ℕ) [Fact (2 < L)]
    (ω : ConfigSpace (Sym2 (ZMod L × ZMod L))) :
    FK.openSub (onsTorusGraph L) (torusCellDualConfig L ω) =
      torusCellDualCutGraph L (FK.openSub (onsTorusGraph L) ω) := by
  ext f g
  by_cases hfg : (onsTorusGraph L).Adj f g
  · have he : s(f, g) ∈ (onsTorusGraph L).edgeFinset := by
      simpa only [SimpleGraph.mem_edgeFinset]
    simp only [FK.openSub_adj, torusCellDualCutGraph_adj, hfg, true_and,
      torusCellDualConfig, dif_pos he]
    rw [torusCellPrimal_mem_openSub_iff L ω he]
    cases ω (torusCellPrimalOfDualEdge L s(f, g)) <;> simp
  · simp [FK.openSub_adj, torusCellDualCutGraph_adj, hfg]


theorem torusCell_dual_openCount (L : ℕ) [Fact (2 < L)]
    (ω : ConfigSpace (Sym2 (ZMod L × ZMod L))) :
    FK.openCount (onsTorusGraph L) (torusCellDualConfig L ω) =
      (onsTorusGraph L).edgeFinset.card -
        FK.openCount (onsTorusGraph L) ω := by
  classical
  unfold FK.openCount
  let E := (onsTorusGraph L).edgeFinset
  have hopen : E.filter (fun e => torusCellDualConfig L ω e = true) =
      E.filter (fun e => ω (torusCellPrimalOfDualEdge L e) = false) := by
    ext e
    simp only [Finset.mem_filter]
    by_cases he : e ∈ E
    · have he' : e ∈ (onsTorusGraph L).edgeFinset := by
        simpa [E] using he
      simp only [he, true_and, torusCellDualConfig, dif_pos he']
      cases ω (torusCellPrimalOfDualEdge L e) <;> simp
    · simp [he]
  rw [hopen]
  have hcard :
      (E.filter (fun e => ω (torusCellPrimalOfDualEdge L e) = false)).card =
        (E.filter (fun e => ω e = false)).card := by
    apply Finset.card_bij
        (fun e (_he : e ∈ E.filter
          (fun e => ω (torusCellPrimalOfDualEdge L e) = false)) =>
            torusCellPrimalOfDualEdge L e)
    · intro e he
      simp only [Finset.mem_filter] at he ⊢
      exact ⟨torusCellPrimalOfDualEdge_mem L he.1, he.2⟩
    · intro a ha b hb hab
      have ha' := (Finset.mem_filter.mp ha).1
      have hb' := (Finset.mem_filter.mp hb).1
      exact torusCellPrimalOfDualEdge_injOn L ha' hb' hab
    · intro b hb
      simp only [Finset.mem_filter] at hb
      let eb : TorusAmbientEdge L := ⟨b, hb.1⟩
      let d : Sym2 (ZMod L × ZMod L) :=
        (torusCellCrossing L eb : TorusAmbientEdge L)
      have hd : d ∈ E := (torusCellCrossing L eb).2
      have hdb : torusCellPrimalOfDualEdge L d = b := by
        rw [torusCellPrimalOfDualEdge_of_mem L hd]
        exact congrArg Subtype.val ((torusCellCrossing L).symm_apply_apply eb)
      refine ⟨d, ?_, hdb⟩
      simp only [Finset.mem_filter]
      exact ⟨hd, hdb ▸ hb.2⟩
  rw [hcard]
  have hc := Finset.card_filter_add_card_filter_not
    (s := E) (fun e => ω e = true)
  have hnot : E.filter (fun e => ¬ ω e = true) =
      E.filter (fun e => ω e = false) := by
    ext e
    simp only [Finset.mem_filter]
    cases ω e <;> simp
  rw [hnot] at hc
  change (E.filter (fun e => ω e = false)).card =
    E.card - (E.filter (fun e => ω e = true)).card
  omega


@[simp] theorem torusCellDualCutGraph_bot (L : ℕ) [Fact (2 < L)] :
    torusCellDualCutGraph L
      (⊥ : SimpleGraph (ZMod L × ZMod L)) = onsTorusGraph L := by
  ext f g
  simp [torusCellDualCutGraph_adj]


theorem torusCellDualCutGraph_full (L : ℕ) [Fact (2 < L)] :
    torusCellDualCutGraph L (onsTorusGraph L) = ⊥ := by
  ext f g
  simp only [torusCellDualCutGraph_adj, bot_adj, iff_false]
  rintro ⟨hfg, hwall⟩
  apply hwall
  have heSet : s(f, g) ∈ (onsTorusGraph L).edgeSet := by
    rw [SimpleGraph.mem_edgeSet]
    exact hfg
  have he : s(f, g) ∈ (onsTorusGraph L).edgeFinset := by
    simpa [SimpleGraph.edgeFinset] using heSet
  have hp := torusCellPrimalOfDualEdge_mem L he
  simpa [SimpleGraph.edgeFinset] using hp


end StatMech.BeffaraDC
