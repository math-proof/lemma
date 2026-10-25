/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexTorusDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexPeriodicDual.Part7
import Theorem.StatisticalMechanics.Code.BeffaraDC.Duality
import Def.StatisticalMechanics.Code.FK.TriHexTorusDuality.Part7
open Finset Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

theorem triHexTorus_dual_openCount (L : ℕ) [Fact (2 < L)]
    (omega : ConfigSpace (Sym2 (TorusSite L))) :
    FK.openCount (hexagonalTorusGraph L) (triHexTorusDualConfig L omega) =
      (hexagonalTorusGraph L).edgeFinset.card -
        FK.openCount (triangularTorusGraph L) omega := by
  classical
  unfold FK.openCount
  let EH := (hexagonalTorusGraph L).edgeFinset
  let ET := (triangularTorusGraph L).edgeFinset
  have hcardE : EH.card = ET.card := by
    simpa [EH, ET, SimpleGraph.edgeFinset] using
      (Fintype.card_congr (triHexTorusDualEdgeEquiv L)).symm
  have hopen : EH.filter (fun e => triHexTorusDualConfig L omega e = true) =
      EH.filter (fun e => omega (triHexTorusPrimalOfDualEdge L e) = false) := by
    ext e
    simp only [Finset.mem_filter]
    by_cases he : e ∈ EH
    · have heSet : e ∈ (hexagonalTorusGraph L).edgeSet := by
        simpa [EH, SimpleGraph.edgeFinset] using he
      simp only [he, true_and, triHexTorusDualConfig, dif_pos heSet]
      cases omega (triHexTorusPrimalOfDualEdge L e) <;> simp
    · simp [he]
  rw [hopen]
  have hclosed :
      (EH.filter (fun e => omega (triHexTorusPrimalOfDualEdge L e) = false)).card =
        (ET.filter (fun e => omega e = false)).card := by
    apply Finset.card_bij
        (fun e (_ : e ∈ EH.filter
          (fun e => omega (triHexTorusPrimalOfDualEdge L e) = false)) =>
            triHexTorusPrimalOfDualEdge L e)
    · intro e he
      simp only [Finset.mem_filter] at he ⊢
      exact ⟨triHexTorusPrimalOfDualEdge_mem L he.1, he.2⟩
    · intro a ha b hb hab
      simp only [Finset.mem_filter] at ha hb
      exact triHexTorusPrimalOfDualEdge_injOn L ha.1 hb.1 hab
    · intro b hb
      simp only [Finset.mem_filter] at hb
      have hbSet : b ∈ (triangularTorusGraph L).edgeSet := by
        simpa [ET, SimpleGraph.edgeFinset] using hb.1
      let tb : (triangularTorusGraph L).edgeSet := ⟨b, hbSet⟩
      let d : Sym2 (HexTorusVertex L) :=
        (triHexTorusDualEdgeEquiv L tb :
          (hexagonalTorusGraph L).edgeSet)
      have hdSet : d ∈ (hexagonalTorusGraph L).edgeSet :=
        (triHexTorusDualEdgeEquiv L tb).2
      have hd : d ∈ EH := by
        simpa [EH, SimpleGraph.edgeFinset] using hdSet
      have hdb : triHexTorusPrimalOfDualEdge L d = b := by
        simp only [triHexTorusPrimalOfDualEdge, dif_pos hdSet]
        exact congrArg Subtype.val ((triHexTorusDualEdgeEquiv L).symm_apply_apply tb)
      refine ⟨d, ?_, hdb⟩
      simp only [Finset.mem_filter]
      exact ⟨hd, hdb ▸ hb.2⟩
  rw [hclosed, hcardE]
  have hc := Finset.card_filter_add_card_filter_not
    (s := ET) (fun e => omega e = true)
  have hnot : ET.filter (fun e => ¬ omega e = true) =
      ET.filter (fun e => omega e = false) := by
    ext e
    simp only [Finset.mem_filter]
    cases omega e <;> simp
  rw [hnot] at hc
  have hopen_le : (ET.filter (fun e => omega e = true)).card ≤ ET.card :=
    Finset.card_filter_le _ _
  change (ET.filter (fun e => omega e = false)).card =
    ET.card - (ET.filter (fun e => omega e = true)).card
  omega


end PeriodicPlanar
end FK
end StatMech
