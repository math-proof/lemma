/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredRibbon.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredCompletion.Part19
import Theorem.StatisticalMechanics.Code.FrontierA.PermCycleQuotientCount.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.FKTutte
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredRibbon
open Equiv SimpleGraph


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareWiredDartColor_localMate_ne
    (n : Nat)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    fkIsingSquareWiredDartSideColor
        (FKIsingMedialDart.localMate omega d).2 ≠
      fkIsingSquareWiredDartSideColor d.2 := by
  rcases d with ⟨e, side⟩
  cases h : omega e.1 <;> cases side <;>
    simp [FKIsingMedialDart.localMate,
      fkIsingSquareWiredDartSideColor, h]

theorem fkIsingSquareWiredBoundaryDart_turn
    (n : Nat) (hn : 0 < n) (i : FKIsingSquareWiredBoundaryDartIndex n) :
    (fkIsingSquareSideCorner
      (fkIsingSquareWiredBoundaryDart n hn i).2).2 =
      match i with
      | .bottom | .north _ => .clockwise
      | .west _ | .top => .counterclockwise := by
  cases i <;> simp [fkIsingSquareWiredBoundaryDart,
    fkIsingSquareDirectionDart_turn]

theorem fkIsingSquareWiredBondMate_turn_ne_of_boundary
    (n : Nat) (hn : 0 < n) (i : FKIsingSquareWiredBoundaryDartIndex n) :
    (fkIsingSquareSideCorner
      (fkIsingSquareWiredBondMate n hn
        (fkIsingSquareWiredBoundaryDart n hn i)).2).2 ≠
      (fkIsingSquareSideCorner
        (fkIsingSquareWiredBoundaryDart n hn i).2).2 := by
  cases i with
  | bottom => simp [fkIsingSquareWiredBoundaryDart_turn]
  | top => simp [fkIsingSquareWiredBoundaryDart_turn]
  | west k => simp [fkIsingSquareWiredBoundaryDart_turn]
  | north k => simp [fkIsingSquareWiredBoundaryDart_turn]

theorem fkIsingSquareWiredBondMate_turn_ne
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    (fkIsingSquareSideCorner (fkIsingSquareWiredBondMate n hn d).2).2 ≠
      (fkIsingSquareSideCorner d.2).2 := by
  let emb := fkIsingSquareWiredBoundaryEmbedding n hn
  let S := fkIsingSquareWiredShiftDartEquiv n hn
  by_cases hd : d ∈ Set.range emb
  · obtain ⟨i, rfl⟩ := hd
    exact fkIsingSquareWiredBondMate_turn_ne_of_boundary n hn i
  · have hSd : S.symm d = d := by
      have hforward : S d = d := by
        exact Equiv.Perm.viaFintypeEmbedding_apply_notMem_range _ _ hd
      apply S.injective
      rw [S.apply_symm_apply, hforward]
    have hBd : fkIsingSquareBondMate n hn d ∉ Set.range emb := by
      intro hmem
      obtain ⟨i, hi⟩ := hmem
      have hback := congrArg (fkIsingSquareBondMate n hn) hi
      rw [fkIsingSquareBondMate_involutive] at hback
      apply hd
      cases i with
      | bottom =>
          refine ⟨.west ⟨0, by omega⟩, ?_⟩
          exact (fkIsingSquareBondMate_wired_bottom n hn).symm.trans hback
      | west k =>
          by_cases hk : k.val = 0
          · have hkfin : k = ⟨0, by omega⟩ := Fin.ext hk
            refine ⟨.bottom, ?_⟩
            rw [hkfin] at hback
            exact (fkIsingSquareBondMate_wired_west_zero n hn).symm.trans hback
          · refine ⟨.north ⟨k.val - 1, by omega⟩, ?_⟩
            exact (fkIsingSquareBondMate_wired_west_succ n hn k hk).symm.trans hback
      | north k =>
          by_cases hk : k.val + 1 < 2 * n
          · refine ⟨.west ⟨k.val + 1, hk⟩, ?_⟩
            exact (fkIsingSquareBondMate_wired_north_not_last n hn k hk).symm.trans hback
          · refine ⟨.top, ?_⟩
            exact (fkIsingSquareBondMate_wired_north_last n hn k hk).symm.trans hback
      | top =>
          refine ⟨.north ⟨2 * n - 1, by omega⟩, ?_⟩
          exact (fkIsingSquareBondMate_wired_top n hn).symm.trans hback
    have hSB : S (fkIsingSquareBondMate n hn d) =
        fkIsingSquareBondMate n hn d := by
      exact Equiv.Perm.viaFintypeEmbedding_apply_notMem_range _ _ hBd
    have hwire : fkIsingSquareWiredBondMate n hn d =
        fkIsingSquareBondMate n hn d := by
      simp only [fkIsingSquareWiredBondMate,
        fkIsingSquareWiredBondMateEquiv, Equiv.Perm.mul_apply]
      rw [hSd]
      change S (fkIsingSquareBondMate n hn d) = _
      exact hSB
    rw [hwire]
    exact fkIsingSquareBondMate_cornerTurn_ne n hn d

theorem fkIsingSquareWiredBondColor_bondMate_ne
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    (!fkIsingSquareWiredTurnColor
        (fkIsingSquareSideCorner
          (fkIsingSquareWiredBondMate n hn d).2).2) ≠
      !fkIsingSquareWiredTurnColor (fkIsingSquareSideCorner d.2).2 := by
  have hturn := fkIsingSquareWiredBondMate_turn_ne n hn d
  generalize ha : (fkIsingSquareSideCorner
    (fkIsingSquareWiredBondMate n hn d).2).2 = a at hturn ⊢
  generalize hb : (fkIsingSquareSideCorner d.2).2 = b at hturn ⊢
  cases a <;> cases b <;>
    simp_all [fkIsingSquareWiredTurnColor]


end
end StatMech.Universality
