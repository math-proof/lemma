/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPathSplice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredCompletion.Part19
open Finset SimpleGraph


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareWiredBondMate_cornerTurn_ne
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) :
    (fkIsingSquareSideCorner (fkIsingSquareWiredBondMate n hn d).2).2 ≠
      (fkIsingSquareSideCorner d.2).2 := by
  classical
  let f := fkIsingSquareWiredBoundaryEmbedding n hn
  let sigma := fkIsingSquareWiredShiftDartEquiv n hn
  by_cases hd : ∃ i, d = fkIsingSquareWiredBoundaryDart n hn i
  · obtain ⟨i, rfl⟩ := hd
    cases i with
    | bottom =>
        rw [fkIsingSquareWiredBondMate_bottom]
        simp [fkIsingSquareWiredBoundaryDart]
    | west k =>
        rw [fkIsingSquareWiredBondMate_west]
        simp [fkIsingSquareWiredBoundaryDart]
    | north k =>
        rw [fkIsingSquareWiredBondMate_north]
        simp [fkIsingSquareWiredBoundaryDart]
    | top =>
        rw [fkIsingSquareWiredBondMate_top]
        simp [fkIsingSquareWiredBoundaryDart]
  · have hdRange : d ∉ Set.range f := by
      rintro ⟨i, hi⟩
      exact hd ⟨i, hi.symm⟩
    have hsigma : sigma d = d := by
      exact Equiv.Perm.viaFintypeEmbedding_apply_notMem_range _ f hdRange
    have hsigmaInv : sigma.symm d = d := by
      apply sigma.injective
      simpa [hsigma]
    have hBd : fkIsingSquareBondMate n hn d ∉ Set.range f := by
      intro hmem
      obtain ⟨i, hi⟩ := hmem
      have hB : fkIsingSquareBondMate n hn (f i) = d := by
        calc
          fkIsingSquareBondMate n hn (f i) =
              fkIsingSquareBondMate n hn (fkIsingSquareBondMate n hn d) :=
            congrArg (fkIsingSquareBondMate n hn) hi
          _ = d := fkIsingSquareBondMate_involutive n hn d
      apply hd
      cases i with
      | bottom =>
          refine ⟨.west ⟨0, by omega⟩, ?_⟩
          change fkIsingSquareBondMate n hn
            (fkIsingSquareWiredBoundaryDart n hn .bottom) = d at hB
          rw [fkIsingSquareBondMate_wired_bottom] at hB
          exact hB.symm
      | west k =>
          by_cases hk : k.val = 0
          · have hk0 : k = ⟨0, by omega⟩ := Fin.ext hk
            refine ⟨.bottom, ?_⟩
            change fkIsingSquareBondMate n hn
              (fkIsingSquareWiredBoundaryDart n hn (.west k)) = d at hB
            rw [hk0] at hB
            rw [fkIsingSquareBondMate_wired_west_zero] at hB
            exact hB.symm
          · refine ⟨.north ⟨k.val - 1, by omega⟩, ?_⟩
            change fkIsingSquareBondMate n hn
              (fkIsingSquareWiredBoundaryDart n hn (.west k)) = d at hB
            rw [fkIsingSquareBondMate_wired_west_succ n hn k hk] at hB
            exact hB.symm
      | north k =>
          by_cases hk : k.val + 1 < 2 * n
          · refine ⟨.west ⟨k.val + 1, hk⟩, ?_⟩
            change fkIsingSquareBondMate n hn
              (fkIsingSquareWiredBoundaryDart n hn (.north k)) = d at hB
            rw [fkIsingSquareBondMate_wired_north_not_last n hn k hk] at hB
            exact hB.symm
          · refine ⟨.top, ?_⟩
            change fkIsingSquareBondMate n hn
              (fkIsingSquareWiredBoundaryDart n hn (.north k)) = d at hB
            rw [fkIsingSquareBondMate_wired_north_last n hn k hk] at hB
            exact hB.symm
      | top =>
          refine ⟨.north ⟨2 * n - 1, by omega⟩, ?_⟩
          change fkIsingSquareBondMate n hn
            (fkIsingSquareWiredBoundaryDart n hn .top) = d at hB
          rw [fkIsingSquareBondMate_wired_top] at hB
          exact hB.symm
    have hsigmaB : sigma (fkIsingSquareBondMate n hn d) =
        fkIsingSquareBondMate n hn d := by
      exact Equiv.Perm.viaFintypeEmbedding_apply_notMem_range _ f hBd
    change (fkIsingSquareSideCorner
      (sigma (fkIsingSquareBondMate n hn (sigma.symm d))).2).2 ≠ _
    rw [hsigmaInv, hsigmaB]
    exact fkIsingSquareBondMate_cornerTurn_ne n hn d


end
end StatMech.Universality
