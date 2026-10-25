/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredFullFaces.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredClosedFibers.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredRibbon.Part9
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredFullFaces.Part6


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open StatMech.FrontierA

noncomputable section

theorem fkIsingSquareWiredFullLeftDart_step
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    fkIsingSquareWiredBlackBoundaryPerm n hn
        (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset)
        (fkIsingSquareWiredFullLeftDart n hn k) =
      fkIsingSquareWiredFullLeftBond n hn k := by
  have hopen : FK.edgeSetConfig (boxGraph 2 n).edgeFinset
      (fkIsingSquareLeftVerticalEdge n hn k).1 = true := by
    rw [FK.edgeSetConfig_apply]
    exact SimpleGraph.mem_edgeFinset.mpr
      (fkIsingSquareLeftVerticalEdge n hn k).2
  have hlocal : FKIsingMedialDart.localMate
      (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset)
        (fkIsingSquareLeftVerticalEdge n hn k, .west) =
      (fkIsingSquareLeftVerticalEdge n hn k, .north) := by
    simp [FKIsingMedialDart.localMate, FK.edgeSetConfig]
  apply Subtype.ext
  simp only [fkIsingSquareWiredFullLeftDart,
    fkIsingSquareWiredFullLeftBond]
  simp only [fkIsingSquareWiredBoundaryDart_west_eq_leftEdge,
    fkIsingSquareWiredBoundaryDart_north_eq_leftEdge]
  simp [fkIsingSquareWiredBlackBoundaryPerm,
    fkIsingSquareWiredBoundaryStep, fkIsingSquareWiredTransitionEquiv,
    fkIsingSquareWiredTransitionMate, fkIsingSquareWiredCompletedIncidenceEquiv,
    fkIsingSquareWiredFullLeftDart, fkIsingSquareWiredFullLeftBond,
    show FKIsingMedialDart.localMate
      (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset)
        (fkIsingSquareLeftVerticalEdge n hn k, .west) =
      (fkIsingSquareLeftVerticalEdge n hn k, .north) from hlocal]
  exact hlocal

theorem fkIsingSquareWiredFullLeftBond_step
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    fkIsingSquareWiredBlackBoundaryPerm n hn
        (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset)
        (fkIsingSquareWiredFullLeftBond n hn k) =
      fkIsingSquareWiredFullLeftDart n hn k := by
  have hns : fkIsingSquareWiredBoundaryDart n hn (.north k) ≠
      fkIsingSquareWiredSourceDart n hn := by
    intro h
    have hi := fkIsingSquareWiredBoundaryDart_injective n hn h
    cases hi
  have hnt : fkIsingSquareWiredBoundaryDart n hn (.north k) ≠
      fkIsingSquareWiredTerminalDart n hn := by
    intro h
    have hi := fkIsingSquareWiredBoundaryDart_injective n hn h
    cases hi
  apply Subtype.ext
  simp [fkIsingSquareWiredBlackBoundaryPerm,
    fkIsingSquareWiredBoundaryStep, fkIsingSquareWiredTransitionEquiv,
    fkIsingSquareWiredTransitionMate, fkIsingSquareWiredCompletedIncidenceEquiv,
    fkIsingSquareWiredFullLeftDart, fkIsingSquareWiredFullLeftBond,
    hns, hnt]

theorem fkIsingSquareWiredFullLeftDart_pow_mem
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    ∀ m : Nat,
      ((fkIsingSquareWiredBlackBoundaryPerm n hn
          (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset)) ^ m)
          (fkIsingSquareWiredFullLeftDart n hn k) =
          fkIsingSquareWiredFullLeftDart n hn k ∨
      ((fkIsingSquareWiredBlackBoundaryPerm n hn
          (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset)) ^ m)
          (fkIsingSquareWiredFullLeftDart n hn k) =
          fkIsingSquareWiredFullLeftBond n hn k := by
  intro m
  induction m with
  | zero => exact Or.inl rfl
  | succ m ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      rcases ih with ih | ih
      · rw [ih, fkIsingSquareWiredFullLeftDart_step]
        exact Or.inr rfl
      · rw [ih, fkIsingSquareWiredFullLeftBond_step]
        exact Or.inl rfl

end
end StatMech.Universality
