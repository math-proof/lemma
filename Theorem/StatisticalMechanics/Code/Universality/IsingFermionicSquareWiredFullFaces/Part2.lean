/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredFullFaces.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredClosedFibers.Part2
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredRibbon.Part9
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredFullFaces.Part2


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open StatMech.FrontierA

noncomputable section

theorem fkIsingSquareWiredBlackFaceKey_boundaryStep_of_interior
    (n : Nat) (hn : 0 < n) (x : FKIsingSquareWiredBlackCarrier n)
    (p : Int × Int)
    (hx : fkIsingSquareWiredBlackFaceKey n x = some p)
    (hp : fkIsingSquareInteriorFaceKey n p) :
    fkIsingSquareWiredBlackFaceKey n
        (fkIsingSquareWiredBlackBoundaryPerm n hn
          (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset) x) =
      some p := by
  rcases x with ⟨x, hcolor⟩
  cases x with
  | source => simp [fkIsingSquareWiredBlackFaceKey] at hx
  | terminal => simp [fkIsingSquareWiredBlackFaceKey] at hx
  | dart d =>
      have hkey : fkIsingSquareWedgeFaceKey n d = p := by
        simpa [fkIsingSquareWiredBlackFaceKey] using hx
      simp only [fkIsingSquareWiredBlackBoundaryPerm,
        Equiv.Perm.subtypePerm_apply, fkIsingSquareWiredBoundaryStep,
        Equiv.trans_apply, fkIsingSquareWiredTransitionEquiv]
      change fkIsingSquareWiredBlackFaceKey n ⟨.bond
          (FKIsingMedialDart.localMate
            (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset) d), _⟩ = _
      simp only [fkIsingSquareWiredBlackFaceKey, Option.some.injEq]
      rw [fkIsingSquareWedgeFaceKey_open_localMate, hkey]
  | bond d =>
      have hkey : fkIsingSquareWedgeFaceKey n d = p := by
        simpa [fkIsingSquareWiredBlackFaceKey] using hx
      have hdint : fkIsingSquareInteriorFaceKey n
          (fkIsingSquareWedgeFaceKey n d) := by simpa only [hkey] using hp
      have hnotSource : d ≠ fkIsingSquareWiredSourceDart n hn := by
        intro h
        subst d
        exact (fkIsingSquareWiredBoundaryDart_faceKey_not_interior n hn .bottom)
          hdint
      have hnotTerminal : d ≠ fkIsingSquareWiredTerminalDart n hn := by
        intro h
        subst d
        exact (fkIsingSquareWiredBoundaryDart_faceKey_not_interior n hn .top)
          hdint
      have htrans : fkIsingSquareWiredTransitionEquiv n hn
          (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset) (.bond d) =
          .bond (fkIsingSquareWiredBondMate n hn d) := by
        change fkIsingSquareWiredTransitionMate n hn
          (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset) (.bond d) = _
        simp [fkIsingSquareWiredTransitionMate, hnotSource, hnotTerminal]
      simp only [fkIsingSquareWiredBlackBoundaryPerm,
        Equiv.Perm.subtypePerm_apply, fkIsingSquareWiredBoundaryStep,
        Equiv.trans_apply]
      simp only [htrans]
      change fkIsingSquareWiredBlackFaceKey n
        ⟨.dart (fkIsingSquareWiredBondMate n hn d), _⟩ = _
      simp only [fkIsingSquareWiredBlackFaceKey, Option.some.injEq]
      rw [fkIsingSquareWiredBondMate_eq_bondMate_of_interior n hn d hdint,
        fkIsingSquareWedgeFaceKey_bondMate n hn d hdint, hkey]

theorem fkIsingSquareWiredBlackFaceKey_pow_of_interior
    (n : Nat) (hn : 0 < n) (x : FKIsingSquareWiredBlackCarrier n)
    (p : Int × Int)
    (hx : fkIsingSquareWiredBlackFaceKey n x = some p)
    (hp : fkIsingSquareInteriorFaceKey n p) :
    ∀ k : Nat, fkIsingSquareWiredBlackFaceKey n
      (((fkIsingSquareWiredBlackBoundaryPerm n hn
        (FK.edgeSetConfig (fkSquareBoxPlanar n).G.edgeFinset)) ^ k) x) = some p := by
  intro k
  induction k with
  | zero => simpa using hx
  | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact fkIsingSquareWiredBlackFaceKey_boundaryStep_of_interior
        n hn _ p ih hp

end
end StatMech.Universality
