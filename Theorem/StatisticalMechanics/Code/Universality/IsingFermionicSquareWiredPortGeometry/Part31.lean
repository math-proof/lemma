/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredOneVisitInsertedPhase
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredTangentCode
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveClosure
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearPolygonBridge.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part32


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open scoped Affine

noncomputable section

@[simp] theorem fkIsingSquareWiredBoundaryNorthIndex_boundaryDart
    (n : Nat) (hn : 0 < n) (k : Fin (2 * n)) :
    fkIsingSquareWiredBoundaryNorthIndex n hn
      (fkIsingSquareWiredBoundaryDart n hn (.north k)) = some k := by
  have hex : ∃ l : Fin (2 * n),
      fkIsingSquareWiredBoundaryDart n hn (.north k) =
        fkIsingSquareWiredBoundaryDart n hn (.north l) := ⟨k, rfl⟩
  simp only [fkIsingSquareWiredBoundaryNorthIndex, dif_pos hex]
  congr 1
  have hchoose := Classical.choose_spec hex
  exact Fin.ext (congrArg (fun d => match d with
    | FKIsingSquareWiredBoundaryDartIndex.north l => l.val
    | _ => 0) (fkIsingSquareWiredBoundaryDart_injective n hn hchoose)).symm

theorem fkIsingSquareWiredBoundaryNorthIndex_eq_some
    (n : Nat) (hn : 0 < n)
    (d : FKIsingMedialDart (fkSquareBoxPlanar n)) (k : Fin (2 * n))
    (h : fkIsingSquareWiredBoundaryNorthIndex n hn d = some k) :
    d = fkIsingSquareWiredBoundaryDart n hn (.north k) := by
  unfold fkIsingSquareWiredBoundaryNorthIndex at h
  split at h
  · have hchoose := Classical.choose_spec ‹∃ l, _›
    have hk : Classical.choose ‹∃ l, _› = k := Option.some.inj h
    simpa [hk] using hchoose
  · simp at h


end
end StatMech.Universality
