/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitOrientedFourColor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitSplitTag.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part17
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitOrientedFourColor.Part4
open Finset


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem card_lpReplicaOrientedFourColorFiber
    (G : SimpleGraph V) (sites : I -> V)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (m : {p : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat //
      lpReplicaSymmetrizedProfile G sites p = q}) :
    Fintype.card (LPReplicaOrientedFourColorFiber G sites A B q m) =
      ∑ a : {p : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat //
          p <= m.1},
        lpReplicaCollisionSplitMultiplicity G sites m.1 a.1 *
          lpReplicaProfileOrbitMultiplicity G sites q m.1 *
          (lpReplicaDisconnProfileFamily G sites A a.1).card *
          (lpReplicaDisconnProfileFamily G sites B
            (lpReplicaReflectedResidual G sites m.1 a.1)).card := by
  classical
  unfold LPReplicaOrientedFourColorFiber
  change Fintype.card (Σ a :
      {p : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat // p <= m.1},
      (LPReplicaCollisionSplitLabel G sites m.1 a.1 ×
        LPReplicaProfileOrbitLabel G sites q m.1) ×
        (↑(lpReplicaDisconnProfileFamily G sites A a.1) ×
          ↑(lpReplicaDisconnProfileFamily G sites B
            (lpReplicaReflectedResidual G sites m.1 a.1)))) = _
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro a _
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_prod,
    card_lpReplicaCollisionSplitLabel, card_lpReplicaProfileOrbitLabel,
    Fintype.card_coe, Fintype.card_coe]
  ring


theorem card_lpReplicaOrientedFourColorAtom
    (G : SimpleGraph V) (sites : I -> V)
    (A B : Finset (LPReplicaCurrentVertex V))
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    Fintype.card (LPReplicaOrientedFourColorAtom G sites A B q) =
      Fintype.card (LPReplicaDecoratedOrbitAtom G sites A B q) := by
  exact Fintype.card_congr
    (lpReplicaDecoratedOrbitAtomEquivOrientedFourColor
      G sites A B q).symm


end
end StatMech.Ising
