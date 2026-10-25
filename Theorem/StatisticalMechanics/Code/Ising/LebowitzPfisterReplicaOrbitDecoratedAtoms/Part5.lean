/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitDecoratedAtoms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitAtoms.Part3
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitDecoratedAtoms.Part4
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaOffdiagOrbitAtomCardInequality_of_decoratedInjection
    (G : SimpleGraph V) (sites : I -> V)
    (i j : I)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hinj : LPReplicaOffdiagDecoratedOrbitInjection G sites i j q) :
    LPReplicaOffdiagOrbitAtomCardInequality G sites i j q := by
  classical
  let Si := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i
  let Sj := lpMatchingSeamSource
    (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j
  let T := lpMatchingGhostSource
    (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
    lpReplicaCurrentGhost1
  obtain ⟨move, hmove⟩ := hinj
  dsimp only [LPReplicaOffdiagOrbitAtomCardInequality,
    LPReplicaOffdiagDecoratedOrbitInjection] at ⊢
  rw [<- card_lpReplicaDecoratedOrbitAtom,
    <- card_lpReplicaDecoratedOrbitAtom,
    <- card_lpReplicaDecoratedOrbitAtom,
    <- Fintype.card_sum]
  exact Fintype.card_le_of_injective move hmove


theorem lpReplicaAggregateProfileOrbitInequality_of_decoratedInjections
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (hinj : ∀ q i j, i ≠ j ->
      LPReplicaOffdiagDecoratedOrbitInjection G sites i j q) :
    LPReplicaAggregateProfileOrbitInequality G sites beta J hf r := by
  apply lpReplicaAggregateProfileOrbitInequality_of_atomCard
    G sites beta J hf r hbeta hJ hhf hr
  intro q i j hij
  exact lpReplicaOffdiagOrbitAtomCardInequality_of_decoratedInjection
    G sites i j q (hinj q i j hij)

end
end StatMech.Ising
