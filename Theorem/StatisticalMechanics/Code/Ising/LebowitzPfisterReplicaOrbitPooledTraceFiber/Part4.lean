/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitPooledTraceFiber.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPooledGateSplit
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitBalancedSourceTrace.Part3
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitPooledTraceFiber.Part6
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem lpReplicaAggregateDecoratedCard_of_injection
    (G : SimpleGraph V) (sites : I -> V)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hinj : LPReplicaAggregateDecoratedInjection G sites q) :
    Fintype.card (LPReplicaAggregateDecoratedSource G sites q) <=
      Fintype.card (LPReplicaAggregateDecoratedTarget G sites q) := by
  obtain ⟨move, hmove⟩ := hinj
  exact Fintype.card_le_of_injective move hmove


theorem lpReplicaAggregateProfileOrbitInequality_of_aggregateDecoratedInjections
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (hinj : ∀ q, LPReplicaAggregateDecoratedInjection G sites q) :
    LPReplicaAggregateProfileOrbitInequality G sites beta J hf r := by
  classical
  intro q
  have hcard := lpReplicaAggregateDecoratedCard_of_injection
    G sites q (hinj q)
  rw [card_lpReplicaAggregateDecoratedSource,
    card_lpReplicaAggregateDecoratedTarget] at hcard
  have hcardReal :
      (∑ i : I, ∑ j : I, if i = j then 0 else
          (Fintype.card
            (LPReplicaOffdiagDecoratedSource G sites i j q) : Real)) <=
        ∑ i : I, ∑ j : I, 2 *
          (Fintype.card
            (LPReplicaDecoratedOrbitAtom G sites
              (lpMatchingSeamSource
                (lpReplicaCurrentLeft sites)
                (lpReplicaCurrentRight sites) i)
              (lpMatchingSeamSource
                  (lpReplicaCurrentLeft sites)
                  (lpReplicaCurrentRight sites) j ∆
                lpMatchingGhostSource
                  (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V)
                  lpReplicaCurrentGhost1) q) : Real) := by
    exact_mod_cast hcard
  have hbase := lpReplicaProfileOrbitBaseWeight_nonneg
    G sites beta J hf r hbeta hJ hhf hr q
  have hweighted := mul_le_mul_of_nonneg_right hcardReal hbase
  simp_rw [lpReplicaProfileOrbitMass_eq_card_atoms_mul_base,
    <- card_lpReplicaDecoratedOrbitAtom]
  simpa only [Finset.sum_mul, Finset.mul_sum, mul_assoc,
    ite_mul, zero_mul] using hweighted

end
end StatMech.Ising
