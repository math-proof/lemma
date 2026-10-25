/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveAggregateLowRow.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateHighRow.Part6
import Structure.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateLowRow
open Finset
open scoped symmDiff


namespace StatMech.Ising

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

theorem nonempty_lpReplicaLowRowMarkedOutputData
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hlow : LPReplicaOffdiagDecoratedSource.IsLowRowRankFive
      G sites i j q z) :
    Nonempty (LPReplicaLowRowMarkedOutputData G sites q z) := by
  classical
  rcases lpReplicaOffdiagDecoratedSource_rank_five_exists_seamCopy_of_active_card_eq_three
      G sites hsite hij q hcard z hlow.1 with
    ⟨c, hcK, hc⟩ | ⟨c, hcK, hc⟩
  · obtain ⟨_s, _hp, _hL, _hP, _hmove, y, hyBal, hyRest⟩ :=
      lpReplicaOffdiagDecoratedSource_rank_five_balancedSelector_of_iSeam
        G sites hsite hij q hcard z hlow.1 c hcK hc
    have hyState := hyRest.1
    exact ⟨{
      output := Sum.inl y
      copy := c
      copy_active := hcK
      balanced := hyBal
      branch := Or.inl ⟨y, rfl, hc⟩
      state_eq := hyState }⟩
  · obtain ⟨_s, _hp, _hL, _hP, _hmove, y, hyBal, hyRest⟩ :=
      lpReplicaOffdiagDecoratedSource_rank_five_balancedSelector_of_jSeam
        G sites hsite hij q hcard z hlow.1 c hcK hc
    have hyState := hyRest.1
    exact ⟨{
      output := Sum.inr y
      copy := c
      copy_active := hcK
      balanced := hyBal
      branch := Or.inr ⟨y, rfl, hc⟩
      state_eq := hyState }⟩


end
end StatMech.Ising
