/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveAggregateLowRow.Part6
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictInvariant
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveStrictRouteFractionalHall.Part4
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveHandledStrictInvariant.Part7


namespace StatMech.Ising

noncomputable section

open scoped symmDiff

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

set_option maxHeartbeats 1200000 in


theorem lpReplicaLowRowMarkedOutputData_not_hasStrictPhysicalDoubleIncidence
    (G : SimpleGraph V) (sites : I -> V)
    (hsite : Function.Injective sites) {i j : I} (hij : i ≠ j)
    (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5)
    (z : LPReplicaOffdiagDecoratedSource G sites i j q)
    (hlow : LPReplicaOffdiagDecoratedSource.IsLowRowRankFive
      G sites i j q z)
    (d : LPReplicaLowRowMarkedOutputData G sites q z) :
    ¬ LPReplicaOffdiagDecoratedTarget.HasStrictPhysicalDoubleIncidence
      G sites i j q d.output := by
  classical
  rcases d.branch with ⟨y, hy, hc⟩ | ⟨y, hy, hc⟩
  · obtain ⟨s, hp, _hL, _hP, hmove, y', _hyBal, hyState, hyPres⟩ :=
      lpReplicaOffdiagDecoratedSource_rank_five_balancedSelector_of_iSeam
        G sites hsite hij q hcard z hlow.1 d.copy d.copy_active hc
    have hout : d.output = Sum.inl y' := by
      rw [hy]
      apply lpReplicaOffdiagDecoratedTargetBranchedSlotState_injective
        G sites i j q
      apply Prod.ext
      · rfl
      · have hdState := d.state_eq
        rw [hy] at hdState
        exact hdState.trans hyState.symm
    rw [hout, LPReplicaOffdiagDecoratedTarget.HasStrictPhysicalDoubleIncidence,
      hyPres]
    rw [
      lpReplicaDecoratedOrbitAtomOfBalancedSelector_left_hasStrictPhysicalDoubleIncidence]
    rcases s with ⟨sp, sorbit, stag, sgate, slabel, sselector,
      sfalse, strue, srow0, srow1⟩
    dsimp at hp hmove ⊢
    subst sp
    rw [eq_of_heq hmove]
    exact lpReplicaOffdiagDecoratedSource_rankFive_low_singletonToggle_not_strictRaw
      G sites hsite hij q hcard z hlow d.copy d.copy_active
  · obtain ⟨s, hp, _hL, _hP, hmove, y', _hyBal, hyState,
      s', hyPres, hp', hselector', htag'⟩ :=
      lpReplicaOffdiagDecoratedSource_rank_five_balancedSelector_of_jSeam
        G sites hsite hij q hcard z hlow.1 d.copy d.copy_active hc
    have hout : d.output = Sum.inr y' := by
      rw [hy]
      apply lpReplicaOffdiagDecoratedTargetBranchedSlotState_injective
        G sites i j q
      apply Prod.ext
      · rfl
      · have hdState := d.state_eq
        rw [hy] at hdState
        exact hdState.trans hyState.symm
    rw [hout, LPReplicaOffdiagDecoratedTarget.HasStrictPhysicalDoubleIncidence,
      hyPres]
    rw [
      lpReplicaDecoratedOrbitAtomOfBalancedSelector_left_hasStrictPhysicalDoubleIncidence]
    rcases s with ⟨sp, sorbit, stag, sgate, slabel, sselector,
      sfalse, strue, srow0, srow1⟩
    rcases s' with ⟨sp', sorbit', stag', sgate', slabel', sselector',
      sfalse', strue', srow0', srow1'⟩
    dsimp at hp hp' hselector' htag' hmove ⊢
    subst sp
    subst sp'
    rw [eq_of_heq hselector', eq_of_heq htag', eq_of_heq hmove]
    exact lpReplicaOffdiagDecoratedSource_rankFive_low_singletonToggle_not_strictRaw
      G sites hsite hij q hcard z hlow d.copy d.copy_active

end
end StatMech.Ising
