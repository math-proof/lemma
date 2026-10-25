/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnAdaptiveMixedCharge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnDevelopedIncidence.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnAdaptiveMixedCharge


namespace StatMech.FrontierD

noncomputable section

noncomputable def FKRectZeroTurnAdaptiveMixedRouting.toCharge
    (R : FKRectTorus) (omega : R.Configuration)
    (routing : FKRectZeroTurnAdaptiveMixedRouting R omega)
    (hdual : ∀ C D : FKRectZeroTurnCutRemainderComponent R omega,
      ∀ X : FKRectRawWiredDualHorizontalCrossingComponent R omega,
        routing.crossing C = Sum.inr X →
        routing.crossing D = Sum.inr X →
        fkRectZeroTurnRemainderSide R omega C =
          fkRectZeroTurnRemainderSide R omega D → C = D) :
    FKRectZeroTurnMixedAnnulusCharge R omega :=
  FKRectZeroTurnMixedAnnulusCharge.ofCrossing
    R omega routing.crossing (by
      intro C D hcross hside
      cases hC : routing.crossing C with
      | inl X =>
          have hD : routing.crossing D = Sum.inl X := hcross.symm.trans hC
          have hXC := routing.primal_spec C X hC
          have hXD := routing.primal_spec D X hD
          exact
            fkRectZeroTurnRemainder_eq_of_shared_primalTouchedCrossing_of_endpointReachable
              R omega C D X hXC.1 hXD.1 hXC.2 hXD.2 hside
      | inr X =>
          have hD : routing.crossing D = Sum.inr X := hcross.symm.trans hC
          exact hdual C D X hC hD hside)


noncomputable def fkRectZeroTurnAdaptiveMixedRouting
    (R : FKRectTorus) (omega : R.Configuration) :
    FKRectZeroTurnAdaptiveMixedRouting R omega := by
  classical
  refine {
    crossing := fun C =>
      if h : ∃ X : FKRectRawPrimalHorizontalCrossingComponent R omega,
          FKRectZeroTurnReachablePrimalTouchedCrossing R omega C X then
        Sum.inl (Classical.choose h)
      else
        Sum.inr
          (fkRectZeroTurnDualTouchedCrossings_nonempty R omega C).choose
    primal_spec := ?_
    dual_spec := ?_ }
  · intro C X hX
    split at hX
    next h =>
      simp only [Sum.inl.injEq] at hX
      subst X
      exact Classical.choose_spec h
    next h => simp at hX
  · intro C X hX
    split at hX
    next h => simp at hX
    next h =>
      simp only [Sum.inr.injEq] at hX
      subst X
      exact (fkRectZeroTurnDualTouchedCrossings_nonempty R omega C).choose_spec


end
end StatMech.FrontierD
