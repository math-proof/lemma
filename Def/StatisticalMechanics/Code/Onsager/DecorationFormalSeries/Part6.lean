module
public import Theorem.StatisticalMechanics.Code.Onsager.DecorationTransitionWeights.Part2
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalSeries.Part5


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalSeries.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Onsager

open BigOperators Finset

def ons_decoratedFormalKacWardIdentity
    (L : ℕ) [Fact (2 < L)] : Prop :=
  ∀ a b : Fin 2,
    ons_decFormalRoot L ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b) =
      (ons_decoratedSpinPolynomial L a b :
        MvPowerSeries (ons_DecEdge L) ℂ)

end StatMech.Onsager
