module
public import Theorem.StatisticalMechanics.Code.Onsager.DecorationTransitionWeights.Part2
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalSeries.Part3


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

noncomputable def ons_decoratedSpinPolynomial
    (L : ℕ) [Fact (2 < L)] (a b : Fin 2) :
    MvPolynomial (ons_DecEdge L) ℂ :=
  ∑ D : ons_DecoratedEvenSubgraph L,
    MvPolynomial.monomial (ons_finsetExponent D.1)
      (ons_spinCharacter a b
        (ons_evenHomology L (ons_originalEdgesOfDecorated L D)) : ℂ)

end StatMech.Onsager
