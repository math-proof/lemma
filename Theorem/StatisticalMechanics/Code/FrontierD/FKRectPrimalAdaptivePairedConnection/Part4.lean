/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptivePairedConnection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalAdaptiveProjection.Part9
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalPairedConnection
import Def.StatisticalMechanics.Code.FrontierD.FKRectPrimalAdaptivePairedConnection.Part3
open MeasureTheory SimpleGraph StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

theorem fkRectPrimalPairedConnectionFactor_nonneg
    (R : FKRectTorus) (pair : Fin R.height -> Fin R.height)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (i : Fin R.height) :
    0 <= fkRectPrimalPairedConnectionFactor R pair hp hp1 hq i :=
  measureReal_nonneg

theorem fkRectPrimalPairedConnectionFactor_le_one
    (R : FKRectTorus) (pair : Fin R.height -> Fin R.height)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (i : Fin R.height) :
    fkRectPrimalPairedConnectionFactor R pair hp hp1 hq i <= 1 :=
  measureReal_le_one


theorem fkRectPrimalFullDistinctPairedWitness_mass_le_prod
    (R : FKRectTorus) (pair : Fin R.height -> Fin R.height)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (S : Finset (Fin R.height)) :
    StatMech.Probability.finiteEventMass
        (FK.fkProb (fkRectCutGraph R) p q)
        {rho | FKRectPrimalFullDistinctPairedWitness R pair S rho} <=
      ∏ i ∈ S, fkRectPrimalPairedConnectionFactor R pair hp hp1 hq i := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      calc
        StatMech.Probability.finiteEventMass
            (FK.fkProb (fkRectCutGraph R) p q)
            {rho | FKRectPrimalFullDistinctPairedWitness R pair ∅ rho} = 1 := by
          unfold StatMech.Probability.finiteEventMass
          have hevent : {rho : ConfigSpace (Sym2 R.Vertex) |
              FKRectPrimalFullDistinctPairedWitness R pair ∅ rho} =
              Set.univ := by
            ext rho
            simp [FKRectPrimalFullDistinctPairedWitness]
          rw [hevent]
          simpa using FK.fkProb_sum_eq_one (fkRectCutGraph R)
            hp hp1 (zero_lt_one.trans_le hq)
        _ <= ∏ i ∈ (∅ : Finset (Fin R.height)),
            fkRectPrimalPairedConnectionFactor R pair hp hp1 hq i := by simp
  | @insert i S hi ih =>
      calc
        StatMech.Probability.finiteEventMass
            (FK.fkProb (fkRectCutGraph R) p q)
            {rho | FKRectPrimalFullDistinctPairedWitness
              R pair (insert i S) rho} <=
          fkRectPrimalPairedConnectionFactor R pair hp hp1 hq i *
            StatMech.Probability.finiteEventMass
              (FK.fkProb (fkRectCutGraph R) p q)
              {rho | FKRectPrimalFullDistinctPairedWitness R pair S rho} := by
                simpa only [fkRectPrimalPairedConnectionFactor] using
                  fkRectPrimalFullDistinctPairedWitness_step
                    R pair S i hi hp hp1 hq
        _ <= fkRectPrimalPairedConnectionFactor R pair hp hp1 hq i *
            (∏ j ∈ S,
              fkRectPrimalPairedConnectionFactor R pair hp hp1 hq j) :=
          mul_le_mul_of_nonneg_left ih
            (fkRectPrimalPairedConnectionFactor_nonneg
              R pair hp hp1 hq i)
        _ = ∏ j ∈ insert i S,
            fkRectPrimalPairedConnectionFactor R pair hp hp1 hq j := by
          simp [hi]


theorem fkRectPrimalFullDistinctPairedWitness_mass_le_prod_erase
    (R : FKRectTorus) (pair : Fin R.height -> Fin R.height)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 <= q)
    (S : Finset (Fin R.height)) (first : Fin R.height) (hfirst : first ∈ S) :
    StatMech.Probability.finiteEventMass
        (FK.fkProb (fkRectCutGraph R) p q)
        {rho | FKRectPrimalFullDistinctPairedWitness R pair S rho} <=
      ∏ i ∈ S.erase first,
        fkRectPrimalPairedConnectionFactor R pair hp hp1 hq i := by
  let f := fkRectPrimalPairedConnectionFactor R pair hp hp1 hq
  have hfull := fkRectPrimalFullDistinctPairedWitness_mass_le_prod
    R pair hp hp1 hq S
  have hnonneg : 0 <= ∏ i ∈ S.erase first, f i :=
    Finset.prod_nonneg fun i _ =>
      fkRectPrimalPairedConnectionFactor_nonneg R pair hp hp1 hq i
  have hfactor : f first <= 1 :=
    fkRectPrimalPairedConnectionFactor_le_one R pair hp hp1 hq first
  calc
    StatMech.Probability.finiteEventMass
        (FK.fkProb (fkRectCutGraph R) p q)
        {rho | FKRectPrimalFullDistinctPairedWitness R pair S rho} <=
      ∏ i ∈ S, f i := hfull
    _ = f first * ∏ i ∈ S.erase first, f i := by
      exact (Finset.mul_prod_erase S f hfirst).symm
    _ <= 1 * ∏ i ∈ S.erase first, f i :=
      mul_le_mul_of_nonneg_right hfactor hnonneg
    _ = ∏ i ∈ S.erase first, f i := one_mul _


end
end StatMech.FrontierD
