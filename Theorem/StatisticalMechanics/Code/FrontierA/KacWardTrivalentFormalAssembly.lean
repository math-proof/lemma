/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardTrivalentFormalAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardFormalMultiaffine
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardTrivalentCoefficients
import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalCoefficient.Part3
import Def.StatisticalMechanics.Code.FrontierA.KacWardTrivalentFormalAssembly
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager

universe u


theorem kwGraphFormalEvenPolynomial_eq_coe
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    kwGraphFormalEvenPolynomial G =
      (kwGraphEvenMvPolynomial G : MvPowerSeries (Sym2 V) ℂ) := by
  classical
  unfold kwGraphFormalEvenPolynomial kwGraphEvenMvPolynomial
  ext m
  rw [map_sum, MvPolynomial.coeff_coe, MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro F hF
  rw [MvPowerSeries.coeff_monomial, MvPolynomial.coeff_monomial]
  simp [eq_comm]

theorem kwGraphFormalEvenPolynomial_eval
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : Sym2 V → ℂ) :
    ons_mvSeriesEval (kwGraphFormalEvenPolynomial G) weight =
      kwEvenPolynomial G weight := by
  classical
  rw [kwGraphFormalEvenPolynomial_eq_coe,
    ons_mvSeriesEval_coe]
  unfold kwGraphEvenMvPolynomial kwEvenPolynomial
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro F hF
  rw [MvPolynomial.eval_monomial, ons_finsetExponent_prod]
  simp


end StatMech.FrontierA
