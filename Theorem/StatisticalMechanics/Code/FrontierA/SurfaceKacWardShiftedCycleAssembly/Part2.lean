/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardShiftedCycleAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardQuadraticAssembly.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardFlatSpinor
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAngularSplitUnitCycleReduction
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainHomology
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardLocalAngularSplitCycleReversal
import Def.StatisticalMechanics.Code.FrontierA.SurfaceKacWardShiftedCycleAssembly.Part2
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager Polynomial

universe u

theorem surfaceSpinFormalEvenPolynomial_eq_coe
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (edgeClass : Sym2 V -> SurfaceHomology g)
    (lambda : SurfaceSpinStructure g) :
    surfaceSpinFormalEvenPolynomial G edgeClass lambda =
      (surfaceSpinEvenMvPolynomial G edgeClass lambda :
        MvPowerSeries (Sym2 V) Complex) := by
  classical
  unfold surfaceSpinFormalEvenPolynomial surfaceSpinEvenMvPolynomial
  ext m
  rw [map_sum, MvPolynomial.coeff_coe, MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro F hF
  rw [MvPowerSeries.coeff_monomial, MvPolynomial.coeff_monomial]
  simp [eq_comm]

theorem surfaceSpinFormalEvenPolynomial_coeff_finsetExponent
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (edgeClass : Sym2 V -> SurfaceHomology g)
    (lambda : SurfaceSpinStructure g)
    (S : Finset (Sym2 V)) :
    MvPowerSeries.coeff (ons_finsetExponent S)
        (surfaceSpinFormalEvenPolynomial G edgeClass lambda) =
      if S ∈ evenSubgraphs G then
        surfaceSpinCycleCoefficient edgeClass lambda S else 0 := by
  classical
  unfold surfaceSpinFormalEvenPolynomial
  rw [map_sum]
  by_cases hS : S ∈ evenSubgraphs G
  · rw [Finset.sum_eq_single S]
    · simp [hS]
    · intro T hT hTS
      rw [MvPowerSeries.coeff_monomial, if_neg]
      intro heq
      exact hTS (ons_finsetExponent_injective heq.symm)
    · exact fun hnot => (hnot hS).elim
  · rw [if_neg hS]
    apply Finset.sum_eq_zero
    intro T hT
    rw [MvPowerSeries.coeff_monomial, if_neg]
    intro heq
    apply hS
    rw [ons_finsetExponent_injective heq]
    exact hT

theorem surfaceSpinFormalEvenPolynomial_coeff_eq_zero_of_not_squarefree
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (edgeClass : Sym2 V -> SurfaceHomology g)
    (lambda : SurfaceSpinStructure g)
    (m : Sym2 V →₀ Nat) (hm : ¬ ons_IsSquarefreeExponent m) :
    MvPowerSeries.coeff m
        (surfaceSpinFormalEvenPolynomial G edgeClass lambda) = 0 := by
  classical
  unfold surfaceSpinFormalEvenPolynomial
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro S hS
  rw [MvPowerSeries.coeff_monomial, if_neg]
  intro heq
  apply hm
  intro edge
  rw [heq, ons_finsetExponent_apply]
  split <;> omega

theorem kwGraphFormalRoot_eq_surfaceSpinFormalEvenPolynomial
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart -> G.Dart -> Complex)
    (edgeClass : Sym2 V -> SurfaceHomology g)
    (lambda : SurfaceSpinStructure g)
    (hlog : KWGraphWeightedCycleLog G phase
      (surfaceSpinCycleCoefficient edgeClass lambda))
    (hisotropic : SurfaceDisjointCycleIsotropic G edgeClass)
    (hdeg : ∀ vertex, G.degree vertex <= 3)
    (hnonsquare : ∀ m : Sym2 V →₀ Nat,
      ¬ ons_IsSquarefreeExponent m ->
        MvPowerSeries.coeff m (kwGraphFormalRoot G phase) = 0) :
    kwGraphFormalRoot G phase =
      surfaceSpinFormalEvenPolynomial G edgeClass lambda := by
  ext m
  by_cases hm : ons_IsSquarefreeExponent m
  · rw [ons_eq_finsetExponent_support_of_squarefree m hm]
    by_cases heven : m.support ∈ evenSubgraphs G
    · rw [kwGraphFormalRoot_coeff_surfaceQuadratic_shifted
        G phase edgeClass lambda hlog hisotropic hdeg m.support heven,
        surfaceSpinFormalEvenPolynomial_coeff_finsetExponent,
        if_pos heven]
      rfl
    · rw [kwGraphFormalRoot_coeff_squarefree_eq_zero_of_not_even_weighted
        G phase _ hlog m.support heven,
        surfaceSpinFormalEvenPolynomial_coeff_finsetExponent,
        if_neg heven]
  · rw [hnonsquare m hm,
      surfaceSpinFormalEvenPolynomial_coeff_eq_zero_of_not_squarefree
        G edgeClass lambda m hm]

theorem surfaceSpinEvenMvPolynomial_eval
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (edgeClass : Sym2 V -> SurfaceHomology g)
    (lambda : SurfaceSpinStructure g)
    (weight : Sym2 V -> Complex) :
    MvPolynomial.eval weight
        (surfaceSpinEvenMvPolynomial G edgeClass lambda) =
      surfaceQuadraticEvenPolynomial G edgeClass lambda weight := by
  classical
  unfold surfaceSpinEvenMvPolynomial surfaceQuadraticEvenPolynomial
    surfaceSpinCycleCoefficient evenSubgraphs
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro F hF
  rw [MvPolynomial.eval_monomial, ons_finsetExponent_prod]

theorem surfaceSpinFormalEvenPolynomial_eval
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (edgeClass : Sym2 V -> SurfaceHomology g)
    (lambda : SurfaceSpinStructure g)
    (weight : Sym2 V -> Complex) :
    ons_mvSeriesEval (surfaceSpinFormalEvenPolynomial G edgeClass lambda)
        weight =
      surfaceQuadraticEvenPolynomial G edgeClass lambda weight := by
  rw [surfaceSpinFormalEvenPolynomial_eq_coe, ons_mvSeriesEval_coe,
    surfaceSpinEvenMvPolynomial_eval]

end StatMech.FrontierA
