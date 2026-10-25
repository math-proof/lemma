/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardQuadraticAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardArbitraryValenceReduction
import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardTwist.Part7
import Def.StatisticalMechanics.Code.FrontierA.SurfaceKacWardQuadraticAssembly.Part3
open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager Polynomial

universe u


theorem surfaceBaseFormalEvenPolynomial_eq_coe
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (edgeClass : Sym2 V -> SurfaceHomology g) :
    surfaceBaseFormalEvenPolynomial G edgeClass =
      (surfaceBaseEvenMvPolynomial G edgeClass :
        MvPowerSeries (Sym2 V) Complex) := by
  classical
  unfold surfaceBaseFormalEvenPolynomial surfaceBaseEvenMvPolynomial
  ext m
  rw [map_sum, MvPolynomial.coeff_coe, MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro F hF
  rw [MvPowerSeries.coeff_monomial, MvPolynomial.coeff_monomial]
  simp [eq_comm]

theorem surfaceBaseFormalEvenPolynomial_coeff_finsetExponent
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (edgeClass : Sym2 V -> SurfaceHomology g)
    (S : Finset (Sym2 V)) :
    MvPowerSeries.coeff (ons_finsetExponent S)
        (surfaceBaseFormalEvenPolynomial G edgeClass) =
      if S ∈ evenSubgraphs G then
        surfaceBaseCycleCoefficient edgeClass S else 0 := by
  classical
  unfold surfaceBaseFormalEvenPolynomial
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

theorem surfaceBaseFormalEvenPolynomial_coeff_eq_zero_of_not_squarefree
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (edgeClass : Sym2 V -> SurfaceHomology g)
    (m : Sym2 V →₀ Nat) (hm : ¬ ons_IsSquarefreeExponent m) :
    MvPowerSeries.coeff m
        (surfaceBaseFormalEvenPolynomial G edgeClass) = 0 := by
  classical
  unfold surfaceBaseFormalEvenPolynomial
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro S hS
  rw [MvPowerSeries.coeff_monomial, if_neg]
  intro heq
  apply hm
  intro edge
  rw [heq, ons_finsetExponent_apply]
  split <;> omega


theorem kwGraphFormalRoot_eq_surfaceBaseFormalEvenPolynomial
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart -> G.Dart -> Complex)
    (edgeClass : Sym2 V -> SurfaceHomology g)
    (hlog : KWGraphWeightedCycleLog G phase
      (surfaceBaseCycleCoefficient edgeClass))
    (hisotropic : SurfaceDisjointCycleIsotropic G edgeClass)
    (hdeg : ∀ vertex, G.degree vertex <= 3)
    (hnonsquare : ∀ m : Sym2 V →₀ Nat,
      ¬ ons_IsSquarefreeExponent m ->
        MvPowerSeries.coeff m (kwGraphFormalRoot G phase) = 0) :
    kwGraphFormalRoot G phase =
      surfaceBaseFormalEvenPolynomial G edgeClass := by
  ext m
  by_cases hm : ons_IsSquarefreeExponent m
  · rw [ons_eq_finsetExponent_support_of_squarefree m hm]
    by_cases heven : m.support ∈ evenSubgraphs G
    · rw [kwGraphFormalRoot_coeff_surfaceQuadratic
        G phase edgeClass hlog hisotropic hdeg m.support heven,
        surfaceBaseFormalEvenPolynomial_coeff_finsetExponent,
        if_pos heven]
      rfl
    · rw [kwGraphFormalRoot_coeff_squarefree_eq_zero_of_not_even_weighted
        G phase _ hlog m.support heven,
        surfaceBaseFormalEvenPolynomial_coeff_finsetExponent,
        if_neg heven]
  · rw [hnonsquare m hm,
      surfaceBaseFormalEvenPolynomial_coeff_eq_zero_of_not_squarefree
        G edgeClass m hm]

theorem surfaceBaseEvenMvPolynomial_eval
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (edgeClass : Sym2 V -> SurfaceHomology g)
    (weight : Sym2 V -> Complex) :
    MvPolynomial.eval weight (surfaceBaseEvenMvPolynomial G edgeClass) =
      surfaceQuadraticEvenPolynomial G edgeClass
        (0 : SurfaceSpinStructure g) weight := by
  classical
  unfold surfaceBaseEvenMvPolynomial surfaceQuadraticEvenPolynomial
    surfaceBaseCycleCoefficient evenSubgraphs
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro F hF
  rw [MvPolynomial.eval_monomial, ons_finsetExponent_prod,
    surfaceQuadraticParity_zero]

theorem surfaceBaseFormalEvenPolynomial_eval
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (edgeClass : Sym2 V -> SurfaceHomology g)
    (weight : Sym2 V -> Complex) :
    ons_mvSeriesEval (surfaceBaseFormalEvenPolynomial G edgeClass) weight =
      surfaceQuadraticEvenPolynomial G edgeClass
        (0 : SurfaceSpinStructure g) weight := by
  rw [surfaceBaseFormalEvenPolynomial_eq_coe, ons_mvSeriesEval_coe,
    surfaceBaseEvenMvPolynomial_eval]


end StatMech.FrontierA
