/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardQuadraticAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardArbitraryValenceReduction
import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardTwist.Part7
import Def.StatisticalMechanics.Code.FrontierA.SurfaceKacWardQuadraticAssembly.Part4
open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager Polynomial

universe u


theorem surfaceBaseScalePolynomial_eval
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (edgeClass : Sym2 V -> SurfaceHomology g)
    (weight : Sym2 V -> Complex) (t : Complex) :
    (surfaceBaseScalePolynomial G edgeClass weight).eval t =
      surfaceQuadraticEvenPolynomial G edgeClass
        (0 : SurfaceSpinStructure g) (fun edge => t * weight edge) := by
  classical
  unfold surfaceBaseScalePolynomial surfaceQuadraticEvenPolynomial
    surfaceBaseCycleCoefficient evenSubgraphs
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro F hF
  rw [Finset.prod_mul_distrib, surfaceQuadraticParity_zero]
  simp
  ring


theorem surface_kacWard_base_det_square_of_cycle_phase
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableEq G.Dart]
    (phase : G.Dart -> G.Dart -> Complex)
    (edgeClass : Sym2 V -> SurfaceHomology g)
    (hlog : KWGraphWeightedCycleLog G phase
      (surfaceBaseCycleCoefficient edgeClass))
    (hisotropic : SurfaceDisjointCycleIsotropic G edgeClass)
    (hdeg : ∀ vertex, G.degree vertex <= 3)
    (hnonsquare : ∀ m : Sym2 V →₀ Nat,
      ¬ ons_IsSquarefreeExponent m ->
        MvPowerSeries.coeff m (kwGraphFormalRoot G phase) = 0)
    (weight : Sym2 V -> Complex) :
    (1 - kwGraphTransition G weight phase).det =
      surfaceQuadraticEvenPolynomial G edgeClass
        (0 : SurfaceSpinStructure g) weight ^ 2 := by
  let originalDartDecEq : DecidableEq G.Dart := inferInstance
  let standardDartDecEq : DecidableEq G.Dart :=
    fun a b => SimpleGraph.instDecidableEqDart a b
  letI : DecidableEq G.Dart := standardDartDecEq
  let M := kwGraphTransition G weight phase
  let P := kwDetScalePolynomial M
  let Q := (surfaceBaseScalePolynomial G edgeClass weight) ^ 2
  let card : Real := Fintype.card G.Dart
  let q : Real := (2 * (1 + card))⁻¹
  let B : Real := ∑ dart : G.Dart, ∑ next : G.Dart, norm (M dart next)
  let delta : Real := q / (1 + B)
  have hcard0 : 0 <= card := by positivity
  have hq : 0 < q := by
    dsimp only [q]
    positivity
  have hB : 0 <= B := by
    dsimp only [B]
    positivity
  have hdelta : 0 < delta := by
    dsimp only [delta]
    positivity
  have hcardq : card * q < 1 := by
    dsimp only [q]
    rw [mul_inv_lt_iff₀ (by positivity : 0 < 2 * (1 + card))]
    nlinarith
  have hraw (dart next : G.Dart) : norm (M dart next) <= B := by
    dsimp only [B]
    exact (Finset.single_le_sum
      (fun d _ => Finset.sum_nonneg fun e _ => norm_nonneg (M d e))
      (Finset.mem_univ dart)).trans' <|
        Finset.single_le_sum
          (fun e _ => norm_nonneg (M dart e)) (Finset.mem_univ next)
  have hformal := kwGraphFormalRoot_eq_surfaceBaseFormalEvenPolynomial
    G phase edgeClass hlog hisotropic hdeg hnonsquare
  have heval (r : Real) (hr : r ∈ Set.Ioo (0 : Real) delta) :
      P.eval (r : Complex) = Q.eval (r : Complex) := by
    have hrnorm : norm (r : Complex) = r := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr.1]
    let scaled : Sym2 V -> Complex := fun edge => (r : Complex) * weight edge
    have hentry : ∀ dart next,
        norm (kwGraphTransition G scaled phase dart next) <= q := by
      intro dart next
      rw [show scaled = fun edge => (r : Complex) * weight edge from rfl,
        kwGraphTransition_smulWeight, norm_mul, hrnorm]
      have hlt : r * B < q := by
        have hden : 0 < 1 + B := by positivity
        have h := hr.2
        dsimp only [delta] at h
        rw [lt_div_iff₀ hden] at h
        nlinarith
      exact (mul_le_mul_of_nonneg_left
        (hraw dart next) hr.1.le).trans hlt.le
    have hspec : ∀ alpha ∈
        (kwGraphTransition G scaled phase).charpoly.roots,
        norm alpha < 1 :=
      ons_spectral_lt_one_of_entry
        (kwGraphTransition G scaled phase) q hq.le hentry hcardq
    have hroot :
        ons_detWalkRoot (kwGraphTransition G scaled phase) =
          surfaceQuadraticEvenPolynomial G edgeClass
            (0 : SurfaceSpinStructure g) scaled := by
      rw [← kw_mvSeriesEval_GraphFormalRoot
          G phase scaled q hq.le hentry hcardq,
        hformal, surfaceBaseFormalEvenPolynomial_eval]
    have hsmall :
        (1 - kwGraphTransition G scaled phase).det =
          surfaceQuadraticEvenPolynomial G edgeClass
            (0 : SurfaceSpinStructure g) scaled ^ 2 := by
      calc
        (1 - kwGraphTransition G scaled phase).det =
            ons_detWalkRoot (kwGraphTransition G scaled phase) ^ 2 :=
          (ons_detWalkRoot_sq
            (kwGraphTransition G scaled phase) hspec).symm
        _ = _ := by rw [hroot]
    dsimp only [P, Q]
    rw [kwDetScalePolynomial_eval, Polynomial.eval_pow,
      surfaceBaseScalePolynomial_eval]
    have hmatrix : (r : Complex) • M =
        kwGraphTransition G scaled phase := by
      ext dart next
      change (r : Complex) * M dart next = _
      dsimp only [M, scaled]
      rw [kwGraphTransition_smulWeight]
    rw [hmatrix]
    exact hsmall
  have hinfinite : Set.Infinite {z : Complex | P.eval z = Q.eval z} := by
    have hI : Set.Infinite (Set.Ioo (0 : Real) delta) :=
      Set.Ioo_infinite hdelta
    have himage : Set.Infinite
        ((fun r : Real => (r : Complex)) '' Set.Ioo (0 : Real) delta) :=
      hI.image Complex.ofReal_injective.injOn
    apply himage.mono
    rintro z ⟨r, hr, rfl⟩
    exact heval r hr
  have hpoly : P = Q := Polynomial.eq_of_infinite_eval_eq P Q hinfinite
  have hone := congrArg (Polynomial.eval (1 : Complex)) hpoly
  dsimp only [P, Q] at hone
  have hone' : kwDetOneSubWith standardDartDecEq M =
      surfaceQuadraticEvenPolynomial G edgeClass
        (0 : SurfaceSpinStructure g) weight ^ 2 := by
    simpa [kwDetOneSubWith, kwDetScalePolynomial_eval,
      surfaceBaseScalePolynomial_eval, M] using hone
  change kwDetOneSubWith originalDartDecEq M =
    surfaceQuadraticEvenPolynomial G edgeClass
      (0 : SurfaceSpinStructure g) weight ^ 2
  exact (kwDetOneSubWith_eq originalDartDecEq standardDartDecEq M).trans hone'


theorem surface_twisted_kacWard_det_square_of_cycle_phase
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
        MvPowerSeries.coeff m (kwGraphFormalRoot G phase) = 0)
    (lambda : SurfaceSpinStructure g) (weight : Sym2 V -> Complex) :
    (1 - surfaceTwistedKacWardMatrix G phase edgeClass lambda weight).det =
      surfaceQuadraticEvenPolynomial G edgeClass lambda weight ^ 2 := by
  apply surface_twisted_kacWard_det_square_of_base G phase edgeClass
  intro w
  exact surface_kacWard_base_det_square_of_cycle_phase
    G phase edgeClass hlog hisotropic hdeg hnonsquare w


theorem surface_twisted_kacWard_det_eq_sectorSquare_of_cycle_phase
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
        MvPowerSeries.coeff m (kwGraphFormalRoot G phase) = 0)
    (lambda : SurfaceSpinStructure g) (weight : Sym2 V -> Real) :
    (1 - surfaceTwistedKacWardMatrix G phase edgeClass lambda
        (fun edge => (weight edge : Complex))).det =
      (surfaceTwistedSectorSquare
        (surfaceGraphSectorWeight G edgeClass weight) lambda : Complex) := by
  apply surface_twisted_kacWard_det_eq_sectorSquare_of_base G phase edgeClass
  intro w
  exact surface_kacWard_base_det_square_of_cycle_phase
    G phase edgeClass hlog hisotropic hdeg hnonsquare w

end StatMech.FrontierA
