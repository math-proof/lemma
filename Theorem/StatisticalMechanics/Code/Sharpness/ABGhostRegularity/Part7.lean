/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABGhostRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.ABFiniteAssembly.Part2
import Def.StatisticalMechanics.Code.Sharpness.ABGhostRegularity.Part6
open Filter Finset Set SimpleGraph Topology
open Asymptotics


namespace StatMech

namespace Sharpness

open ConfigSpace

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem abgr_sum_offWeight (J : Sym2 V -> Real) (beta : Real) :
    ∑ eta, abgrOffWeight G J beta eta = 1 := by
  simpa [abgrOffWeight, configWeightV, edgeWeightV] using
    (abgr_sum_configWeightV
      (fun e : {e // e ∉ FieldGhostDict.ghostEdges V} =>
        pBeta (abfaLiftCoupling G J e) beta))

theorem abgr_offWeight_nonneg (J : Sym2 V -> Real) (beta : Real)
    (hJ : ∀ e ∈ G.edgeFinset, 0 ≤ J e) (hbeta : 0 ≤ beta)
    (eta : {e // e ∉ FieldGhostDict.ghostEdges V} -> Bool) :
    0 ≤ abgrOffWeight G J beta eta := by
  unfold abgrOffWeight
  apply Finset.prod_nonneg
  intro e _
  have hcoupling := abfaLiftCoupling_nonneg G J hJ e
  by_cases hopen : eta e
  · simp only [hopen, if_true]
    exact pBeta_nonneg (mul_nonneg hbeta hcoupling)
  · simp only [hopen]
    exact sub_nonneg.mpr (pBeta_lt_one (abfaLiftCoupling G J e) beta).le


theorem abgr_cluster_profile_eq_exp (h : Real) (k : Nat) :
    1 - (1 - qField h) ^ k = 1 - Real.exp (-(h * k)) := by
  simp only [qField, sub_sub_cancel]
  rw [← Real.exp_nat_mul]
  congr 2
  push_cast
  ring


theorem abgr_hasDerivAt_abfaMag_field (J : Sym2 V -> Real) (o : V)
    (beta h : Real) :
    HasDerivAt (fun t => abfaMag G J o beta t)
      (∑ eta : {e // e ∉ FieldGhostDict.ghostEdges V} -> Bool,
        abgrOffWeight G J beta eta *
          ((abgrActiveGhost G o eta).card *
            Real.exp (-(h * (abgrActiveGhost G o eta).card)))) h := by
  have hfun : (fun t => abfaMag G J o beta t) =
      fun t => ∑ eta : {e // e ∉ FieldGhostDict.ghostEdges V} -> Bool,
        abgrOffWeight G J beta eta *
          (1 - Real.exp (-(t * (abgrActiveGhost G o eta).card))) := by
    funext t
    rw [abgr_abfaMag_eq_cluster_mixture]
    apply Finset.sum_congr rfl
    intro eta _
    rw [abgr_cluster_profile_eq_exp]
    rfl
  rw [hfun]
  apply HasDerivAt.fun_sum
  intro eta _
  let k : Real := (abgrActiveGhost G o eta).card
  have hexp : HasDerivAt (fun t => Real.exp (-(t * k))) (-k * Real.exp (-(h * k))) h := by
    convert (Real.hasDerivAt_exp (-(h * k))).comp h
      (((hasDerivAt_id h).mul_const k).neg) using 1 <;> ring
  have hprofile : HasDerivAt (fun t => 1 - Real.exp (-(t * k)))
      (k * Real.exp (-(h * k))) h := by
    convert (hasDerivAt_const h (1 : Real)).sub hexp using 1 <;> ring
  convert hprofile.const_mul (abgrOffWeight G J beta eta) using 1 <;> rfl


theorem abgr_hasDerivAt_deriv_abfaMag_field (J : Sym2 V -> Real) (o : V)
    (beta h : Real) :
    HasDerivAt (fun t => deriv (fun u => abfaMag G J o beta u) t)
      (-(∑ eta : {e // e ∉ FieldGhostDict.ghostEdges V} -> Bool,
        abgrOffWeight G J beta eta *
          (((abgrActiveGhost G o eta).card : Real) ^ 2 *
            Real.exp (-(h * (abgrActiveGhost G o eta).card))))) h := by
  have hderiv : (fun t => deriv (fun u => abfaMag G J o beta u) t) =
      fun t => ∑ eta : {e // e ∉ FieldGhostDict.ghostEdges V} -> Bool,
        abgrOffWeight G J beta eta *
          ((abgrActiveGhost G o eta).card *
            Real.exp (-(t * (abgrActiveGhost G o eta).card))) := by
    funext t
    exact (abgr_hasDerivAt_abfaMag_field G J o beta t).deriv
  rw [hderiv]
  rw [← Finset.sum_neg_distrib]
  apply HasDerivAt.fun_sum
  intro eta _
  let k : Real := (abgrActiveGhost G o eta).card
  have hexp : HasDerivAt (fun t => Real.exp (-(t * k))) (-k * Real.exp (-(h * k))) h := by
    convert (Real.hasDerivAt_exp (-(h * k))).comp h
      (((hasDerivAt_id h).mul_const k).neg) using 1 <;> ring
  convert (hexp.const_mul k).const_mul (abgrOffWeight G J beta eta) using 1 <;> ring


theorem abgr_nat_mul_exp_le_inv (h : Real) (hh : 0 < h) (k : Nat) :
    (k : Real) * Real.exp (-(h * k)) ≤ 1 / h := by
  have hbase := Real.mul_exp_neg_le_exp_neg_one (h * (k : Real))
  have hexp : Real.exp (-(1 : Real)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by norm_num)
  rw [le_div_iff₀ hh]
  calc
    (k : Real) * Real.exp (-(h * k)) * h =
        (h * (k : Real)) * Real.exp (-(h * k)) := by ring
    _ ≤ Real.exp (-(1 : Real)) := hbase
    _ ≤ 1 := hexp


theorem abgr_nat_sq_mul_exp_le (h : Real) (hh : 0 < h) (k : Nat) :
    (k : Real) ^ 2 * Real.exp (-(h * k)) ≤ 2 / h ^ 2 := by
  let y : Real := h * (k : Real)
  have hy : 0 ≤ y := mul_nonneg hh.le (Nat.cast_nonneg k)
  have hquad : y ^ 2 / 2 ≤ Real.exp y := by
    have h := Real.quadratic_le_exp_of_nonneg hy
    nlinarith
  have hm := mul_le_mul_of_nonneg_right hquad (Real.exp_pos (-y)).le
  have hdecay : y ^ 2 * Real.exp (-y) ≤ 2 := by
    have hexpcancel : Real.exp y * Real.exp (-y) = 1 := by
      rw [← Real.exp_add]
      simp
    rw [hexpcancel] at hm
    nlinarith
  rw [div_eq_mul_inv, le_mul_inv_iff₀ (sq_pos_of_pos hh)]
  calc
    (k : Real) ^ 2 * Real.exp (-(h * k)) * h ^ 2 =
        y ^ 2 * Real.exp (-y) := by simp [y]; ring
    _ ≤ 2 := hdecay


theorem abgr_deriv_abfaMag_field_le (J : Sym2 V -> Real)
    (hJ : ∀ e ∈ G.edgeFinset, 0 ≤ J e) (o : V)
    (beta h : Real) (hbeta : 0 ≤ beta) (hh : 0 < h) :
    deriv (fun t => abfaMag G J o beta t) h ≤ 1 / h := by
  rw [(abgr_hasDerivAt_abfaMag_field G J o beta h).deriv]
  calc
    (∑ eta : {e // e ∉ FieldGhostDict.ghostEdges V} -> Bool,
        abgrOffWeight G J beta eta *
          ((abgrActiveGhost G o eta).card *
            Real.exp (-(h * (abgrActiveGhost G o eta).card)))) ≤
      ∑ eta : {e // e ∉ FieldGhostDict.ghostEdges V} -> Bool,
        abgrOffWeight G J beta eta * (1 / h) := by
          apply Finset.sum_le_sum
          intro eta _
          exact mul_le_mul_of_nonneg_left
            (abgr_nat_mul_exp_le_inv h hh (abgrActiveGhost G o eta).card)
            (abgr_offWeight_nonneg G J beta hJ hbeta eta)
    _ = 1 / h := by
      rw [← Finset.sum_mul, abgr_sum_offWeight]
      ring


theorem abgr_abs_deriv_deriv_abfaMag_field_le (J : Sym2 V -> Real)
    (hJ : ∀ e ∈ G.edgeFinset, 0 ≤ J e) (o : V)
    (beta h : Real) (hbeta : 0 ≤ beta) (hh : 0 < h) :
    |deriv (fun t => deriv (fun u => abfaMag G J o beta u) t) h| ≤ 2 / h ^ 2 := by
  rw [(abgr_hasDerivAt_deriv_abfaMag_field G J o beta h).deriv]
  rw [abs_neg]
  have hsum_nonneg : 0 ≤
      ∑ eta : {e // e ∉ FieldGhostDict.ghostEdges V} -> Bool,
        abgrOffWeight G J beta eta *
          (((abgrActiveGhost G o eta).card : Real) ^ 2 *
            Real.exp (-(h * (abgrActiveGhost G o eta).card))) := by
    apply Finset.sum_nonneg
    intro eta _
    exact mul_nonneg (abgr_offWeight_nonneg G J beta hJ hbeta eta)
      (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
  rw [abs_of_nonneg hsum_nonneg]
  calc
    (∑ eta : {e // e ∉ FieldGhostDict.ghostEdges V} -> Bool,
        abgrOffWeight G J beta eta *
          (((abgrActiveGhost G o eta).card : Real) ^ 2 *
            Real.exp (-(h * (abgrActiveGhost G o eta).card)))) ≤
      ∑ eta : {e // e ∉ FieldGhostDict.ghostEdges V} -> Bool,
        abgrOffWeight G J beta eta * (2 / h ^ 2) := by
          apply Finset.sum_le_sum
          intro eta _
          exact mul_le_mul_of_nonneg_left
            (abgr_nat_sq_mul_exp_le h hh (abgrActiveGhost G o eta).card)
            (abgr_offWeight_nonneg G J beta hJ hbeta eta)
    _ = 2 / h ^ 2 := by
      rw [← Finset.sum_mul, abgr_sum_offWeight]
      ring


theorem abgr_taylor_remainder_le (f : Real -> Real) (x y K : Real)
    (hK : 0 <= K)
    (hfdiff : forall (z : Real), z ∈ Set.uIcc x y -> DifferentiableAt Real f z)
    (hf'diff : forall (z : Real), z ∈ Set.uIcc x y ->
      DifferentiableAt Real (fun t => deriv f t) z)
    (hf'bound : forall (z : Real), z ∈ Set.uIcc x y ->
      |deriv (fun t => deriv f t) z| <= K) :
    |f y - f x - deriv f x * (y - x)| <= K * |y - x| ^ 2 := by
  have hderivLip : forall (z : Real), z ∈ Set.uIcc x y ->
      |deriv f z - deriv f x| <= K * |z - x| := by
    intro z hz
    have hsub : Set.uIcc x z ⊆ Set.uIcc x y :=
      uIcc_subset_uIcc left_mem_uIcc hz
    have hmvt := (convex_uIcc x z).norm_image_sub_le_of_norm_deriv_le
      (f := fun t => deriv f t) (C := K)
      (fun u hu => hf'diff u (hsub hu))
      (fun u hu => by
        rw [Real.norm_eq_abs]
        exact hf'bound u (hsub hu))
      left_mem_uIcc right_mem_uIcc
    simpa [Real.norm_eq_abs] using hmvt
  let g : Real -> Real := fun z => f z - deriv f x * z
  have hgdiff : forall (z : Real), z ∈ Set.uIcc x y -> DifferentiableAt Real g z := by
    intro z hz
    exact (hfdiff z hz).sub ((differentiableAt_const (c := deriv f x)).mul
      differentiableAt_id)
  have hgderiv : forall (z : Real), z ∈ Set.uIcc x y ->
      deriv g z = deriv f z - deriv f x := by
    intro z hz
    have hconst : HasDerivAt (fun t : Real => deriv f x * t) (deriv f x) z := by
      simpa using (hasDerivAt_id z).const_mul (deriv f x)
    exact ((hfdiff z hz).hasDerivAt.sub hconst).deriv
  have hgbound : forall (z : Real), z ∈ Set.uIcc x y ->
      ‖deriv g z‖ <= K * |y - x| := by
    intro z hz
    rw [hgderiv z hz, Real.norm_eq_abs]
    exact (hderivLip z hz).trans
      (mul_le_mul_of_nonneg_left (abs_sub_left_of_mem_uIcc hz) hK)
  have hmvt := (convex_uIcc x y).norm_image_sub_le_of_norm_deriv_le
    (f := g) (C := K * |y - x|) hgdiff hgbound
    left_mem_uIcc right_mem_uIcc
  change |(f y - deriv f x * y) - (f x - deriv f x * x)| <=
    (K * |y - x|) * |y - x| at hmvt
  convert hmvt using 1 <;> ring


theorem abgr_hasDerivAt_limit_of_taylor
    (f : Nat -> Real -> Real) (g : Real -> Real) (d : Nat -> Real)
    (x r K : Real) (hr : 0 < r) (hK : 0 <= K)
    (hlim : forall y, |y - x| < r -> Tendsto (fun n => f n y) atTop (nhds (g y)))
    (htaylor : forall n y, |y - x| < r ->
      |f n y - f n x - d n * (y - x)| <= K * |y - x| ^ 2) :
    exists L, HasDerivAt g L x := by
  have hdCauchy : CauchySeq d := by
    rw [Metric.cauchySeq_iff]
    intro epsilon hepsilon
    let delta : Real := min (r / 2) (epsilon / (6 * (K + 1)))
    have hK1 : 0 < K + 1 := by linarith
    have hdelta : 0 < delta := by
      dsimp [delta]
      positivity
    have hdeltar : delta < r := by
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    let y : Real := x + delta
    have hy : |y - x| < r := by
      simp [y, abs_of_pos hdelta, hdeltar]
    let slope : Nat -> Real := fun n => (f n y - f n x) / delta
    have hslope : Tendsto slope atTop (nhds ((g y - g x) / delta)) := by
      apply Tendsto.div_const
      exact (hlim y hy).sub (hlim x (by simpa using hr))
    have hslopeCauchy : CauchySeq slope := hslope.cauchySeq
    obtain ⟨N, hN⟩ := (Metric.cauchySeq_iff.mp hslopeCauchy)
      (epsilon / 3) (by linarith)
    refine ⟨N, ?_⟩
    intro m hm n hn
    have hslopeDist : |slope m - slope n| < epsilon / 3 := by
      simpa [Real.dist_eq] using hN m hm n hn
    have hclose : forall j, |d j - slope j| <= K * delta := by
      intro j
      have hrem := htaylor j y hy
      have habsdelta : |delta| = delta := abs_of_pos hdelta
      dsimp [slope]
      rw [show d j - (f j y - f j x) / delta =
          -(f j y - f j x - d j * (y - x)) / delta by
            simp [y]; field_simp]
      rw [abs_div, abs_neg, habsdelta]
      apply (div_le_iff₀ hdelta).mpr
      simpa [y, habsdelta, pow_two, mul_assoc] using hrem
    have hKdelta : K * delta <= epsilon / 6 := by
      have hdeltaBound : delta <= epsilon / (6 * (K + 1)) := min_le_right _ _
      have hmul : (K + 1) * delta <= epsilon / 6 := by
        apply (le_div_iff₀ (by positivity : 0 < (6 : Real))).mpr
        have := (mul_le_mul_of_nonneg_left hdeltaBound
          (show 0 <= 6 * (K + 1) by positivity))
        field_simp at this ⊢
        nlinarith
      exact (mul_le_mul_of_nonneg_right (by linarith : K <= K + 1)
        hdelta.le).trans hmul
    rw [Real.dist_eq]
    calc
      |d m - d n| <= |d m - slope m| + |slope m - slope n| +
          |slope n - d n| := by
        calc
          |d m - d n| <= |d m - slope m| + |slope m - d n| := abs_sub_le _ _ _
          _ <= |d m - slope m| +
              (|slope m - slope n| + |slope n - d n|) := by
                gcongr
                exact abs_sub_le _ _ _
          _ = _ := by ring
      _ < epsilon := by
        have hnclose : |slope n - d n| <= K * delta := by
          rw [abs_sub_comm]
          exact hclose n
        linarith [hclose m, hslopeDist, hKdelta]
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hdCauchy
  refine ⟨L, HasDerivAt.of_isLittleO ?_⟩
  have hrem : forall y, |y - x| < r ->
      |g y - g x - (y - x) * L| <= K * |y - x| ^ 2 := by
    intro y hy
    have htend : Tendsto
        (fun n => |f n y - f n x - d n * (y - x)|) atTop
        (nhds |g y - g x - L * (y - x)|) :=
      (((hlim y hy).sub (hlim x (by simpa using hr))).sub
        (hL.mul_const (y - x))).abs
    have hbound := le_of_tendsto htend
      (Filter.Eventually.of_forall (fun n => htaylor n y hy))
    simpa [mul_comm] using hbound
  have hbig : (fun y => g y - g x - (y - x) * L) =O[nhds x]
      (fun y => ‖y - x‖ ^ 2) := by
    apply IsBigO.of_bound K
    filter_upwards [Metric.ball_mem_nhds x hr] with y hy
    rw [Metric.mem_ball, Real.dist_eq] at hy
    simpa [Real.norm_eq_abs, abs_nonneg] using hrem y hy
  exact hbig.trans_isLittleO (isLittleO_pow_sub_sub x one_lt_two)

end Sharpness
end StatMech
