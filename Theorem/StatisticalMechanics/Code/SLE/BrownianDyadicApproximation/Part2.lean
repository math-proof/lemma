/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianDyadicApproximation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.BrownianDyadicControl.Part3
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Def.StatisticalMechanics.Code.SLE.BrownianDyadicApproximation.Part2
open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal


namespace StatMech.SLE

theorem tendsto_brownianCoordinateProcess_brownianDyadicApproxPoint
    (omega : Real -> Real) (N : Nat) {t : Real}
    (htLower : -(N : Real) <= t) (htUpper : t <= N)
    (hgood : ∀ᶠ n in atTop,
      ∀ k ∈ Finset.range (2 * N * brownianDyadicDenominator n),
        edist (brownianCoordinateProcess (brownianDyadicPoint N n k) omega)
          (brownianCoordinateProcess (brownianDyadicPoint N n (k + 1)) omega) <
            brownianDyadicThreshold n) :
    Tendsto (fun n =>
      brownianCoordinateProcess (brownianDyadicApproxPoint N n t) omega)
      atTop (nhds (brownianDyadicLimit N t omega)) := by
  exact (cauchySeq_brownianCoordinateProcess_brownianDyadicApproxPoint
    omega N htLower htUpper hgood).tendsto_limUnder


theorem edist_brownianCoordinateProcess_approxPoint_limit_le
    (omega : Real -> Real) (N n : Nat) {t : Real}
    (htLower : -(N : Real) <= t) (htUpper : t <= N)
    (hgoodFrom : ∀ m, n <= m ->
      ∀ k ∈ Finset.range (2 * N * brownianDyadicDenominator m),
        edist (brownianCoordinateProcess (brownianDyadicPoint N m k) omega)
          (brownianCoordinateProcess (brownianDyadicPoint N m (k + 1)) omega) <
            brownianDyadicThreshold m) :
    edist
        (brownianCoordinateProcess (brownianDyadicApproxPoint N n t) omega)
        (brownianDyadicLimit N t omega) <=
      (256 : ENNReal) * brownianDyadicThreshold n := by
  have hgood : ∀ᶠ m in atTop,
      ∀ k ∈ Finset.range (2 * N * brownianDyadicDenominator m),
        edist (brownianCoordinateProcess (brownianDyadicPoint N m k) omega)
          (brownianCoordinateProcess (brownianDyadicPoint N m (k + 1)) omega) <
            brownianDyadicThreshold m := by
    filter_upwards [eventually_ge_atTop n] with m hm
    exact hgoodFrom m hm
  let f : Nat -> Real := fun m =>
    brownianCoordinateProcess (brownianDyadicApproxPoint N m t) omega
  let g : Nat -> Real := fun m => f (m + n)
  let d : Nat -> ENNReal := fun m =>
    (256 : ENNReal) * brownianDyadicThreshold (m + n + 1)
  have hg : Tendsto g atTop (nhds (brownianDyadicLimit N t omega)) := by
    simpa only [g, f, Function.comp_def, Nat.add_comm] using
      (tendsto_brownianCoordinateProcess_brownianDyadicApproxPoint
        omega N htLower htUpper hgood).comp (tendsto_add_atTop_nat n)
  have hstep (m : Nat) : edist (g m) (g m.succ) <= d m := by
    dsimp only [g, f, d]
    rw [show m.succ + n = (m + n) + 1 by omega]
    exact edist_brownianCoordinateProcess_approxPoint_succ_le
      omega N (m + n) htLower htUpper (hgoodFrom _ (by omega))
  have htsum : (∑' m : Nat, d m) =
      (256 : ENNReal) * brownianDyadicThreshold n := by
    dsimp only [d, brownianDyadicThreshold]
    have hfun : (fun m : Nat =>
        (256 : ENNReal) * (2 : ENNReal)⁻¹ ^ (m + n + 1)) =
        fun m => ((256 : ENNReal) * (2 : ENNReal)⁻¹ ^ (n + 1)) *
          (2 : ENNReal)⁻¹ ^ m := by
      funext m
      rw [show m + n + 1 = m + (n + 1) by omega, pow_add]
      ac_rfl
    rw [hfun, ENNReal.tsum_mul_left, ENNReal.tsum_geometric_two, pow_succ]
    calc
      (256 : ENNReal) * ((2 : ENNReal)⁻¹ ^ n * (2 : ENNReal)⁻¹) * 2 =
          ((256 : ENNReal) * (2 : ENNReal)⁻¹ ^ n) *
            ((2 : ENNReal)⁻¹ * 2) := by ac_rfl
      _ = (256 : ENNReal) * (2 : ENNReal)⁻¹ ^ n := by
        rw [ENNReal.inv_mul_cancel (by norm_num) ENNReal.ofNat_ne_top, mul_one]
  have hbound := edist_le_tsum_of_edist_le_of_tendsto₀ d hstep hg
  change edist (f n) (brownianDyadicLimit N t omega) <= _
  simpa [g, htsum] using hbound


theorem edist_brownianDyadicLimit_le
    (omega : Real -> Real) (N n : Nat) {s t : Real}
    (hsLower : -(N : Real) <= s) (hsUpper : s <= N)
    (htLower : -(N : Real) <= t) (htUpper : t <= N)
    (hclose : dist s t <
      ((brownianDyadicDenominator n : Nat) : Real)⁻¹)
    (hgoodFrom : ∀ m, n <= m ->
      ∀ k ∈ Finset.range (2 * N * brownianDyadicDenominator m),
        edist (brownianCoordinateProcess (brownianDyadicPoint N m k) omega)
          (brownianCoordinateProcess (brownianDyadicPoint N m (k + 1)) omega) <
            brownianDyadicThreshold m) :
    edist (brownianDyadicLimit N s omega) (brownianDyadicLimit N t omega) <=
      (513 : ENNReal) * brownianDyadicThreshold n := by
  let Bs := brownianCoordinateProcess (brownianDyadicApproxPoint N n s) omega
  let Bt := brownianCoordinateProcess (brownianDyadicApproxPoint N n t) omega
  have hsTail : edist Bs (brownianDyadicLimit N s omega) <=
      (256 : ENNReal) * brownianDyadicThreshold n :=
    edist_brownianCoordinateProcess_approxPoint_limit_le
      omega N n hsLower hsUpper hgoodFrom
  have htTail : edist Bt (brownianDyadicLimit N t omega) <=
      (256 : ENNReal) * brownianDyadicThreshold n :=
    edist_brownianCoordinateProcess_approxPoint_limit_le
      omega N n htLower htUpper hgoodFrom
  have hmiddle : edist Bs Bt <= brownianDyadicThreshold n :=
    edist_brownianCoordinateProcess_approxPoint_le omega N n
      hsLower hsUpper htLower htUpper hclose (hgoodFrom n le_rfl)
  calc
    edist (brownianDyadicLimit N s omega) (brownianDyadicLimit N t omega) <=
        edist (brownianDyadicLimit N s omega) Bs +
          edist Bs (brownianDyadicLimit N t omega) := edist_triangle _ _ _
    _ <= edist (brownianDyadicLimit N s omega) Bs +
        (edist Bs Bt + edist Bt (brownianDyadicLimit N t omega)) :=
      add_le_add_right (edist_triangle Bs Bt _) _
    _ <= ((256 : ENNReal) * brownianDyadicThreshold n) +
        (brownianDyadicThreshold n +
          ((256 : ENNReal) * brownianDyadicThreshold n)) := by
      apply add_le_add
      · simpa [edist_comm] using hsTail
      · exact add_le_add hmiddle htTail
    _ = (513 : ENNReal) * brownianDyadicThreshold n := by
      let x := brownianDyadicThreshold n
      change (256 : ENNReal) * x + (x + 256 * x) = 513 * x
      calc
        (256 : ENNReal) * x + (x + 256 * x) =
            256 * x + (1 * x + 256 * x) := by simp only [one_mul]
        _ = (256 + (1 + 256)) * x := by simp only [add_mul]
        _ = 513 * x := by norm_num


theorem continuousOn_brownianDyadicLimit
    (omega : Real -> Real) (N : Nat)
    (hgood : ∀ᶠ n in atTop,
      ∀ k ∈ Finset.range (2 * N * brownianDyadicDenominator n),
        edist (brownianCoordinateProcess (brownianDyadicPoint N n k) omega)
          (brownianCoordinateProcess (brownianDyadicPoint N n (k + 1)) omega) <
            brownianDyadicThreshold n) :
    ContinuousOn (fun t => brownianDyadicLimit N t omega)
      (Set.Icc (-(N : Real)) N) := by
  rw [Filter.eventually_atTop] at hgood
  obtain ⟨n0, hn0⟩ := hgood
  intro t ht
  rw [Metric.continuousWithinAt_iff]
  intro eps heps
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one
    (K := Real) (x := eps / 513) (y := (1 / 2 : Real))
      (by positivity) (by norm_num)
  let n := k + n0
  have hn0n : n0 <= n := by dsimp only [n]; omega
  have hpowN : (1 / 2 : Real) ^ n0 <= 1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  have hpowK : 0 <= (1 / 2 : Real) ^ k := by positivity
  have hpow : 513 * (1 / 2 : Real) ^ n < eps := by
    have hk' : 513 * (1 / 2 : Real) ^ k < eps := by nlinarith
    have hprod : (1 / 2 : Real) ^ k * (1 / 2 : Real) ^ n0 <=
        (1 / 2 : Real) ^ k :=
      mul_le_of_le_one_right hpowK hpowN
    dsimp only [n]
    rw [pow_add]
    nlinarith
  let delta : Real := ((brownianDyadicDenominator n : Nat) : Real)⁻¹
  have hdelta : 0 < delta := by
    dsimp only [delta]
    apply inv_pos.mpr
    exact_mod_cast brownianDyadicDenominator_pos n
  refine ⟨delta, hdelta, ?_⟩
  intro s hs hst
  have hed := edist_brownianDyadicLimit_le omega N n
    hs.1 hs.2 ht.1 ht.2 hst
    (fun m hm => hn0 m (hn0n.trans hm))
  rw [dist_edist]
  have hfinite : (513 : ENNReal) * brownianDyadicThreshold n ≠ ⊤ := by
    apply ENNReal.mul_ne_top ENNReal.ofNat_ne_top
    unfold brownianDyadicThreshold
    exact ENNReal.pow_ne_top
      (ENNReal.inv_ne_top.mpr (by norm_num))
  calc
    (edist (brownianDyadicLimit N s omega)
      (brownianDyadicLimit N t omega)).toReal <=
        ((513 : ENNReal) * brownianDyadicThreshold n).toReal :=
      (ENNReal.toReal_le_toReal (edist_ne_top _ _) hfinite).2 hed
    _ = 513 * (1 / 2 : Real) ^ n := by
      simp [brownianDyadicThreshold, ENNReal.toReal_mul,
        ENNReal.toReal_pow, ENNReal.toReal_inv]
    _ < eps := hpow

end StatMech.SLE
