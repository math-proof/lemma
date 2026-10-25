/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Data.Finset.Card
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Tactic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Sequences
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.Data.Finsupp.Basic
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.Algebra.Module.Basic
import Def.Combinatorics.Additive.Sarkozy.Part6


namespace MathlibExt.Combinatorics.Additive.SarkozyWanted

open scoped InnerProductSpace

/-- Quadratic correlations vanish on the orthocomplement (N9). -/
theorem sarkozy_quad_corr_tendsto {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (U : H →ₗᵢ[ℝ] H)
    (w : H) (hw : w ∈ (sarkozyWclos U)ᗮ) (Q h : ℕ) (hQ : 1 ≤ Q) (hh : 1 ≤ h) :
    Filter.Tendsto
      (fun (M : ℕ) => (M : ℝ)⁻¹ * ∑ n ∈ Finset.range M,
        inner ℝ ((U ^ (Q*Q*((n+h)*(n+h)))) w) ((U ^ (Q*Q*(n*n))) w))
      Filter.atTop (nhds 0) := by
  have ha1 : 1 ≤ 2*Q*Q*h :=
    calc (1:ℕ) = 1*1*1*1 := by ring
      _ ≤ 2*Q*Q*h :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (by omega) hQ) hQ) hh
  have hnormT : ‖((U ^ (2*Q*Q*h)).toContinuousLinearMap : H →L[ℝ] H)‖ ≤ 1 :=
    LinearIsometry.norm_toContinuousLinearMap_le _
  -- per-term reduction to a linear orbit correlation
  have hexp : ∀ n : ℕ, inner ℝ ((U^(Q*Q*((n+h)*(n+h)))) w) ((U^(Q*Q*(n*n))) w)
      = inner ℝ ((((U^(2*Q*Q*h))^n)) ((U^(Q*Q*(h*h))) w)) w := by
    intro n
    have he : Q*Q*((n+h)*(n+h))
        = Q*Q*(n*n) + ((2*Q*Q*h)*n + Q*Q*(h*h)) := by ring
    have hinner : ((U^((2*Q*Q*h)*n + Q*Q*(h*h))) w)
        = ((((U^(2*Q*Q*h))^n)) ((U^(Q*Q*(h*h))) w)) := by
      rw [pow_add, LinearIsometry.coe_mul, Function.comp_apply, pow_mul]
    have hU : ((U^(Q*Q*((n+h)*(n+h)))) w)
        = ((U^(Q*Q*(n*n))) (((U^((2*Q*Q*h)*n + Q*Q*(h*h))) w))) := by
      rw [he, pow_add, LinearIsometry.coe_mul, Function.comp_apply]
    rw [hU, hinner]
    exact LinearIsometry.inner_map_map _ _ _
  have hbir : ∀ M : ℕ, (M:ℝ)⁻¹ • (∑ n ∈ Finset.range M,
        ((((U^(2*Q*Q*h))^n)) ((U^(Q*Q*(h*h))) w)))
      = birkhoffAverage ℝ (⇑((U ^ (2*Q*Q*h)).toContinuousLinearMap)) id M
        ((U^(Q*Q*(h*h))) w) := by
    intro M
    simp only [birkhoffAverage, birkhoffSum]
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    simp only [LinearIsometry.coe_pow, LinearIsometry.coe_toContinuousLinearMap, id_eq]
  have hMeq : ∀ M : ℕ, (M:ℝ)⁻¹ * ∑ n ∈ Finset.range M,
        inner ℝ ((U ^ (Q*Q*((n+h)*(n+h)))) w) ((U ^ (Q*Q*(n*n))) w)
      = inner ℝ (birkhoffAverage ℝ
        (⇑((U ^ (2*Q*Q*h)).toContinuousLinearMap)) id M ((U^(Q*Q*(h*h))) w)) w := by
    intro M
    rw [← hbir M, real_inner_smul_left, sum_inner]
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    exact hexp n
  have hergodic := ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection
    ((U ^ (2*Q*Q*h)).toContinuousLinearMap) hnormT ((U^(Q*Q*(h*h))) w)
  have hclosed : IsClosed ((((U ^ (2*Q*Q*h)).toContinuousLinearMap).eqLocus 1 :
      Submodule ℝ H) : Set H) := by
    change IsClosed {x : H | ((U ^ (2*Q*Q*h)).toContinuousLinearMap) x
      = (1 : H →L[ℝ] H) x}
    exact isClosed_eq (((U ^ (2*Q*Q*h)).toContinuousLinearMap).continuous)
      (1 : H →L[ℝ] H).continuous
  let _hcomplete : CompleteSpace
      ↥((((U ^ (2*Q*Q*h)).toContinuousLinearMap).eqLocus 1 : Submodule ℝ H)) :=
    completeSpace_coe_iff_isComplete.mpr hclosed.isComplete
  let _hproj : (((U ^ (2*Q*Q*h)).toContinuousLinearMap).eqLocus 1).HasOrthogonalProjection :=
    inferInstance
  -- the ergodic limit lies in W
  have hmemT : ((((U ^ (2*Q*Q*h)).toContinuousLinearMap).eqLocus 1).orthogonalProjectionOnto
      ((U^(Q*Q*(h*h))) w) : H)
      ∈ ((U ^ (2*Q*Q*h)).toContinuousLinearMap).eqLocus 1 :=
    ((((U ^ (2*Q*Q*h)).toContinuousLinearMap).eqLocus 1).orthogonalProjectionOnto
      ((U^(Q*Q*(h*h))) w)).2
  have hmem : ((((U ^ (2*Q*Q*h)).toContinuousLinearMap).eqLocus 1).orthogonalProjectionOnto
      ((U^(Q*Q*(h*h))) w) : H) ∈ sarkozyFix U (2*Q*Q*h) := by
    have hTmem := hmemT
    rw [LinearMap.mem_eqLocus] at hTmem
    change (U^(2*Q*Q*h)).toLinearMap _ = LinearMap.id _
    exact hTmem
  have haW : ((((U ^ (2*Q*Q*h)).toContinuousLinearMap).eqLocus 1).orthogonalProjectionOnto
      ((U^(Q*Q*(h*h))) w) : H) ∈ sarkozyWclos U := by
    have h1 : sarkozyFix U (2*Q*Q*h) ≤ ⨆ j : ℕ, sarkozyFix U (j + 1) := by
      have heq : sarkozyFix U (2*Q*Q*h) = sarkozyFix U ((2*Q*Q*h - 1) + 1) := by
        congr 1
        omega
      rw [heq]
      exact le_iSup (fun j => sarkozyFix U (j + 1)) _
    exact Submodule.le_topologicalClosure _ (h1 hmem)
  have hzero : inner ℝ ((((U ^ (2*Q*Q*h)).toContinuousLinearMap).eqLocus 1).orthogonalProjectionOnto
      ((U^(Q*Q*(h*h))) w) : H) w = 0 :=
    Submodule.inner_right_of_mem_orthogonal haW hw
  have hlim : Filter.Tendsto (fun M => inner ℝ (birkhoffAverage ℝ
      (⇑((U ^ (2*Q*Q*h)).toContinuousLinearMap)) id M ((U^(Q*Q*(h*h))) w)) w)
      Filter.atTop
      (nhds (inner ℝ ((((U ^ (2*Q*Q*h)).toContinuousLinearMap).eqLocus 1).orthogonalProjectionOnto
        ((U^(Q*Q*(h*h))) w) : H) w)) :=
    Filter.Tendsto.inner hergodic tendsto_const_nhds
  rw [hzero] at hlim
  exact Filter.Tendsto.congr (fun M => (hMeq M).symm) hlim

/-- Quadratic averages vanish on the orthocomplement (N10). -/
theorem sarkozy_quad_avg_tendsto {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (U : H →ₗᵢ[ℝ] H)
    (w : H) (hw : w ∈ (sarkozyWclos U)ᗮ) (Q : ℕ) (hQ : 1 ≤ Q) :
    Filter.Tendsto
      (fun (M : ℕ) => (M : ℝ)⁻¹ • ∑ n ∈ Finset.range M, ((U ^ (Q*Q*(n*n))) w))
      Filter.atTop (nhds 0) := by
  have h := sarkozy_vdc_tendsto (x := fun n => ((U ^ (Q*Q*(n*n))) w)) (C := ‖w‖)
    (norm_nonneg _) (fun n => le_of_eq (((U ^ (Q*Q*(n*n))).norm_map) w))
    (fun d hd => sarkozy_quad_corr_tendsto U w hw Q d hQ hd)
  exact h

/-- Membership in a fixed-point submodule from the isometry equation (N11 helper). -/
theorem sarkozyFix_mem {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (U : H →ₗᵢ[ℝ] H) (m : ℕ) (x : H) (h : (U ^ m) x = x) : x ∈ sarkozyFix U m := by
  change x ∈ LinearMap.eqLocus ((U ^ m).toLinearMap) (LinearMap.id : H →ₗ[ℝ] H)
  rw [LinearMap.mem_eqLocus]
  change (((U ^ m) x = x))
  exact h

/-- Isometry equation from fixed-point submodule membership (N11 helper). -/
theorem sarkozyFix_eq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (U : H →ₗᵢ[ℝ] H) (m : ℕ) (x : H) (h : x ∈ sarkozyFix U m) : (U ^ m) x = x := by
  have h2 : ((U ^ m).toLinearMap) x = (LinearMap.id : H →ₗ[ℝ] H) x := by
    have := h
    change x ∈ LinearMap.eqLocus ((U ^ m).toLinearMap) (LinearMap.id : H →ₗ[ℝ] H) at this
    rwa [LinearMap.mem_eqLocus] at this
  change (((U ^ m) x = x))
  exact h2

/-- Iterating a fixed point stays fixed (N11 helper). -/
theorem sarkozyFix_pow_iter {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (U : H →ₗᵢ[ℝ] H) {m : ℕ} {x : H} (h : (U ^ m) x = x) (k : ℕ) :
    (((U ^ m) ^ k) x = x) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, LinearIsometry.coe_mul, Function.comp_apply, h]
    exact ih

/-- Fixed-point submodules grow along divisibility (N11 helper). -/
theorem sarkozyFix_mono_div {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (U : H →ₗᵢ[ℝ] H) {a c : ℕ} (h : a ∣ c) : sarkozyFix U a ≤ sarkozyFix U c := by
  intro x hx
  obtain ⟨k, rfl⟩ := h
  have hxa := sarkozyFix_eq U a x hx
  have hkk : (((U ^ a) ^ k) x = x) := sarkozyFix_pow_iter U hxa k
  have hck : (U ^ (a * k)) x = x := by
    rw [pow_mul]
    exact hkk
  exact sarkozyFix_mem U (a * k) x hck

/-- Hilbert-space Sárközy recurrence (N11): square-return correlations force orthogonality
to every fixed vector. -/
theorem sarkozy_hilbert_sarkozy {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (U : H →ₗᵢ[ℝ] H) (v : H)
    (hhyp : ∀ k : ℕ, 0 < k → inner ℝ ((U ^ (k*k)) v) v = 0) :
    ∀ u : H, U u = u → inner ℝ u v = 0 := by
  have hWclosed : IsClosed (((sarkozyWclos U) : Submodule ℝ H) : Set H) :=
    Submodule.isClosed_topologicalClosure (⨆ j : ℕ, sarkozyFix U (j + 1))
  let _hWcomplete : CompleteSpace ↥((sarkozyWclos U : Submodule ℝ H)) :=
    completeSpace_coe_iff_isComplete.mpr hWclosed.isComplete
  let _hWproj : (sarkozyWclos U).HasOrthogonalProjection := inferInstance
  set r : H := (sarkozyWclos U).starProjection v with hrdef
  set w : H := v - r with hwdef
  have hr_mem : r ∈ sarkozyWclos U := by
    rw [hrdef]
    exact (((sarkozyWclos U).orthogonalProjectionOnto v)).2
  have hw_mem : w ∈ (sarkozyWclos U)ᗮ := by
    rw [hwdef, hrdef]
    exact Submodule.sub_starProjection_mem_orthogonal v
  have hrv : inner ℝ r v = ‖r‖^2 := by
    have ev : v = r + w := by
      rw [hwdef]
      abel
    rw [ev, inner_add_right, real_inner_self_eq_norm_sq,
      Submodule.inner_right_of_mem_orthogonal hr_mem hw_mem, add_zero]
  have hdirected : Directed (· ≤ ·) (fun j => sarkozyFix U (j + 1)) := by
    intro i j
    have hi : 1 ≤ i + 1 := Nat.le_add_left 1 i
    have hj : 1 ≤ j + 1 := Nat.le_add_left 1 j
    have h1 : (1:ℕ) ≤ (i+1)*(j+1) := by
      calc (1:ℕ) = 1*1 := by ring
        _ ≤ (i+1)*(j+1) := Nat.mul_le_mul hi hj
    have e : ((i+1)*(j+1) - 1) + 1 = (i+1)*(j+1) := by omega
    refine ⟨(i+1)*(j+1) - 1, ?_, ?_⟩
    · change sarkozyFix U (i + 1) ≤ sarkozyFix U (((i + 1) * (j + 1) - 1) + 1)
      rw [e]
      exact sarkozyFix_mono_div U (dvd_mul_right _ _)
    · change sarkozyFix U (j + 1) ≤ sarkozyFix U (((i + 1) * (j + 1) - 1) + 1)
      rw [e]
      exact sarkozyFix_mono_div U ⟨i+1, by ring⟩
  -- the per-threshold estimate
  have hmain : ∀ ε : ℝ, 0 < ε → ‖r‖^2 ≤ 2*ε*‖v‖ := by
    intro ε hε
    have hrclo : r ∈ closure ((⨆ j : ℕ, sarkozyFix U (j + 1) : Submodule ℝ H) : Set H) :=
      hr_mem
    rw [Metric.mem_closure_iff] at hrclo
    obtain ⟨b, hbmem, hdist⟩ := hrclo ε hε
    have hbU : b ∈ ⨆ j : ℕ, sarkozyFix U (j + 1) := hbmem
    rw [(Submodule.mem_iSup_of_directed _ hdirected)] at hbU
    obtain ⟨j, hjb⟩ := hbU
    have hm1 : 1 ≤ j + 1 := Nat.le_add_left 1 j
    have hrb : ‖r - b‖ < ε := by
      rwa [dist_eq_norm] at hdist
    have hbm := sarkozyFix_eq U (j+1) b hjb
    have hbQ : ∀ n : ℕ, (U^((j+1)*(j+1)*(n*n))) b = b := by
      intro n
      have hpow : ∀ k : ℕ, (((U^(j+1))^k) b = b) :=
        fun k => sarkozyFix_pow_iter U hbm k
      have e : (j+1)*(j+1)*(n*n) = (j+1)*((j+1)*(n*n)) := by ring
      rw [e, pow_mul]
      exact hpow _
    have hsum0 : ∀ M : ℕ, 1 ≤ M →
        (∑ n ∈ Finset.range M, inner ℝ ((U^((j+1)*(j+1)*(n*n))) v) v) = ‖v‖^2 := by
      intro M hM
      have h0mem : 0 ∈ Finset.range M := Finset.mem_range.mpr (by omega)
      rw [← Finset.add_sum_erase _ _ h0mem]
      have e0 : inner ℝ ((U^((j+1)*(j+1)*(0*0))) v) v = ‖v‖^2 := by
        have e00 : (j+1)*(j+1)*(0*0) = 0 := by ring
        rw [e00, pow_zero]
        simp
      rw [e0]
      have erest : (∑ n ∈ (Finset.range M).erase 0,
          inner ℝ ((U^((j+1)*(j+1)*(n*n))) v) v) = 0 := by
        apply Finset.sum_eq_zero
        intro n hn
        have hn0 : n ≠ 0 := Finset.ne_of_mem_erase hn
        have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
        have hQn : 0 < (j+1)*n := Nat.mul_pos (by omega) hnpos
        have e : (j+1)*(j+1)*(n*n) = ((j+1)*n)*((j+1)*n) := by ring
        rw [e]
        exact hhyp _ hQn
      rw [erest, add_zero]
    have havg : ∀ M : ℕ, 1 ≤ M →
        (M:ℝ)⁻¹ * (∑ n ∈ Finset.range M, inner ℝ ((U^((j+1)*(j+1)*(n*n))) w) v)
        = ‖v‖^2/(M:ℝ) - (M:ℝ)⁻¹ * (∑ n ∈ Finset.range M,
          inner ℝ ((U^((j+1)*(j+1)*(n*n))) r) v) := by
      intro M hM
      have esub : ∀ n : ℕ, inner ℝ ((U^((j+1)*(j+1)*(n*n))) w) v
          = inner ℝ ((U^((j+1)*(j+1)*(n*n))) v) v
            - inner ℝ ((U^((j+1)*(j+1)*(n*n))) r) v := by
        intro n
        have hmap : ((U^((j+1)*(j+1)*(n*n))) w)
            = ((U^((j+1)*(j+1)*(n*n))) v) - ((U^((j+1)*(j+1)*(n*n))) r) := by
          rw [hwdef, map_sub]
        rw [hmap, inner_sub_left]
      have esum : (∑ n ∈ Finset.range M, inner ℝ ((U^((j+1)*(j+1)*(n*n))) w) v)
          = (∑ n ∈ Finset.range M, inner ℝ ((U^((j+1)*(j+1)*(n*n))) v) v)
            - (∑ n ∈ Finset.range M, inner ℝ ((U^((j+1)*(j+1)*(n*n))) r) v) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun n _ => esub n)
      rw [esum, hsum0 M hM, div_eq_inv_mul]
      ring
    have hterm_lb : ∀ n : ℕ, ‖r‖^2 - 2*ε*‖v‖
        ≤ inner ℝ ((U^((j+1)*(j+1)*(n*n))) r) v := by
      intro n
      have e : ((U^((j+1)*(j+1)*(n*n))) r)
          = ((U^((j+1)*(j+1)*(n*n))) b) + ((U^((j+1)*(j+1)*(n*n))) (r - b)) := by
        rw [← map_add]
        congr 1
        abel
      have hbQn := hbQ n
      rw [e, hbQn, inner_add_left]
      have h1 : inner ℝ b v ≥ ‖r‖^2 - ε*‖v‖ := by
        have ebr : b = r - (r - b) := by abel
        have hcs : |inner ℝ (r - b) v| ≤ ε*‖v‖ := by
          calc |inner ℝ (r - b) v| ≤ ‖r - b‖ * ‖v‖ := abs_real_inner_le_norm _ _
            _ ≤ ε * ‖v‖ := mul_le_mul_of_nonneg_right (le_of_lt hrb) (norm_nonneg _)
        have ebrw : inner ℝ b v = inner ℝ r v - inner ℝ (r - b) v := by
          conv_lhs => rw [ebr]
          rw [inner_sub_left]
        rw [hrv] at ebrw
        have hab := (abs_le.mp hcs).2
        linarith
      have h2 : inner ℝ (((U^((j+1)*(j+1)*(n*n))) (r - b))) v ≥ -(ε*‖v‖) := by
        have hcs : |inner ℝ (((U^((j+1)*(j+1)*(n*n))) (r - b))) v| ≤ ε*‖v‖ := by
          calc |inner ℝ (((U^((j+1)*(j+1)*(n*n))) (r - b))) v|
                ≤ ‖((U^((j+1)*(j+1)*(n*n))) (r - b))‖ * ‖v‖ :=
                abs_real_inner_le_norm _ _
            _ = ‖r - b‖ * ‖v‖ := by rw [LinearIsometry.norm_map]
            _ ≤ ε * ‖v‖ := mul_le_mul_of_nonneg_right (le_of_lt hrb) (norm_nonneg _)
        have hab := (abs_le.mp hcs).1
        linarith
      linarith
    have hLHS : Filter.Tendsto (fun (M : ℕ) => (M:ℝ)⁻¹ * ∑ n ∈ Finset.range M,
        inner ℝ ((U^((j+1)*(j+1)*(n*n))) w) v)
        Filter.atTop (nhds 0) := by
      have h10 := sarkozy_quad_avg_tendsto U w hw_mem (j+1) hm1
      have e : ∀ M : ℕ, inner ℝ ((M:ℝ)⁻¹ • ∑ n ∈ Finset.range M,
          ((U^((j+1)*(j+1)*(n*n))) w)) v
          = (M:ℝ)⁻¹ * ∑ n ∈ Finset.range M,
            inner ℝ ((U^((j+1)*(j+1)*(n*n))) w) v := by
        intro M
        rw [real_inner_smul_left, sum_inner]
      have hinner : Filter.Tendsto (fun (M : ℕ) => inner ℝ ((M:ℝ)⁻¹ • ∑ n ∈ Finset.range M,
          ((U^((j+1)*(j+1)*(n*n))) w)) v) Filter.atTop (nhds (inner ℝ (0:H) v)) :=
        Filter.Tendsto.inner h10 tendsto_const_nhds
      rw [show inner ℝ (0:H) v = 0 from inner_zero_left _] at hinner
      exact Filter.Tendsto.congr (fun M => e M) hinner
    have hBlim : Filter.Tendsto (fun (M : ℕ) => ‖v‖^2/(M:ℝ) - (‖r‖^2 - 2*ε*‖v‖))
        Filter.atTop (nhds (-(‖r‖^2 - 2*ε*‖v‖))) := by
      have h1 : Filter.Tendsto (fun (M : ℕ) => ‖v‖^2/(M:ℝ)) Filter.atTop (nhds 0) :=
        tendsto_const_div_atTop_nhds_zero_nat _
      have h2 : Filter.Tendsto (fun (M : ℕ) => ‖v‖^2/(M:ℝ) - (‖r‖^2 - 2*ε*‖v‖))
          Filter.atTop (nhds (0 - (‖r‖^2 - 2*ε*‖v‖))) :=
        h1.sub tendsto_const_nhds
      rwa [zero_sub] at h2
    have hAleB : ∀ᶠ (M : ℕ) in Filter.atTop, (M:ℝ)⁻¹ * ∑ n ∈ Finset.range M,
          inner ℝ ((U^((j+1)*(j+1)*(n*n))) w) v
          ≤ ‖v‖^2/(M:ℝ) - (‖r‖^2 - 2*ε*‖v‖) := by
      rw [Filter.eventually_atTop]
      refine ⟨1, fun M hM => ?_⟩
      have hMpos : (0:ℝ) < (M:ℝ) := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM)
      have hMne : (M:ℝ) ≠ 0 := ne_of_gt hMpos
      have hM1nn : (0:ℝ) ≤ (M:ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
      have hlb : (‖r‖^2 - 2*ε*‖v‖)
          ≤ (M:ℝ)⁻¹ * (∑ n ∈ Finset.range M,
            inner ℝ ((U^((j+1)*(j+1)*(n*n))) r) v) := by
        have h1 : (M:ℝ) * (‖r‖^2 - 2*ε*‖v‖)
            ≤ ∑ n ∈ Finset.range M, inner ℝ ((U^((j+1)*(j+1)*(n*n))) r) v := by
          calc (M:ℝ) * (‖r‖^2 - 2*ε*‖v‖)
              = ∑ _n ∈ Finset.range M, (‖r‖^2 - 2*ε*‖v‖) := by
                simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            _ ≤ _ := Finset.sum_le_sum (fun n _ => hterm_lb n)
        calc (‖r‖^2 - 2*ε*‖v‖) = (M:ℝ)⁻¹ * ((M:ℝ) * (‖r‖^2 - 2*ε*‖v‖)) :=
                (inv_mul_cancel_left₀ hMne _).symm
          _ ≤ (M:ℝ)⁻¹ * (∑ n ∈ Finset.range M,
              inner ℝ ((U^((j+1)*(j+1)*(n*n))) r) v) :=
                mul_le_mul_of_nonneg_left h1 hM1nn
      have havgM := havg M hM
      linarith
    have hle : (0:ℝ) ≤ -((‖r‖^2 - 2*ε*‖v‖)) :=
      le_of_tendsto_of_tendsto hLHS hBlim hAleB
    linarith
  have hr0 : r = 0 := by
    by_contra hcon
    have hrpos : (0:ℝ) < ‖r‖ := by
      rcases eq_or_lt_of_le (norm_nonneg r) with h | h
      · exfalso
        apply hcon
        simpa using h.symm
      · exact h
    have hR : (0:ℝ) < ‖r‖^2 := pow_pos hrpos 2
    have hden : (0:ℝ) < 4*(‖v‖+1) := by positivity
    have hdenne : 4*(‖v‖+1) ≠ 0 := ne_of_gt hden
    have hmain2 := hmain (‖r‖^2/(4*(‖v‖+1))) (div_pos hR hden)
    have hclear : ‖r‖^2 * (4*(‖v‖+1)) ≤ 2*‖r‖^2*‖v‖ := by
      have hmul := mul_le_mul_of_nonneg_right hmain2 hden.le
      have eED : 2*(‖r‖^2/(4*(‖v‖+1)))*‖v‖*(4*(‖v‖+1)) = 2*‖r‖^2*‖v‖ := by
        field_simp
      rwa [eED] at hmul
    have hexpand : ‖r‖^2 * (4*(‖v‖+1)) = 4*(‖r‖^2*‖v‖) + 4*‖r‖^2 := by ring
    have hRV : (0:ℝ) ≤ ‖r‖^2*‖v‖ := mul_nonneg (sq_nonneg _) (norm_nonneg _)
    linarith [hclear, hR, hRV, hexpand]
  have hvw : v = w := by
    rw [hwdef, hr0, sub_zero]
  intro u hu
  have huW : u ∈ sarkozyWclos U := by
    have e1 : (U^1) u = u := by
      rw [pow_one]
      exact hu
    have h1 : u ∈ sarkozyFix U 1 := sarkozyFix_mem U 1 u e1
    have h2 : sarkozyFix U 1 ≤ ⨆ j : ℕ, sarkozyFix U (j + 1) :=
      le_iSup (fun j => sarkozyFix U (j + 1)) 0
    exact Submodule.le_topologicalClosure _ (h2 h1)
  rw [hvw]
  exact Submodule.inner_right_of_mem_orthogonal huW hw_mem

/-- Mean-ergodic fixed vector with positive correlation (N12). -/
theorem sarkozy_fixed_inner_pos {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (U : H →ₗᵢ[ℝ] H) (v : H) (δ : ℝ)
    (hδ : 0 < δ)
    (hfej : ∀ L : ℕ, 0 < L → (L:ℝ)^2 * δ^2 ≤ ∑ h ∈ Finset.range L, ∑ h' ∈ Finset.range L,
      inner ℝ ((U^h) v) ((U^h') v)) :
    ∃ u : H, (U u = u) ∧ 0 < inner ℝ u v := by
  have hnormT : ‖(U.toContinuousLinearMap : H →L[ℝ] H)‖ ≤ 1 :=
    LinearIsometry.norm_toContinuousLinearMap_le _
  have hergodic := ContinuousLinearMap.tendsto_birkhoffAverage_orthogonalProjection
    (U.toContinuousLinearMap) hnormT v
  have hclosed : IsClosed (((U.toContinuousLinearMap).eqLocus 1 :
      Submodule ℝ H) : Set H) := by
    change IsClosed {x : H | (U.toContinuousLinearMap) x = (1 : H →L[ℝ] H) x}
    exact isClosed_eq (U.toContinuousLinearMap).continuous (1 : H →L[ℝ] H).continuous
  let _hcomplete : CompleteSpace
      ↥(((U.toContinuousLinearMap).eqLocus 1 : Submodule ℝ H)) :=
    completeSpace_coe_iff_isComplete.mpr hclosed.isComplete
  let _hproj : ((U.toContinuousLinearMap).eqLocus 1).HasOrthogonalProjection :=
    inferInstance
  set p : H := (((U.toContinuousLinearMap).eqLocus 1).orthogonalProjectionOnto v : H)
    with hpdef
  have hmemT : p ∈ (U.toContinuousLinearMap).eqLocus 1 := by
    rw [hpdef]
    exact (((U.toContinuousLinearMap).eqLocus 1).orthogonalProjectionOnto v).2
  -- Birkhoff averages are scaled orbit sums
  have havec : ∀ L : ℕ, birkhoffAverage ℝ (⇑(U.toContinuousLinearMap)) id L v
      = (L:ℝ)⁻¹ • ∑ h ∈ Finset.range L, ((U^h) v) := by
    intro L
    simp only [birkhoffAverage, birkhoffSum]
    congr 1
    apply Finset.sum_congr rfl
    intro h _
    simp only [LinearIsometry.coe_pow, LinearIsometry.coe_toContinuousLinearMap, id_eq]
  have hnormsq : ∀ L : ℕ, ‖birkhoffAverage ℝ (⇑(U.toContinuousLinearMap)) id L v‖^2
      = (L:ℝ)⁻¹^2 * (∑ h ∈ Finset.range L, ∑ h' ∈ Finset.range L,
        inner ℝ ((U^h) v) ((U^h') v)) := by
    intro L
    have e1 : ‖(L:ℝ)⁻¹‖^2 = (L:ℝ)⁻¹^2 := by
      rw [Real.norm_eq_abs, sq_abs]
    have e2 : ‖∑ h ∈ Finset.range L, ((U^h) v)‖^2
        = ∑ h ∈ Finset.range L, ∑ h' ∈ Finset.range L,
          inner ℝ ((U^h) v) ((U^h') v) := by
      rw [← real_inner_self_eq_norm_sq, sum_inner]
      apply Finset.sum_congr rfl
      intro h _
      exact inner_sum _ _ _
    rw [havec L, norm_smul, mul_pow, e1, e2]
  have hδle : ∀ L : ℕ, 1 ≤ L → δ ≤ ‖birkhoffAverage ℝ (⇑(U.toContinuousLinearMap)) id L v‖ := by
    intro L hL
    have hsqL := hnormsq L
    have hfejL := hfej L (by omega : 0 < L)
    have hsq_bound : δ^2 ≤ ‖birkhoffAverage ℝ (⇑(U.toContinuousLinearMap)) id L v‖^2 := by
      rw [hsqL]
      have hMne : (L:ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hL))
      have hnn : (0:ℝ) ≤ (L:ℝ)⁻¹^2 :=
        pow_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) 2
      calc δ^2 = (L:ℝ)⁻¹^2 * ((L:ℝ)^2 * δ^2) := by field_simp
        _ ≤ (L:ℝ)⁻¹^2 * (∑ h ∈ Finset.range L, ∑ h' ∈ Finset.range L,
            inner ℝ ((U^h) v) ((U^h') v)) :=
            mul_le_mul_of_nonneg_left hfejL hnn
    have h := abs_le_of_sq_le_sq hsq_bound (norm_nonneg _)
    rwa [abs_of_pos hδ] at h
  have hnormlim := Filter.Tendsto.norm hergodic
  have hinev : ∀ᶠ L in Filter.atTop,
      δ ≤ ‖birkhoffAverage ℝ (⇑(U.toContinuousLinearMap)) id L v‖ := by
    rw [Filter.eventually_atTop]
    exact ⟨1, fun L hL => hδle L hL⟩
  have hple : δ ≤ ‖p‖ := by
    have h := ge_of_tendsto hnormlim hinev
    rw [hpdef]
    exact h
  have hu : U p = p := by
    have h := hmemT
    rw [LinearMap.mem_eqLocus] at h
    change (U p = p)
    exact h
  have hvo : v - p ∈ ((U.toContinuousLinearMap).eqLocus 1)ᗮ :=
    Submodule.sub_starProjection_mem_orthogonal v
  have hinner : inner ℝ p v = ‖p‖^2 := by
    have e : v = p + (v - p) := by abel
    rw [e, inner_add_right, real_inner_self_eq_norm_sq]
    have h0 : inner ℝ p (v - p) = 0 :=
      Submodule.inner_right_of_mem_orthogonal hmemT hvo
    rw [h0, add_zero]
  refine ⟨p, hu, ?_⟩
  rw [hinner]
  calc (0:ℝ) < δ^2 := by positivity
    _ ≤ ‖p‖^2 := pow_le_pow_left₀ hδ.le hple 2

/--
If `A ⊆ ℕ` has positive upper density, witnessed by `δ > 0` with `δ * N ≤ |A ∩ range N|` for
arbitrarily large `N`, then there are `a, b, k ∈ ℕ` with `a ∈ A`, `b ∈ A`, `0 < k`, `a < b`, and
`b = a + k * k`. Source: A. Sárközy, Acta Math. Acad. Sci. Hungar. 31 (1978) and H. Furstenberg,
J. Analyse Math. 31 (1977); Lean states positive upper density via `initialSegmentCount` with
arbitrarily large N.

Proves `Wanted` entry `furstenberg_sarkozy`.
-/
theorem furstenberg_sarkozy :
    ∀ A : Set ℕ,
      (∃ δ : ℝ, 0 < δ ∧ ∀ M : ℕ, ∃ N : ℕ, M ≤ N ∧
        δ * (N : ℝ) ≤ ((initialSegmentCount A N : ℕ) : ℝ)) →
      ∃ a b k : ℕ, a ∈ A ∧ b ∈ A ∧ 0 < k ∧ a < b ∧ b = a + k * k := by
  intro A hA
  obtain ⟨δ, hδ, hfreq⟩ := hA
  by_contra hcon
  push Not at hcon
  obtain ⟨γ, hsymm, hpos, hzero, hfej⟩ := sarkozy_corr_limit A δ hδ hfreq hcon
  obtain ⟨E, hN, hI, hC, U, v, huv⟩ := sarkozy_dilation γ hsymm hpos
  let hN' := hN
  let hI' := hI
  let hC' := hC
  have hU0 : ((U ^ (0:ℕ)) v) = v := by simp
  have h11hyp : ∀ k : ℕ, 0 < k → inner ℝ ((U ^ (k*k)) v) v = 0 := by
    intro k hk
    have h1 : inner ℝ ((U ^ (k*k)) v) ((U ^ (0:ℕ)) v)
        = γ ((((k*k : ℕ)):ℤ) - (((0:ℕ)):ℤ)) := huv (k*k) 0
    rw [hU0] at h1
    rw [h1]
    have ecast : ((((k*k : ℕ)):ℤ) - (((0:ℕ)):ℤ)) = (k:ℤ)*(k:ℤ) := by
      rw [Nat.cast_mul, Nat.cast_zero, sub_zero]
    rw [ecast]
    exact hzero k hk
  have h12hyp : ∀ L : ℕ, 0 < L → (L:ℝ)^2 * δ^2 ≤ ∑ h ∈ Finset.range L,
      ∑ h' ∈ Finset.range L, inner ℝ ((U^h) v) ((U^h') v) := by
    intro L hL
    calc (L:ℝ)^2 * δ^2
        ≤ ∑ h ∈ Finset.range L, ∑ h' ∈ Finset.range L, γ ((h:ℤ) - h') :=
          hfej L hL
      _ = ∑ h ∈ Finset.range L, ∑ h' ∈ Finset.range L,
          inner ℝ ((U^h) v) ((U^h') v) := by
          apply Finset.sum_congr rfl
          intro h _
          apply Finset.sum_congr rfl
          intro h' _
          exact (huv h h').symm
  obtain ⟨u, hu, hpos_inner⟩ := sarkozy_fixed_inner_pos U v δ hδ h12hyp
  have h11 := sarkozy_hilbert_sarkozy U v h11hyp u hu
  linarith

end MathlibExt.Combinatorics.Additive.SarkozyWanted
