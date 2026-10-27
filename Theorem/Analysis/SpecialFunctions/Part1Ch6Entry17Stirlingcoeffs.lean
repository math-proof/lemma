/-
Author: @akiezun, Avocado
-/
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
open scoped BigOperators
open Filter Finset Topology


-- Supergeometric factor: (i+1) * A^i * X^(i*(i+1)) is summable when
-- 0 ≤ A, 0 ≤ X ≤ 1, and A < 1 in the boundary case X = 1.
theorem supergeom_summable (A X : ℝ) (hA0 : 0 ≤ A) (hX0 : 0 ≤ X)
    (hX1 : X ≤ 1) (hlt : X = 1 → A < 1) :
    Summable fun i : ℕ => ((i : ℝ) + 1) * A ^ i * X ^ (i * (i + 1)) := by
  by_cases hXeq : X = 1
  · subst hXeq
    have hA : ‖A‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg hA0]; exact hlt rfl
    have g1 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hA
    have g0 := summable_geometric_of_norm_lt_one hA
    have hcongr : (fun i : ℕ => ((i : ℝ) + 1) * A ^ i * (1 : ℝ) ^ (i * (i + 1)))
        = (fun i : ℕ => (i : ℝ) ^ 1 * A ^ i + A ^ i) := by
      funext i; simp [one_pow, pow_one]; ring
    rw [hcongr]
    exact g1.add g0
  · have hXlt : X < 1 := lt_of_le_of_ne hX1 hXeq
    have hX2 : ‖X ^ 2‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hX0 2)]
      exact pow_lt_one₀ hX0 hXlt two_ne_zero
    have gpow := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hX2
    -- ratio factor c i → 0
    set c : ℕ → ℝ := fun i => ((i : ℝ) + 2) / ((i : ℝ) + 1) * A * X ^ (2 * (i + 1)) with hcdef
    have hc0 : ∀ i : ℕ, 0 ≤ c i := by
      intro i
      apply mul_nonneg
      · apply mul_nonneg
        · apply div_nonneg
          · have := Nat.cast_nonneg (α := ℝ) i; linarith
          · have := Nat.cast_nonneg (α := ℝ) i; linarith
        · exact hA0
      · exact pow_nonneg hX0 _
    have hc_le : ∀ i : ℕ, c i ≤ 2 * A * (X ^ 2) ^ (i + 1) := by
      intro i
      have hfrac : ((i : ℝ) + 2) / ((i : ℝ) + 1) ≤ 2 := by
        have hpos : (0 : ℝ) < (i : ℝ) + 1 := by
          have := Nat.cast_nonneg (α := ℝ) i; linarith
        rw [div_le_iff₀ hpos]
        have := Nat.cast_nonneg (α := ℝ) i; linarith
      have hXeq2 : X ^ (2 * (i + 1)) = (X ^ 2) ^ (i + 1) := by rw [pow_mul]
      have hnn : 0 ≤ A * (X ^ 2) ^ (i + 1) :=
        mul_nonneg hA0 (pow_nonneg (pow_nonneg hX0 2) _)
      calc c i = ((i : ℝ) + 2) / ((i : ℝ) + 1) * (A * (X ^ 2) ^ (i + 1)) := by
            simp only [hcdef]; rw [hXeq2]; ring
        _ ≤ 2 * (A * (X ^ 2) ^ (i + 1)) :=
            mul_le_mul_of_nonneg_right hfrac hnn
        _ = 2 * A * (X ^ 2) ^ (i + 1) := by ring
    have hlim : Tendsto (fun i : ℕ => 2 * A * (X ^ 2) ^ (i + 1)) atTop (𝓝 0) := by
      have hbase : Tendsto (fun i : ℕ => (2 * A * X ^ 2) * (X ^ 2) ^ i) atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds.mul gpow)
      refine hbase.congr (fun i => ?_)
      rw [pow_succ']; ring
    have hc_tend : Tendsto c atTop (𝓝 0) :=
      squeeze_zero hc0 (fun i => hc_le i) hlim
    -- step equation u (i+1) = c i * u i
    have hstep : ∀ i : ℕ,
        (((i + 1 : ℕ) : ℝ) + 1) * A ^ (i + 1) * X ^ ((i + 1) * (i + 1 + 1))
          = c i * (((i : ℝ) + 1) * A ^ i * X ^ (i * (i + 1))) := by
      intro i
      have eA : A ^ (i + 1) = A ^ i * A := pow_succ A i
      have eX : X ^ ((i + 1) * (i + 1 + 1)) = X ^ (i * (i + 1)) * X ^ (2 * (i + 1)) := by
        rw [← pow_add]; congr 1; ring
      have ecast : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
      have hpos : (0 : ℝ) < (i : ℝ) + 1 := by
        have := Nat.cast_nonneg (α := ℝ) i; linarith
      rw [ecast, eA, eX]
      simp only [hcdef]
      field_simp
      ring
    have hnn : ∀ i : ℕ, 0 ≤ ((i : ℝ) + 1) * A ^ i * X ^ (i * (i + 1)) := by
      intro i
      apply mul_nonneg
      · apply mul_nonneg
        · have := Nat.cast_nonneg (α := ℝ) i; linarith
        · exact pow_nonneg hA0 _
      · exact pow_nonneg hX0 _
    apply summable_of_ratio_norm_eventually_le (r := 1 / 2) (by norm_num)
    have hev : ∀ᶠ i in atTop, c i < 1 / 2 :=
      hc_tend.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
    refine hev.mono (fun i hi => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hnn (i + 1)),
      abs_of_nonneg (hnn i), hstep i]
    exact mul_le_mul_of_nonneg_right (le_of_lt hi) (hnn i)

-- Plain supergeometric factor, derived from the linear-weighted version.
theorem supergeom_summable_plain (A X : ℝ) (hA0 : 0 ≤ A) (hX0 : 0 ≤ X)
    (hX1 : X ≤ 1) (hlt : X = 1 → A < 1) :
    Summable fun i : ℕ => A ^ i * X ^ (i * (i + 1)) := by
  have hsup := supergeom_summable A X hA0 hX0 hX1 hlt
  apply Summable.of_norm_bounded hsup
  intro i
  have hnn : 0 ≤ A ^ i * X ^ (i * (i + 1)) :=
    mul_nonneg (pow_nonneg hA0 _) (pow_nonneg hX0 _)
  have h1i : (1 : ℝ) ≤ (i : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) i; linarith
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  calc A ^ i * X ^ (i * (i + 1)) = 1 * (A ^ i * X ^ (i * (i + 1))) := (one_mul _).symm
    _ ≤ ((i : ℝ) + 1) * (A ^ i * X ^ (i * (i + 1))) :=
        mul_le_mul_of_nonneg_right h1i hnn
    _ = ((i : ℝ) + 1) * A ^ i * X ^ (i * (i + 1)) := by ring

-- Tail of a geometric series.
theorem geom_tail_summable (r : ℝ) (hr : ‖r‖ < 1) :
    Summable fun j : ℕ => r ^ (j + 1) := by
  have g := summable_geometric_of_norm_lt_one hr (R := ℝ)
  exact (g.mul_right r).congr (fun j => (pow_succ r j).symm)

-- Linear-weighted tail of a geometric series.
theorem geom_weighted_summable (r : ℝ) (hr : ‖r‖ < 1) :
    Summable fun j : ℕ => ((j : ℝ) + 1) * r ^ (j + 1) := by
  have g1 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hr
  have g0 := summable_geometric_of_norm_lt_one hr (R := ℝ)
  have hcongr : (fun j : ℕ => ((j : ℝ) + 1) * r ^ (j + 1))
      = (fun j : ℕ => r * ((j : ℝ) ^ 1 * r ^ j) + r * r ^ j) := by
    funext j; simp only [pow_succ]; ring
  rw [hcongr]
  exact (g1.mul_left r).add (g0.mul_left r)

-- Value of a geometric row sum.
theorem row_geom_value (C r : ℝ) (hr : ‖r‖ < 1) :
    ∑' j : ℕ, C * r ^ j = C / (1 - r) := by
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hr, div_eq_mul_inv]

-- Value of a linear-weighted geometric row sum.
theorem row_weighted_value (C r : ℝ) (hr : ‖r‖ < 1) :
    ∑' j : ℕ, ((j : ℝ) + 1) * (C * r ^ j) = C / (1 - r) ^ 2 := by
  have hs := (hasSum_coe_mul_geometric_of_norm_lt_one hr).summable
  have g0 := summable_geometric_of_norm_lt_one hr (R := ℝ)
  have hr1 : r ≠ 1 := by
    intro h; rw [h, norm_one] at hr; exact lt_irrefl 1 hr
  have h1r : (1 : ℝ) - r ≠ 0 := sub_ne_zero.mpr (Ne.symm hr1)
  have hcongr : (fun j : ℕ => ((j : ℝ) + 1) * (C * r ^ j))
      = (fun j : ℕ => C * ((j : ℝ) * r ^ j) + C * (r ^ j)) := by
    funext j; ring
  rw [hcongr, Summable.tsum_add (hs.mul_left C) (g0.mul_left C),
    tsum_mul_left, tsum_mul_left,
    (hasSum_coe_mul_geometric_of_norm_lt_one hr).tsum_eq,
    tsum_geometric_of_norm_lt_one hr]
  field_simp
  ring

-- Factorization of the double-series summand along rows.
theorem G_row_factor (m nu x : ℝ) (k j : ℕ) :
    m ^ k * nu ^ (k + j + 1) * x ^ (k * (k + j + 1))
      = (m ^ k * nu ^ (k + 1) * x ^ (k * (k + 1))) * (nu * x ^ k) ^ j := by
  have e1 : k + j + 1 = (k + 1) + j := by omega
  have e2 : k * (k + j + 1) = k * (k + 1) + k * j := by ring
  rw [e2, e1, mul_pow, ← pow_mul, pow_add, pow_add]
  ring

-- The second-series numerator is m times the row numerator.
theorem second_num_factor (m nu x : ℝ) (k : ℕ) :
    (m * nu * x ^ k) ^ (k + 1) = m * (m ^ k * nu ^ (k + 1) * x ^ (k * (k + 1))) := by
  have e : (m * nu * x ^ k) ^ (k + 1)
      = m ^ (k + 1) * nu ^ (k + 1) * (x ^ k) ^ (k + 1) := by
    rw [mul_pow, mul_pow]
  rw [e, ← pow_mul, pow_succ m k]
  ring

-- Pieces for the first-term algebra.
theorem first_alg_ts (m nu x : ℝ) (k : ℕ) :
    m * nu * x ^ (2 * k) = (m * x ^ k) * (nu * x ^ k) := by
  have ex : x ^ (2 * k) = x ^ k * x ^ k := by
    rw [← pow_add]; congr 1; omega
  rw [ex]; ring

theorem first_alg_tkq (m nu x : ℝ) (k : ℕ) :
    (m * nu * x ^ k) ^ k = (m * x ^ k) ^ k * nu ^ k := by
  rw [show m * nu * x ^ k = (m * x ^ k) * nu from by ring, mul_pow]

-- Expanded norm bound for the double-series summand.
theorem G_norm_bound (m nu x : ℝ) (_hx : |x| ≤ 1) (i j : ℕ) :
    ‖m ^ i * nu ^ (i + j + 1) * x ^ (i * (i + j + 1))‖
      ≤ (|m * nu| ^ i * |x| ^ (i * (i + 1))) * (|nu| ^ (j + 1) * |x| ^ (i * j)) := by
  have e2 : i * (i + j + 1) = i * (i + 1) + i * j := by ring
  have e1 : i + j + 1 = i + (j + 1) := by omega
  have eA : |m * nu| ^ i = |m| ^ i * |nu| ^ i := by rw [abs_mul, mul_pow]
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_pow, abs_pow, e2, e1,
    pow_add, pow_add, eA]
  exact le_of_eq (by ring)

-- The double series G is absolutely summable.
theorem G_summable (m nu x : ℝ) (hx : |x| ≤ 1) (hnu : |nu| < 1)
    (hboundary : |x| = 1 → |m * nu| < 1) :
    Summable fun p : ℕ × ℕ =>
      m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1)) := by
  have hU := supergeom_summable_plain |m * nu| |x| (abs_nonneg _) (abs_nonneg _) hx
    (fun h => hboundary h)
  have hV : Summable fun j : ℕ => |nu| ^ (j + 1) :=
    geom_tail_summable |nu| (by rw [Real.norm_eq_abs, abs_abs]; exact hnu)
  have hUV := hU.mul_of_nonneg hV
    (fun i => mul_nonneg (pow_nonneg (abs_nonneg _) _) (pow_nonneg (abs_nonneg _) _))
    (fun j => pow_nonneg (abs_nonneg _) _)
  apply Summable.of_norm_bounded hUV
  intro ⟨i, j⟩
  have hXij : |x| ^ (i * j) ≤ 1 := pow_le_one₀ (abs_nonneg _) hx
  have hnn : 0 ≤ |m * nu| ^ i * |x| ^ (i * (i + 1)) := by positivity
  have hnn2 : 0 ≤ |nu| ^ (j + 1) := pow_nonneg (abs_nonneg _) _
  calc ‖m ^ i * nu ^ (i + j + 1) * x ^ (i * (i + j + 1))‖
        ≤ (|m * nu| ^ i * |x| ^ (i * (i + 1))) * (|nu| ^ (j + 1) * |x| ^ (i * j)) :=
          G_norm_bound m nu x hx i j
      _ ≤ (|m * nu| ^ i * |x| ^ (i * (i + 1))) * (|nu| ^ (j + 1) * 1) := by
          apply mul_le_mul_of_nonneg_left _ hnn
          exact mul_le_mul_of_nonneg_left hXij hnn2
      _ = |m * nu| ^ i * |x| ^ (i * (i + 1)) * |nu| ^ (j + 1) := by ring

-- The (i+1)-weighted double series is summable.
theorem Gi_summable (m nu x : ℝ) (hx : |x| ≤ 1) (hnu : |nu| < 1)
    (hboundary : |x| = 1 → |m * nu| < 1) :
    Summable fun p : ℕ × ℕ => ((p.1 : ℝ) + 1) *
      (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1))) := by
  have hU := supergeom_summable |m * nu| |x| (abs_nonneg _) (abs_nonneg _) hx
    (fun h => hboundary h)
  have hV : Summable fun j : ℕ => |nu| ^ (j + 1) :=
    geom_tail_summable |nu| (by rw [Real.norm_eq_abs, abs_abs]; exact hnu)
  have hnnU : ∀ i : ℕ, 0 ≤ ((i : ℝ) + 1) * |m * nu| ^ i * |x| ^ (i * (i + 1)) := by
    intro i
    apply mul_nonneg
    · apply mul_nonneg
      · have := Nat.cast_nonneg (α := ℝ) i; linarith
      · exact pow_nonneg (abs_nonneg _) _
    · exact pow_nonneg (abs_nonneg _) _
  have hUV := hU.mul_of_nonneg hV hnnU (fun j => pow_nonneg (abs_nonneg _) _)
  have hbound : ∀ i j : ℕ, ‖((i : ℝ) + 1) *
      (m ^ i * nu ^ (i + j + 1) * x ^ (i * (i + j + 1)))‖
      ≤ (((i : ℝ) + 1) * |m * nu| ^ i * |x| ^ (i * (i + 1))) * |nu| ^ (j + 1) := by
    intro i j
    have hfi : (0 : ℝ) ≤ (i : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) i; linarith
    have hXij : |x| ^ (i * j) ≤ 1 := pow_le_one₀ (abs_nonneg _) hx
    have hnnUij : 0 ≤ ((i : ℝ) + 1) * (|m * nu| ^ i * |x| ^ (i * (i + 1))) := by
      positivity
    have hnn2 : 0 ≤ |nu| ^ (j + 1) := pow_nonneg (abs_nonneg _) _
    have efac : ‖((i : ℝ) + 1) * (m ^ i * nu ^ (i + j + 1) * x ^ (i * (i + j + 1)))‖
        = ((i : ℝ) + 1) * ‖m ^ i * nu ^ (i + j + 1) * x ^ (i * (i + j + 1))‖ := by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg hfi,
        ← Real.norm_eq_abs]
    rw [efac]
    refine le_trans
      (mul_le_mul_of_nonneg_left (G_norm_bound m nu x hx i j) hfi) ?_
    have hle : |nu| ^ (j + 1) * |x| ^ (i * j) ≤ |nu| ^ (j + 1) * 1 :=
      mul_le_mul_of_nonneg_left hXij hnn2
    calc ((i : ℝ) + 1) * ((|m * nu| ^ i * |x| ^ (i * (i + 1))) *
            (|nu| ^ (j + 1) * |x| ^ (i * j)))
          = (((i : ℝ) + 1) * (|m * nu| ^ i * |x| ^ (i * (i + 1)))) *
            (|nu| ^ (j + 1) * |x| ^ (i * j)) := by rw [← mul_assoc]
        _ ≤ (((i : ℝ) + 1) * (|m * nu| ^ i * |x| ^ (i * (i + 1)))) *
            (|nu| ^ (j + 1) * 1) :=
          mul_le_mul_of_nonneg_left hle hnnUij
        _ = (((i : ℝ) + 1) * |m * nu| ^ i * |x| ^ (i * (i + 1))) * |nu| ^ (j + 1) := by
          rw [mul_one, ← mul_assoc]
  apply Summable.of_norm_bounded hUV
  intro ⟨i, j⟩
  exact hbound i j

-- The (j+1)-weighted double series is summable.
theorem Gj_summable (m nu x : ℝ) (hx : |x| ≤ 1) (hnu : |nu| < 1)
    (hboundary : |x| = 1 → |m * nu| < 1) :
    Summable fun p : ℕ × ℕ => ((p.2 : ℝ) + 1) *
      (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1))) := by
  have hU := supergeom_summable_plain |m * nu| |x| (abs_nonneg _) (abs_nonneg _) hx
    (fun h => hboundary h)
  have hV := geom_weighted_summable |nu|
    (by rw [Real.norm_eq_abs, abs_abs]; exact hnu)
  have hUV := hU.mul_of_nonneg hV
    (fun i => mul_nonneg (pow_nonneg (abs_nonneg _) _) (pow_nonneg (abs_nonneg _) _))
    (fun j => mul_nonneg (by have := Nat.cast_nonneg (α := ℝ) j; linarith)
      (pow_nonneg (abs_nonneg _) _))
  have hbound : ∀ i j : ℕ, ‖((j : ℝ) + 1) *
      (m ^ i * nu ^ (i + j + 1) * x ^ (i * (i + j + 1)))‖
      ≤ (|m * nu| ^ i * |x| ^ (i * (i + 1))) * (((j : ℝ) + 1) * |nu| ^ (j + 1)) := by
    intro i j
    have hfj : (0 : ℝ) ≤ (j : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) j; linarith
    have hXij : |x| ^ (i * j) ≤ 1 := pow_le_one₀ (abs_nonneg _) hx
    have hnn : 0 ≤ |m * nu| ^ i * |x| ^ (i * (i + 1)) := by positivity
    have hnn2 : 0 ≤ ((j : ℝ) + 1) * |nu| ^ (j + 1) := mul_nonneg hfj
      (pow_nonneg (abs_nonneg _) _)
    have efac : ‖((j : ℝ) + 1) * (m ^ i * nu ^ (i + j + 1) * x ^ (i * (i + j + 1)))‖
        = ((j : ℝ) + 1) * ‖m ^ i * nu ^ (i + j + 1) * x ^ (i * (i + j + 1))‖ := by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg hfj,
        ← Real.norm_eq_abs]
    rw [efac]
    refine le_trans
      (mul_le_mul_of_nonneg_left (G_norm_bound m nu x hx i j) hfj) ?_
    have hle : ((j : ℝ) + 1) * |nu| ^ (j + 1) * |x| ^ (i * j)
        ≤ ((j : ℝ) + 1) * |nu| ^ (j + 1) * 1 :=
      mul_le_mul_of_nonneg_left hXij hnn2
    calc ((j : ℝ) + 1) * ((|m * nu| ^ i * |x| ^ (i * (i + 1))) *
            (|nu| ^ (j + 1) * |x| ^ (i * j)))
          = (|m * nu| ^ i * |x| ^ (i * (i + 1))) *
            (((j : ℝ) + 1) * |nu| ^ (j + 1) * |x| ^ (i * j)) := by ring
        _ ≤ (|m * nu| ^ i * |x| ^ (i * (i + 1))) *
            (((j : ℝ) + 1) * |nu| ^ (j + 1) * 1) :=
          mul_le_mul_of_nonneg_left hle hnn
        _ = (|m * nu| ^ i * |x| ^ (i * (i + 1))) *
            (((j : ℝ) + 1) * |nu| ^ (j + 1)) := by rw [mul_one]
  apply Summable.of_norm_bounded hUV
  intro ⟨i, j⟩
  exact hbound i j

-- Row sums of G are geometric.
theorem Grow_tsum (m nu x : ℝ) (k : ℕ) (hr : ‖nu * x ^ k‖ < 1) :
    ∑' j : ℕ, m ^ k * nu ^ (k + j + 1) * x ^ (k * (k + j + 1))
      = (m ^ k * nu ^ (k + 1) * x ^ (k * (k + 1))) / (1 - nu * x ^ k) := by
  have hcongr : (fun j : ℕ => m ^ k * nu ^ (k + j + 1) * x ^ (k * (k + j + 1)))
      = (fun j : ℕ => (m ^ k * nu ^ (k + 1) * x ^ (k * (k + 1))) * (nu * x ^ k) ^ j) :=
    funext (fun j => G_row_factor m nu x k j)
  rw [hcongr]
  exact row_geom_value _ _ hr

-- Weighted row sums of G.
theorem Grow_weighted_tsum (m nu x : ℝ) (k : ℕ) (hr : ‖nu * x ^ k‖ < 1) :
    ∑' j : ℕ, ((j : ℝ) + 1) *
        (m ^ k * nu ^ (k + j + 1) * x ^ (k * (k + j + 1)))
      = (m ^ k * nu ^ (k + 1) * x ^ (k * (k + 1))) / (1 - nu * x ^ k) ^ 2 := by
  have hcongr : (fun j : ℕ => ((j : ℝ) + 1) *
        (m ^ k * nu ^ (k + j + 1) * x ^ (k * (k + j + 1))))
      = (fun j : ℕ => ((j : ℝ) + 1) *
        ((m ^ k * nu ^ (k + 1) * x ^ (k * (k + 1))) * (nu * x ^ k) ^ j)) := by
    funext j
    congr 1
    exact G_row_factor m nu x k j
  rw [hcongr]
  exact row_weighted_value _ _ hr

