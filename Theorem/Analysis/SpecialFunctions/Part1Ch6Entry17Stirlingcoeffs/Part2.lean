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
import Def.Analysis.SpecialFunctions.Part1Ch6Entry17Stirlingcoeffs
open scoped BigOperators
open Filter Finset Topology


-- Norm bound for the geometric factor nu * x^k.
theorem row_norm_aux (nu x : ℝ) (hx : |x| ≤ 1) (hnu : |nu| < 1) (k : ℕ) :
    ‖nu * x ^ k‖ < 1 := by
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  calc |nu| * |x| ^ k ≤ |nu| * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ (abs_nonneg _) hx) (abs_nonneg _)
    _ = |nu| := mul_one _
    _ < 1 := hnu

-- Nonvanishing of 1 - nu * x^k.
theorem nu_ne_aux (nu x : ℝ) (hx : |x| ≤ 1) (hnu : |nu| < 1) (k : ℕ) :
    1 - nu * x ^ k ≠ 0 := by
  have h1 := row_norm_aux nu x hx hnu k
  intro hcon
  have heq : nu * x ^ k = 1 := (sub_eq_zero.mp hcon).symm
  rw [heq, norm_one] at h1
  exact lt_irrefl 1 h1

-- Pointwise bound for the linear-times-geometric numerator.
theorem base_norm_bound (a b nu : ℝ) (k : ℕ) :
    ‖(a + (k : ℝ) * b) * nu ^ k‖ ≤ (|a| + |b| * ((k : ℝ) + 1)) * |nu| ^ k := by
  have hk := Nat.cast_nonneg (α := ℝ) k
  have h1 : |(a + (k : ℝ) * b)| ≤ |a| + |b| * ((k : ℝ) + 1) := by
    have h2 : (k : ℝ) * |b| ≤ |b| * ((k : ℝ) + 1) := by
      rw [mul_comm (k : ℝ) |b|]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      linarith
    calc |(a + (k : ℝ) * b)| ≤ |a| + |(k : ℝ) * b| := abs_add_le _ _
      _ = |a| + (k : ℝ) * |b| := by rw [abs_mul, abs_of_nonneg hk]
      _ ≤ |a| + |b| * ((k : ℝ) + 1) := by linarith
  calc ‖(a + (k : ℝ) * b) * nu ^ k‖ = |(a + (k : ℝ) * b)| * |nu| ^ k := by
        rw [Real.norm_eq_abs, abs_mul, abs_pow]
    _ ≤ (|a| + |b| * ((k : ℝ) + 1)) * |nu| ^ k :=
        mul_le_mul_of_nonneg_right h1 (pow_nonneg (abs_nonneg _) _)

-- Summable majorant for the numerators.
theorem maj_summable (a b nu : ℝ) (hnu : |nu| < 1) :
    Summable fun k : ℕ => (|a| + |b| * ((k : ℝ) + 1)) * |nu| ^ k := by
  have hnuA : ‖|nu|‖ < 1 := by rw [Real.norm_eq_abs, abs_abs]; exact hnu
  have g1 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hnuA
  have g0 := summable_geometric_of_norm_lt_one hnuA (R := ℝ)
  have hcongr : (fun k : ℕ => (|a| + |b| * ((k : ℝ) + 1)) * |nu| ^ k)
      = (fun k : ℕ => |a| * |nu| ^ k
        + (|b| * ((k : ℝ) ^ 1 * |nu| ^ k) + |b| * |nu| ^ k)) := by
    funext k; simp only [pow_one]; ring
  rw [hcongr]
  exact (g0.mul_left |a|).add ((g1.mul_left |b|).add (g0.mul_left |b|))

-- The numerators (a + k b) nu^k are absolutely summable.
theorem base_summable (a b nu : ℝ) (hnu : |nu| < 1) :
    Summable fun k : ℕ => (a + (k : ℝ) * b) * nu ^ k := by
  apply Summable.of_norm_bounded (maj_summable a b nu hnu)
  intro k
  exact base_norm_bound a b nu k

-- Left series, interior case: the cofactor tends to 1.
theorem left_summable_lt (a b m nu x : ℝ) (hxlt : |x| < 1) (hnu : |nu| < 1) :
    Summable fun k : ℕ => (a + (k : ℝ) * b) * nu ^ k / (1 - m * x ^ k) := by
  have hfnorm : Summable fun k : ℕ => ‖(a + (k : ℝ) * b) * nu ^ k‖ := by
    apply Summable.of_norm_bounded (maj_summable a b nu hnu)
    intro k
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact base_norm_bound a b nu k
  have hxk : Tendsto (fun k : ℕ => m * x ^ k) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hxlt))
  have h1 : Tendsto (fun k : ℕ => 1 - m * x ^ k) atTop (𝓝 (1 : ℝ)) := by
    simpa using (tendsto_const_nhds.sub hxk)
  have h2 : Tendsto (fun k : ℕ => (1 - m * x ^ k)⁻¹) cofinite (𝓝 (1 : ℝ)) := by
    rw [Nat.cofinite_eq_atTop]
    simpa using (h1.inv₀ one_ne_zero)
  have hmul := Summable.mul_tendsto_const hfnorm h2
  refine hmul.congr (fun k => ?_)
  change (a + (k : ℝ) * b) * nu ^ k * (1 - m * x ^ k)⁻¹
    = (a + (k : ℝ) * b) * nu ^ k / (1 - m * x ^ k)
  exact (div_eq_mul_inv _ _).symm

-- Left series, boundary case x = 1.
theorem left_summable_one (a b m nu : ℝ) (hnu : |nu| < 1) :
    Summable fun k : ℕ => (a + (k : ℝ) * b) * nu ^ k / (1 - m * (1 : ℝ) ^ k) := by
  have hbase := base_summable a b nu hnu
  have hcongr : (fun k : ℕ => (a + (k : ℝ) * b) * nu ^ k / (1 - m * (1 : ℝ) ^ k))
      = (fun k : ℕ => ((a + (k : ℝ) * b) * nu ^ k) * (1 - m)⁻¹) := by
    funext k; rw [one_pow, mul_one, div_eq_mul_inv]
  rw [hcongr]
  exact hbase.mul_right _

-- Left series, boundary case x = -1.
theorem left_summable_negone (a b m nu : ℝ) (hnu : |nu| < 1) :
    Summable fun k : ℕ => (a + (k : ℝ) * b) * nu ^ k / (1 - m * (-1 : ℝ) ^ k) := by
  have hmaj := maj_summable a b nu hnu
  have hB : ∀ k : ℕ, ‖((1 : ℝ) - m * (-1) ^ k)⁻¹‖ ≤ ‖(1 - m)⁻¹‖ ⊔ ‖(1 + m)⁻¹‖ := by
    intro k
    rcases Nat.even_or_odd k with hev | hodd
    · rw [hev.neg_one_pow, mul_one]
      exact le_max_left _ _
    · have e : (-1 : ℝ) ^ k = -1 := hodd.neg_one_pow
      have e2 : (1 : ℝ) - m * -1 = 1 + m := by ring
      rw [e, e2]
      exact le_max_right _ _
  have hmul := hmaj.mul_left (‖(1 - m)⁻¹‖ ⊔ ‖(1 + m)⁻¹‖)
  apply Summable.of_norm_bounded hmul
  intro k
  calc ‖(a + (k : ℝ) * b) * nu ^ k / (1 - m * (-1) ^ k)‖
      = ‖(a + (k : ℝ) * b) * nu ^ k‖ * ‖((1 : ℝ) - m * (-1) ^ k)⁻¹‖ := by
        rw [div_eq_mul_inv, norm_mul]
    _ ≤ ((|a| + |b| * ((k : ℝ) + 1)) * |nu| ^ k) * (‖(1 - m)⁻¹‖ ⊔ ‖(1 + m)⁻¹‖) :=
        mul_le_mul (base_norm_bound a b nu k) (hB k) (norm_nonneg _)
          (mul_nonneg (add_nonneg (abs_nonneg _)
            (mul_nonneg (abs_nonneg _) (by
              have hk := Nat.cast_nonneg (α := ℝ) k; linarith)))
            (pow_nonneg (abs_nonneg _) _))
    _ = (‖(1 - m)⁻¹‖ ⊔ ‖(1 + m)⁻¹‖) * ((|a| + |b| * ((k : ℝ) + 1)) * |nu| ^ k) := by
        ring

-- Left series in all cases.
theorem left_summable (a b m nu x : ℝ) (hx : |x| ≤ 1) (hnu : |nu| < 1)
    (hmx : ∀ k : ℕ, 1 - m * x ^ k ≠ 0) :
    Summable fun k : ℕ => (a + (k : ℝ) * b) * nu ^ k / (1 - m * x ^ k) := by
  rcases lt_or_eq_of_le hx with hlt | heq
  · exact left_summable_lt a b m nu x hlt hnu
  · have hxval : x = 1 ∨ x = -1 := eq_or_eq_neg_of_abs_eq heq
    rcases hxval with rfl | rfl
    · exact left_summable_one a b m nu hnu
    · exact left_summable_negone a b m nu hnu

-- The i-weighted double series is summable.
theorem IG_summable (m nu x : ℝ) (hx : |x| ≤ 1) (hnu : |nu| < 1)
    (hboundary : |x| = 1 → |m * nu| < 1) :
    Summable fun p : ℕ × ℕ => (p.1 : ℝ) *
      (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1))) := by
  have hsub := (Gi_summable m nu x hx hnu hboundary).sub
    (G_summable m nu x hx hnu hboundary)
  exact hsub.congr (fun p => by ring)

-- The j-weighted double series is summable.
theorem JG_summable (m nu x : ℝ) (hx : |x| ≤ 1) (hnu : |nu| < 1)
    (hboundary : |x| = 1 → |m * nu| < 1) :
    Summable fun p : ℕ × ℕ => (p.2 : ℝ) *
      (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1))) := by
  have hsub := (Gj_summable m nu x hx hnu hboundary).sub
    (G_summable m nu x hx hnu hboundary)
  exact hsub.congr (fun p => by ring)

-- The (a + i b)-weighted double series is summable (Q side).
theorem W1_summable (a b m nu x : ℝ) (hx : |x| ≤ 1) (hnu : |nu| < 1)
    (hboundary : |x| = 1 → |m * nu| < 1) :
    Summable fun p : ℕ × ℕ => (a + (p.1 : ℝ) * b) *
      (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1))) := by
  have hG := G_summable m nu x hx hnu hboundary
  have hIG := IG_summable m nu x hx hnu hboundary
  have hcongr : (fun p : ℕ × ℕ => (a + (p.1 : ℝ) * b) *
        (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1))))
      = (fun p : ℕ × ℕ => a * (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1)))
        + b * ((p.1 : ℝ) * (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1))))) := by
    funext p; ring
  rw [hcongr]
  exact (hG.mul_left a).add (hIG.mul_left b)

-- The (a + (i+j+1) b)-weighted double series is summable (D side).
theorem W2_summable (a b m nu x : ℝ) (hx : |x| ≤ 1) (hnu : |nu| < 1)
    (hboundary : |x| = 1 → |m * nu| < 1) :
    Summable fun p : ℕ × ℕ => (a + (((p.1 + p.2 + 1 : ℕ)) : ℝ) * b) *
      (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1))) := by
  have hG := G_summable m nu x hx hnu hboundary
  have hIG := IG_summable m nu x hx hnu hboundary
  have hJG := JG_summable m nu x hx hnu hboundary
  have hcongr : (fun p : ℕ × ℕ => (a + (((p.1 + p.2 + 1 : ℕ)) : ℝ) * b) *
        (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1))))
      = (fun p : ℕ × ℕ => (a + b) * (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1)))
        + (b * ((p.1 : ℝ) * (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1))))
          + b * ((p.2 : ℝ) * (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1)))))) := by
    funext p; push_cast; ring
  rw [hcongr]
  exact (hG.mul_left (a + b)).add ((hIG.mul_left b).add (hJG.mul_left b))

-- Row sums on the Q side.
theorem Qrow_value (a b m nu x : ℝ) (k : ℕ) (hr : ‖nu * x ^ k‖ < 1) :
    (∑' j : ℕ, (a + (k : ℝ) * b) *
      (m ^ k * nu ^ (k + j + 1) * x ^ (k * (k + j + 1))))
      = (a + (k : ℝ) * b) *
        ((m ^ k * nu ^ (k + 1) * x ^ (k * (k + 1))) / (1 - nu * x ^ k)) := by
  rw [tsum_mul_left]
  congr 1
  exact Grow_tsum m nu x k hr

-- Diagonal terms equal nu^k * (m * x^k)^i.
theorem Dterm_value (a b m nu x : ℝ) (k i : ℕ) (h : i < k) :
    (fun p : ℕ × ℕ => (a + (((p.1 + p.2 + 1 : ℕ)) : ℝ) * b) *
      (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1)))) (i, k - 1 - i)
      = (a + (k : ℝ) * b) * (nu ^ k * (m * x ^ k) ^ i) := by
  have e : i + (k - 1 - i) + 1 = k := by omega
  have e3 : i * k = k * i := by ring
  change (a + (((i + (k - 1 - i) + 1 : ℕ)) : ℝ) * b) *
      (m ^ i * nu ^ (i + (k - 1 - i) + 1) * x ^ (i * (i + (k - 1 - i) + 1)))
      = (a + (k : ℝ) * b) * (nu ^ k * (m * x ^ k) ^ i)
  rw [e, e3, mul_pow, ← pow_mul]
  ring

-- Diagonal (range) sums on the D side.
theorem Drow_value (a b m nu x : ℝ) (k : ℕ)
    (hf : ∀ i : Fin k, ((fun p : ℕ × ℕ => (a + (((p.1 + p.2 + 1 : ℕ)) : ℝ) * b) *
      (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1)))) ∘ diagEquiv.symm) ⟨k, i⟩
        = (a + (k : ℝ) * b) * (nu ^ k * (m * x ^ k) ^ (i.val))) :
    (∑' i : Fin k, ((fun p : ℕ × ℕ => (a + (((p.1 + p.2 + 1 : ℕ)) : ℝ) * b) *
      (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1)))) ∘ diagEquiv.symm) ⟨k, i⟩)
      = (a + (k : ℝ) * b) * (nu ^ k * ∑ i ∈ range k, (m * x ^ k) ^ i) := by
  have h1 : (∑' i : Fin k, ((fun p : ℕ × ℕ => (a + (((p.1 + p.2 + 1 : ℕ)) : ℝ) * b) *
      (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1)))) ∘ diagEquiv.symm) ⟨k, i⟩)
      = ∑ i ∈ range k, (a + (k : ℝ) * b) * (nu ^ k * (m * x ^ k) ^ i) := by
    rw [tsum_fintype]
    apply Finset.sum_bij (fun a _ => a.val)
    · intro a _
      exact Finset.mem_range.mpr a.isLt
    · intro a₁ _ a₂ _ h12
      exact Fin.ext h12
    · intro b hb
      exact ⟨⟨b, Finset.mem_range.mp hb⟩, Finset.mem_univ _, rfl⟩
    · intro a _
      exact hf a
  rw [h1, ← Finset.mul_sum]
  congr 1
  rw [← Finset.mul_sum]

-- Second-series terms are m times the weighted row sums.
theorem hsec_val (m nu x : ℝ) (k : ℕ) (hr : ‖nu * x ^ k‖ < 1) :
    (m * nu * x ^ k) ^ (k + 1) / (1 - nu * x ^ k) ^ 2
      = m * (∑' j : ℕ, ((j : ℝ) + 1) *
        (m ^ k * nu ^ (k + j + 1) * x ^ (k * (k + j + 1)))) := by
  rw [Grow_weighted_tsum m nu x k hr, second_num_factor]
  ring

-- Pointwise identity: leftTerm = firstTerm + (w * D - w * Q).
theorem point_ident (a b m nu x : ℝ) (k : ℕ)
    (h1mt : (1 : ℝ) - m * x ^ k ≠ 0) (h1ms : (1 : ℝ) - nu * x ^ k ≠ 0)
    (ht1 : m * x ^ k ≠ 1) :
    (a + (k : ℝ) * b) * nu ^ k / (1 - m * x ^ k)
      = ((a + (k : ℝ) * b) * (1 - m * nu * x ^ (2 * k)) * (m * nu * x ^ k) ^ k) /
          ((1 - m * x ^ k) * (1 - nu * x ^ k))
        + ((a + (k : ℝ) * b) * (nu ^ k * ∑ i ∈ range k, (m * x ^ k) ^ i)
          - (a + (k : ℝ) * b) *
            ((m ^ k * nu ^ (k + 1) * x ^ (k * (k + 1))) / (1 - nu * x ^ k))) := by
  have hgeom : ∑ i ∈ range k, (m * x ^ k) ^ i = ((m * x ^ k) ^ k - 1) / ((m * x ^ k) - 1) :=
    geom_sum_eq ht1 k
  have hQnum : m ^ k * nu ^ (k + 1) * x ^ (k * (k + 1))
      = nu ^ k * (m * x ^ k) ^ k * (nu * x ^ k) := by
    rw [mul_pow, ← pow_mul]; ring
  rw [hgeom, hQnum, first_alg_tkq m nu x k, first_alg_ts m nu x k]
  have hmt : (m : ℝ) * x ^ k - 1 ≠ 0 := sub_ne_zero.mpr ht1
  have h1ms' : (1 : ℝ) - x ^ k * nu ≠ 0 := by
    have h := h1ms
    rwa [mul_comm nu (x ^ k)] at h
  field_simp [h1mt, h1ms, h1ms', hmt]
  ring

-- Full statement with explicit series (no local lets).
theorem entry17_aux (a b m nu x : ℝ)
    (hx : |x| ≤ 1) (hnu : |nu| < 1)
    (hboundary : |x| = 1 → |m * nu| < 1)
    (hm : m ≠ 0)
    (hmx : ∀ k : ℕ, 1 - m * x ^ k ≠ 0) :
    (∀ k : ℕ, 1 - nu * x ^ k ≠ 0) ∧
      Summable (fun k : ℕ => (a + (k : ℝ) * b) * nu ^ k / (1 - m * x ^ k)) ∧
      Summable (fun k : ℕ => ((a + (k : ℝ) * b) * (1 - m * nu * x ^ (2 * k)) *
        (m * nu * x ^ k) ^ k) / ((1 - m * x ^ k) * (1 - nu * x ^ k))) ∧
      Summable (fun k : ℕ => (m * nu * x ^ k) ^ (k + 1) / (1 - nu * x ^ k) ^ 2) ∧
      (∑' k : ℕ, ((a + (k : ℝ) * b) * nu ^ k / (1 - m * x ^ k)))
        = (∑' k : ℕ, (((a + (k : ℝ) * b) * (1 - m * nu * x ^ (2 * k)) *
          (m * nu * x ^ k) ^ k) / ((1 - m * x ^ k) * (1 - nu * x ^ k))))
          + b / m * ∑' k : ℕ, ((m * nu * x ^ k) ^ (k + 1) / (1 - nu * x ^ k) ^ 2) := by
  have hnu_ne : ∀ k : ℕ, 1 - nu * x ^ k ≠ 0 := fun k => nu_ne_aux nu x hx hnu k
  have hr : ∀ k : ℕ, ‖nu * x ^ k‖ < 1 := fun k => row_norm_aux nu x hx hnu k
  have hLeft := left_summable a b m nu x hx hnu hmx
  have hW1 := W1_summable a b m nu x hx hnu hboundary
  have hW2 := W2_summable a b m nu x hx hnu hboundary
  have hGj := Gj_summable m nu x hx hnu hboundary
  have hWQ : Summable fun k : ℕ => (a + (k : ℝ) * b) *
      ((m ^ k * nu ^ (k + 1) * x ^ (k * (k + 1))) / (1 - nu * x ^ k)) := by
    have hS : Summable ((fun p : ℕ × ℕ => (a + (p.1 : ℝ) * b) *
        (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1)))) ∘
        ⇑(Equiv.sigmaEquivProd ℕ ℕ)) :=
      ((Equiv.sigmaEquivProd ℕ ℕ).summable_iff (f := fun p : ℕ × ℕ => (a + (p.1 : ℝ) * b) *
        (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1))))).mpr hW1
    have hsig := hS.sigma
    apply hsig.congr
    intro k
    simp only [Function.comp_apply, Equiv.sigmaEquivProd_apply]
    exact Qrow_value a b m nu x k (hr k)
  have hW2d : Summable ((fun p : ℕ × ℕ => (a + (((p.1 + p.2 + 1 : ℕ)) : ℝ) * b) *
      (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1)))) ∘ diagEquiv.symm) :=
    (diagEquiv.symm.summable_iff (f := fun p : ℕ × ℕ => (a + (((p.1 + p.2 + 1 : ℕ)) : ℝ) * b) *
      (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1))))).mpr hW2
  have hWD : Summable fun k : ℕ => (a + (k : ℝ) * b) *
      (nu ^ k * ∑ i ∈ range k, (m * x ^ k) ^ i) := by
    have hsig : Summable fun k : ℕ => ∑' i : Fin k,
        ((fun p : ℕ × ℕ => (a + (((p.1 + p.2 + 1 : ℕ)) : ℝ) * b) *
          (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1)))) ∘
          diagEquiv.symm) ⟨k, i⟩ := hW2d.sigma
    apply hsig.congr
    intro k
    apply Drow_value a b m nu x k
    intro i
    obtain ⟨i', h⟩ := i
    exact Dterm_value a b m nu x k i' h
  have hSec : Summable fun k : ℕ => (m * nu * x ^ k) ^ (k + 1) / (1 - nu * x ^ k) ^ 2 := by
    have hS : Summable ((fun p : ℕ × ℕ => ((p.2 : ℝ) + 1) *
        (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1)))) ∘
        ⇑(Equiv.sigmaEquivProd ℕ ℕ)) :=
      ((Equiv.sigmaEquivProd ℕ ℕ).summable_iff (f := fun p : ℕ × ℕ => ((p.2 : ℝ) + 1) *
        (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1))))).mpr hGj
    have hsig := hS.sigma
    have hval : (fun k : ℕ => (m * nu * x ^ k) ^ (k + 1) / (1 - nu * x ^ k) ^ 2)
        = (fun k : ℕ => m * (∑' j : ℕ, ((j : ℝ) + 1) *
          (m ^ k * nu ^ (k + j + 1) * x ^ (k * (k + j + 1))))) := by
      funext k
      exact hsec_val m nu x k (hr k)
    rw [hval]
    exact hsig.mul_left m
  have hpoint : ∀ k : ℕ, (a + (k : ℝ) * b) * nu ^ k / (1 - m * x ^ k)
      = ((a + (k : ℝ) * b) * (1 - m * nu * x ^ (2 * k)) * (m * nu * x ^ k) ^ k) /
          ((1 - m * x ^ k) * (1 - nu * x ^ k))
        + ((a + (k : ℝ) * b) * (nu ^ k * ∑ i ∈ range k, (m * x ^ k) ^ i)
          - (a + (k : ℝ) * b) *
            ((m ^ k * nu ^ (k + 1) * x ^ (k * (k + 1))) / (1 - nu * x ^ k))) := by
    intro k
    exact point_ident a b m nu x k (hmx k) (hnu_ne k)
      (fun h => hmx k (by rw [h, sub_self]))
  have hFirst : Summable fun k : ℕ => ((a + (k : ℝ) * b) *
      (1 - m * nu * x ^ (2 * k)) * (m * nu * x ^ k) ^ k) /
        ((1 - m * x ^ k) * (1 - nu * x ^ k)) := by
    have hsub := hWD.sub hWQ
    have hmain := hLeft.sub hsub
    have hcongr : ∀ k : ℕ, ((a + (k : ℝ) * b) * nu ^ k / (1 - m * x ^ k)
        - ((a + (k : ℝ) * b) * (nu ^ k * ∑ i ∈ range k, (m * x ^ k) ^ i)
          - (a + (k : ℝ) * b) *
            ((m ^ k * nu ^ (k + 1) * x ^ (k * (k + 1))) / (1 - nu * x ^ k))))
        = ((a + (k : ℝ) * b) * (1 - m * nu * x ^ (2 * k)) * (m * nu * x ^ k) ^ k) /
          ((1 - m * x ^ k) * (1 - nu * x ^ k)) := fun k => by
      rw [hpoint k]; ring
    exact hmain.congr hcongr
  have hT1 : (∑' k : ℕ, (a + (k : ℝ) * b) *
      ((m ^ k * nu ^ (k + 1) * x ^ (k * (k + 1))) / (1 - nu * x ^ k)))
      = ∑' p : ℕ × ℕ, (a + (p.1 : ℝ) * b) *
        (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1))) :=
    (tsum_congr (fun k => (Qrow_value a b m nu x k (hr k)).symm)).trans
      hW1.tsum_prod.symm
  have hT2 : (∑' k : ℕ, (a + (k : ℝ) * b) *
      (nu ^ k * ∑ i ∈ range k, (m * x ^ k) ^ i))
      = ∑' p : ℕ × ℕ, (a + (((p.1 + p.2 + 1 : ℕ)) : ℝ) * b) *
        (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1))) := by
    have hstep : (∑' k : ℕ, (a + (k : ℝ) * b) *
        (nu ^ k * ∑ i ∈ range k, (m * x ^ k) ^ i))
        = ∑' k : ℕ, ∑' i : Fin k, ((fun p : ℕ × ℕ => (a + (((p.1 + p.2 + 1 : ℕ)) : ℝ) * b) *
          (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1)))) ∘
          diagEquiv.symm) ⟨k, i⟩ :=
      tsum_congr (fun k => (Drow_value a b m nu x k (fun i => by
        obtain ⟨i', h⟩ := i
        exact Dterm_value a b m nu x k i' h)).symm)
    have hsig := hW2d.tsum_sigma
    have hteq := diagEquiv.symm.tsum_eq (fun p : ℕ × ℕ => (a + (((p.1 + p.2 + 1 : ℕ)) : ℝ) * b) *
      (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1))))
    exact hstep.trans hsig.symm |>.trans hteq
  have hS2 : (∑' k : ℕ, (m * nu * x ^ k) ^ (k + 1) / (1 - nu * x ^ k) ^ 2)
      = m * ∑' p : ℕ × ℕ, ((p.2 : ℝ) + 1) *
        (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1))) := by
    have hstep : (∑' k : ℕ, (m * nu * x ^ k) ^ (k + 1) / (1 - nu * x ^ k) ^ 2)
        = ∑' k : ℕ, m * (∑' j : ℕ, ((j : ℝ) + 1) *
          (m ^ k * nu ^ (k + j + 1) * x ^ (k * (k + j + 1)))) :=
      tsum_congr (fun k => hsec_val m nu x k (hr k))
    have hmul : (∑' k : ℕ, m * (∑' j : ℕ, ((j : ℝ) + 1) *
        (m ^ k * nu ^ (k + j + 1) * x ^ (k * (k + j + 1)))))
        = m * ∑' k : ℕ, (∑' j : ℕ, ((j : ℝ) + 1) *
          (m ^ k * nu ^ (k + j + 1) * x ^ (k * (k + j + 1)))) :=
      tsum_mul_left
    exact hstep.trans hmul |>.trans (congrArg (m * ·) hGj.tsum_prod.symm)
  have hDiff : (∑' p : ℕ × ℕ, (a + (((p.1 + p.2 + 1 : ℕ)) : ℝ) * b) *
      (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1))))
      - (∑' p : ℕ × ℕ, (a + (p.1 : ℝ) * b) *
        (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1))))
      = b * ∑' p : ℕ × ℕ, ((p.2 : ℝ) + 1) *
        (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1))) := by
    have hsub := hW2.tsum_sub hW1
    have hfun : (fun p : ℕ × ℕ => (a + (((p.1 + p.2 + 1 : ℕ)) : ℝ) * b) *
        (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1)))
        - (a + (p.1 : ℝ) * b) *
          (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1))))
        = (fun p : ℕ × ℕ => b * (((p.2 : ℝ) + 1) *
          (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1))))) := by
      funext p; push_cast; ring
    have hval : (∑' p : ℕ × ℕ, ((a + (((p.1 + p.2 + 1 : ℕ)) : ℝ) * b) *
        (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1)))
        - (a + (p.1 : ℝ) * b) *
          (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1)))))
        = b * ∑' p : ℕ × ℕ, ((p.2 : ℝ) + 1) *
          (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1))) := by
      rw [hfun, tsum_mul_left]
    exact hsub.symm.trans hval
  have hval : (∑' k : ℕ, ((a + (k : ℝ) * b) * nu ^ k / (1 - m * x ^ k)))
      = (∑' k : ℕ, (((a + (k : ℝ) * b) * (1 - m * nu * x ^ (2 * k)) *
        (m * nu * x ^ k) ^ k) / ((1 - m * x ^ k) * (1 - nu * x ^ k))))
        + ((∑' k : ℕ, (a + (k : ℝ) * b) *
          (nu ^ k * ∑ i ∈ range k, (m * x ^ k) ^ i))
          - (∑' k : ℕ, (a + (k : ℝ) * b) *
            ((m ^ k * nu ^ (k + 1) * x ^ (k * (k + 1))) / (1 - nu * x ^ k)))) := by
    have htsum : (∑' k : ℕ, ((a + (k : ℝ) * b) * nu ^ k / (1 - m * x ^ k)
        - ((a + (k : ℝ) * b) * (nu ^ k * ∑ i ∈ range k, (m * x ^ k) ^ i)
          - (a + (k : ℝ) * b) *
            ((m ^ k * nu ^ (k + 1) * x ^ (k * (k + 1))) / (1 - nu * x ^ k)))))
        = (∑' k : ℕ, ((a + (k : ℝ) * b) * nu ^ k / (1 - m * x ^ k)))
          - (∑' k : ℕ, ((a + (k : ℝ) * b) * (nu ^ k * ∑ i ∈ range k, (m * x ^ k) ^ i)
            - (a + (k : ℝ) * b) *
              ((m ^ k * nu ^ (k + 1) * x ^ (k * (k + 1))) / (1 - nu * x ^ k)))) :=
      hLeft.tsum_sub (hWD.sub hWQ)
    have htsum2 : (∑' k : ℕ, ((a + (k : ℝ) * b) * (nu ^ k * ∑ i ∈ range k, (m * x ^ k) ^ i)
        - (a + (k : ℝ) * b) *
          ((m ^ k * nu ^ (k + 1) * x ^ (k * (k + 1))) / (1 - nu * x ^ k))))
        = (∑' k : ℕ, (a + (k : ℝ) * b) * (nu ^ k * ∑ i ∈ range k, (m * x ^ k) ^ i))
          - (∑' k : ℕ, (a + (k : ℝ) * b) *
            ((m ^ k * nu ^ (k + 1) * x ^ (k * (k + 1))) / (1 - nu * x ^ k))) :=
      hWD.tsum_sub hWQ
    have hcongr : (∑' k : ℕ, ((a + (k : ℝ) * b) * nu ^ k / (1 - m * x ^ k)
        - ((a + (k : ℝ) * b) * (nu ^ k * ∑ i ∈ range k, (m * x ^ k) ^ i)
          - (a + (k : ℝ) * b) *
            ((m ^ k * nu ^ (k + 1) * x ^ (k * (k + 1))) / (1 - nu * x ^ k)))))
        = (∑' k : ℕ, (((a + (k : ℝ) * b) * (1 - m * nu * x ^ (2 * k)) *
          (m * nu * x ^ k) ^ k) / ((1 - m * x ^ k) * (1 - nu * x ^ k)))) :=
      tsum_congr (fun k => by rw [hpoint k]; ring)
    have hL : (∑' k : ℕ, ((a + (k : ℝ) * b) * nu ^ k / (1 - m * x ^ k)))
        - (∑' k : ℕ, ((a + (k : ℝ) * b) * (nu ^ k * ∑ i ∈ range k, (m * x ^ k) ^ i)
          - (a + (k : ℝ) * b) *
            ((m ^ k * nu ^ (k + 1) * x ^ (k * (k + 1))) / (1 - nu * x ^ k))))
        = (∑' k : ℕ, (((a + (k : ℝ) * b) * (1 - m * nu * x ^ (2 * k)) *
          (m * nu * x ^ k) ^ k) / ((1 - m * x ^ k) * (1 - nu * x ^ k)))) :=
      htsum.symm.trans hcongr
    rw [htsum2] at hL
    exact sub_eq_iff_eq_add.mp hL
  have hfin : b / m * (∑' k : ℕ, (m * nu * x ^ k) ^ (k + 1) / (1 - nu * x ^ k) ^ 2)
      = b * ∑' p : ℕ × ℕ, ((p.2 : ℝ) + 1) *
        (m ^ p.1 * nu ^ (p.1 + p.2 + 1) * x ^ (p.1 * (p.1 + p.2 + 1))) := by
    rw [hS2, ← mul_assoc, div_mul_cancel₀ _ hm]
  refine ⟨hnu_ne, hLeft, hFirst, hSec, ?_⟩
  rw [hval, hT2, hT1, hDiff, hfin]


section

/-!
# Ramanujan's Notebooks, Part I, Chapter 6

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

namespace Ramanujan.Part1Ch6

namespace Entry17Stirlingcoeffs

open scoped BigOperators

open Filter Finset Topology

noncomputable section

/-- Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 6.

Proves `Wanted` entry `ramanujan_part1_ch6_entry17_stirlingcoeffs`.
-/
theorem ramanujan_part1_ch6_entry17_stirlingcoeffs
    (a b m nu x : ℝ)
    (hx : |x| ≤ 1) (hnu : |nu| < 1)
    (hboundary : |x| = 1 → |m * nu| < 1)
    (hm : m ≠ 0)
    (hmx : ∀ k : ℕ, 1 - m * x ^ k ≠ 0) :
    let leftTerm := fun k : ℕ =>
      (a + (k : ℝ) * b) * nu ^ k / (1 - m * x ^ k)
    let firstTerm := fun k : ℕ =>
      ((a + (k : ℝ) * b) * (1 - m * nu * x ^ (2 * k)) *
          (m * nu * x ^ k) ^ k) /
        ((1 - m * x ^ k) * (1 - nu * x ^ k))
    let secondTerm := fun k : ℕ =>
      (m * nu * x ^ k) ^ (k + 1) / (1 - nu * x ^ k) ^ 2
    (∀ k : ℕ, 1 - nu * x ^ k ≠ 0) ∧
      Summable leftTerm ∧ Summable firstTerm ∧ Summable secondTerm ∧
      ∑' k, leftTerm k =
        ∑' k, firstTerm k + b / m * ∑' k, secondTerm k := by
  exact entry17_aux a b m nu x hx hnu hboundary hm hmx

end
end Entry17Stirlingcoeffs
end Ramanujan.Part1Ch6
end
