import Mathlib
import sympy.Basic
import Def.v1.Atlas.ProjectionTheory.code.MultConvProjection
open Finset Complex Nat BigOperators MultiplicativeConvolution


namespace MultiplicativeConvolution

/--
[sum_comm4](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MultConvProjection.lean)
-/
@[path]
lemma sum_comm4
  {N q : ℕ}
  [NeZero q]
-- given
  (h : ZMod q → ZMod q → ℕ → ℕ → ℂ) :
-- imply
  (∑ b : ZMod q, ∑ c : ZMod q, ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, h b c n m) = (∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, ∑ b : ZMod q, ∑ c : ZMod q, h b c n m) := by
-- proof
  trans (∑ b : ZMod q, ∑ n ∈ Finset.range N, ∑ c : ZMod q, ∑ m ∈ Finset.range N, h b c n m)
  · apply Finset.sum_congr rfl; intro b _; exact Finset.sum_comm
  trans (∑ n ∈ Finset.range N, ∑ b : ZMod q, ∑ c : ZMod q, ∑ m ∈ Finset.range N, h b c n m)
  · exact Finset.sum_comm
  apply Finset.sum_congr rfl; intro n _
  trans (∑ b : ZMod q, ∑ m ∈ Finset.range N, ∑ c : ZMod q, h b c n m)
  · apply Finset.sum_congr rfl; intro b _; exact Finset.sum_comm
  trans (∑ m ∈ Finset.range N, ∑ b : ZMod q, ∑ c : ZMod q, h b c n m)
  · exact Finset.sum_comm
  · rfl

end MultiplicativeConvolution

namespace MultiplicativeConvolution

/--
[mulConv_ZMod_eq_double_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MultConvProjection.lean)
-/
@[path]
lemma mulConv_ZMod_eq_double_sum
  {N q : ℕ}
  [NeZero q]
  {f g : ℕ → ℂ}
  {a : ZMod q} :
-- imply
  mulConv_ZMod q (modProjection_arith N q f) (modProjection_arith N q g) a = ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, if ((n : ℕ) : ZMod q) * ((m : ℕ) : ZMod q) = a then f n * g m else 0 := by
-- proof
  simp only [mulConv_ZMod, modProjection_arith]
  have prod_expand : ∀ b c : ZMod q,
    (∑ n ∈ Finset.range N, if ((n : ℕ) : ZMod q) = b then f n else 0) *
    (∑ m ∈ Finset.range N, if ((m : ℕ) : ZMod q) = c then g m else 0) =
    ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
      (if ((n : ℕ) : ZMod q) = b then f n else 0) *
      (if ((m : ℕ) : ZMod q) = c then g m else 0) := by
    intro b c; rw [Finset.sum_mul]; congr 1; ext n; rw [Finset.mul_sum]
  have push_if : ∀ b c : ZMod q,
    (if b * c = a then
      (∑ n ∈ Finset.range N, if ((n : ℕ) : ZMod q) = b then f n else 0) *
      (∑ m ∈ Finset.range N, if ((m : ℕ) : ZMod q) = c then g m else 0)
    else 0) =
    ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N,
      (if ((n : ℕ) : ZMod q) = b ∧ ((m : ℕ) : ZMod q) = c ∧ b * c = a
        then f n * g m else 0) := by
    intro b c
    rw [prod_expand]
    by_cases hbc : b * c = a
    · simp only [hbc, ite_true]
      apply Finset.sum_congr rfl; intro n _
      apply Finset.sum_congr rfl; intro m _
      by_cases hb : ((n : ℕ) : ZMod q) = b <;> by_cases hc : ((m : ℕ) : ZMod q) = c <;>
        simp [hb, hc, hbc]
    · simp only [hbc, ite_false, and_false, Finset.sum_const_zero]
  simp_rw [push_if]
  rw [sum_comm4]
  apply Finset.sum_congr rfl; intro n _
  apply Finset.sum_congr rfl; intro m _
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2; ext y; arg 2; ext x
    rw [show (if ((n : ℕ) : ZMod q) = x ∧ ((m : ℕ) : ZMod q) = y ∧ x * y = a
      then f n * g m else 0) =
      (if ((n : ℕ) : ZMod q) = x then
        (if ((m : ℕ) : ZMod q) = y ∧ x * y = a then f n * g m else 0)
      else 0) from by split_ifs <;> tauto]
  simp_rw [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  conv_lhs =>
    arg 2; ext y
    rw [show (if ((m : ℕ) : ZMod q) = y ∧ ((n : ℕ) : ZMod q) * y = a
      then f n * g m else 0) =
      (if ((m : ℕ) : ZMod q) = y then
        (if ((n : ℕ) : ZMod q) * y = a then f n * g m else 0)
      else 0) from by split_ifs <;> tauto]
  simp_rw [Finset.sum_ite_eq, Finset.mem_univ, ite_true]

end MultiplicativeConvolution

namespace MultiplicativeConvolution

/--
[sum_product_eq_sum_divisorsAntidiagonal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MultConvProjection.lean)
-/
@[path]
lemma sum_product_eq_sum_divisorsAntidiagonal
  {N : ℕ}
  {f g : ℕ → ℂ}
  {n : ℕ}
-- given
  (hf : ∀ n, N ≤ n → f n = 0)
  (hg : ∀ n, N ≤ n → g n = 0)
  (hf0 : f 0 = 0)
  (hg0 : g 0 = 0)
  (hn : n < N * N) :
-- imply
  (∑ x ∈ (Finset.range N ×ˢ Finset.range N).filter (fun x => x.1 * x.2 = n), f x.1 * g x.2) = ∑ x ∈ Nat.divisorsAntidiagonal n, f x.1 * g x.2 := by
-- proof
  by_cases hn0 : n = 0
  · subst hn0
    simp only [Nat.divisorsAntidiagonal_zero, Finset.sum_empty]
    apply Finset.sum_eq_zero
    intro ⟨d1, d2⟩ hx
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hx
    have hprod : d1 * d2 = 0 := hx.2
    obtain hd1 | hd1 := Nat.eq_zero_or_pos d1
    · simp [hd1, hf0]
    · have hd2 : d2 = 0 := (Nat.mul_eq_zero.mp hprod).resolve_left (Nat.pos_iff_ne_zero.mp hd1)
      simp [hd2, hg0]
  · apply Finset.sum_subset
    · intro ⟨d1, d2⟩ hx
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hx
      rw [Nat.mem_divisorsAntidiagonal]
      exact ⟨hx.2, hn0⟩
    · intro ⟨d1, d2⟩ hd hd_not
      rw [Nat.mem_divisorsAntidiagonal] at hd
      have h : ¬(d1 < N ∧ d2 < N) := by
        intro ⟨h1, h2⟩
        apply hd_not
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
        exact ⟨⟨h1, h2⟩, hd.1⟩
      by_cases hd1 : d1 < N
      · have hd2 : N ≤ d2 := by
        by_contra hlt; push Not at hlt; exact h ⟨hd1, hlt⟩
        simp [hg d2 hd2]
      · simp [hf d1 (by omega)]

end MultiplicativeConvolution

namespace MultiplicativeConvolution

/--
[modProjection_mulConv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MultConvProjection.lean)
-/
@[path]
lemma modProjection_mulConv
  {N q : ℕ}
  [NeZero q]
  {f g : ℕ → ℂ}
  {a : ZMod q}
-- given
  (hf : ∀ n, N ≤ n → f n = 0)
  (hg : ∀ n, N ≤ n → g n = 0)
  (hf0 : f 0 = 0)
  (hg0 : g 0 = 0) :
-- imply
  modProjection_arith (N * N) q (mulConv f g) a = mulConv_ZMod q (modProjection_arith N q f) (modProjection_arith N q g) a := by
-- proof
  rw [mulConv_ZMod_eq_double_sum]
  simp only [modProjection_arith, mulConv]
  simp_rw [show ∀ (n m : ℕ), ((n : ℕ) : ZMod q) * ((m : ℕ) : ZMod q) = ((n * m : ℕ) : ZMod q)
    from by intros; push_cast; ring]
  rw [← Finset.sum_product']
  have hmaps : ∀ x ∈ (Finset.range N) ×ˢ (Finset.range N),
    x.1 * x.2 ∈ Finset.range (N * N) := by
    intro ⟨d1, d2⟩ hx
    simp only [Finset.mem_product, Finset.mem_range] at hx ⊢
    exact Nat.mul_lt_mul'' hx.1 hx.2
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_congr rfl; intro n hn
  simp only [Finset.mem_range] at hn
  have h_ind : ∀ x ∈ (Finset.range N ×ˢ Finset.range N).filter (fun x => x.1 * x.2 = n),
    (if ((x.1 * x.2 : ℕ) : ZMod q) = a then f x.1 * g x.2 else 0) =
    (if ((n : ℕ) : ZMod q) = a then f x.1 * g x.2 else 0) := by
    intro x hx; simp only [Finset.mem_filter] at hx; rw [hx.2]
  rw [Finset.sum_congr rfl h_ind]
  split_ifs with ha
  ·
    exact (sum_product_eq_sum_divisorsAntidiagonal N f g hf hg hf0 hg0 n hn).symm
  ·
    simp

end MultiplicativeConvolution

namespace MultiplicativeConvolution

/--
[modProjection_mulConv_arithFun](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MultConvProjection.lean)
-/
@[path]
lemma modProjection_mulConv_arithFun
  {N q : ℕ}
  [NeZero q]
  {f g : ArithmeticFunction ℂ}
  {a : ZMod q}
-- given
  (hf : ∀ n, N ≤ n → f n = 0)
  (hg : ∀ n, N ≤ n → g n = 0) :
-- imply
  modProjection_arith (N * N) q (fun n => (f * g) n) a = mulConv_ZMod q (modProjection_arith N q f) (modProjection_arith N q g) a := by
-- proof
  have key := modProjection_mulConv N q (fun n => f n) (fun n => g n) hf hg
    f.map_zero g.map_zero a
  simp only [show (fun n => (f * g) n) = mulConv (fun n => f n) (fun n => g n) from by
    ext n; rw [← mulConv_eq_arithmeticFunction_mul]] at key ⊢
  exact key

end MultiplicativeConvolution

namespace MultiplicativeConvolution

/--
[modProjection_mulConv_arithFun'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MultConvProjection.lean)
-/
@[path]
lemma modProjection_mulConv_arithFun'
  {N q : ℕ}
  [NeZero q]
  {f g : ℕ → ℂ}
-- given
  (hf : ∀ n, N ≤ n → f n = 0)
  (hg : ∀ n, N ≤ n → g n = 0)
  (hf0 : f 0 = 0)
  (hg0 : g 0 = 0) :
-- imply
  modProjection_arith (N * N) q (mulConv f g) = mulConv_ZMod q (modProjection_arith N q f) (modProjection_arith N q g) := by
-- proof
  funext a
  exact modProjection_mulConv N q f g hf hg hf0 hg0 a

end MultiplicativeConvolution

namespace MultiplicativeConvolution

/--
[zeroAt0_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MultConvProjection.lean)
-/
@[path]
lemma zeroAt0_zero
  {f : ℕ → ℂ} :
-- imply
  zeroAt0 f 0 = 0 :=
-- proof
  if_pos rfl

end MultiplicativeConvolution

namespace MultiplicativeConvolution

/--
[zeroAt0_support](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MultConvProjection.lean)
-/
@[path]
lemma zeroAt0_support
  {f : ℕ → ℂ}
  {N : ℕ}
-- given
  (hf : ∀ n, N ≤ n → f n = 0) :
-- imply
  ∀ n, N ≤ n → zeroAt0 f n = 0 := by
-- proof
  intro n hn
  unfold zeroAt0
  split
  · rfl
  · exact hf n hn

end MultiplicativeConvolution

namespace MultiplicativeConvolution

/--
[modProjection_pos_eq_arith_zeroAt0](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MultConvProjection.lean)
-/
@[path]
lemma modProjection_pos_eq_arith_zeroAt0
  {N q : ℕ}
  [NeZero q]
  {f : ℕ → ℂ}
  {a : ZMod q} :
-- imply
  modProjection_pos N q f a = modProjection_arith N q (zeroAt0 f) a := by
-- proof
  simp only [modProjection_pos, modProjection_arith, zeroAt0]
  conv_rhs =>
    arg 2; ext n
    rw [show (if ((n : ℕ) : ZMod q) = a then if n = 0 then 0 else f n else 0) =
      (if n ≠ 0 then (if ((n : ℕ) : ZMod q) = a then f n else 0) else 0) from by
        split_ifs <;> simp_all]
  rw [Finset.sum_filter]

end MultiplicativeConvolution

namespace MultiplicativeConvolution

/--
[mulConv_pos_eq_zeroAt0](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MultConvProjection.lean)
-/
@[path]
lemma mulConv_pos_eq_zeroAt0
  {f g : ℕ → ℂ}
  {n : ℕ}
-- given
  (hn : n ≠ 0) :
-- imply
  mulConv f g n = mulConv (zeroAt0 f) (zeroAt0 g) n := by
-- proof
  simp only [mulConv, zeroAt0]
  apply Finset.sum_congr rfl
  intro ⟨d1, d2⟩ hd
  rw [Nat.mem_divisorsAntidiagonal] at hd
  have hd1 : d1 ≠ 0 := by intro h; rw [h, zero_mul] at hd; exact hn hd.1.symm
  have hd2 : d2 ≠ 0 := by intro h; rw [h, mul_zero] at hd; exact hn hd.1.symm
  simp [hd1, hd2]

end MultiplicativeConvolution

namespace MultiplicativeConvolution

/--
[modProjection_mulConv_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/MultConvProjection.lean)
-/
@[path]
lemma modProjection_mulConv_pos
  {N q : ℕ}
  [NeZero q]
  {f g : ℕ → ℂ}
-- given
  (hf : ∀ n, N ≤ n → f n = 0)
  (hg : ∀ n, N ≤ n → g n = 0) :
-- imply
  modProjection_pos (N * N) q (mulConv f g) = mulConv_ZMod q (modProjection_pos N q f) (modProjection_pos N q g) := by
-- proof
  have lhs_eq : ∀ a, modProjection_pos (N * N) q (mulConv f g) a =
    modProjection_arith (N * N) q (mulConv (zeroAt0 f) (zeroAt0 g)) a := by
    intro a
    rw [modProjection_pos_eq_arith_zeroAt0]
    congr 1; funext n
    simp only [zeroAt0]; split_ifs with h
    · subst h; simp [mulConv, Nat.divisorsAntidiagonal_zero]
    · exact mulConv_pos_eq_zeroAt0 f g n h
  have rhs_eq : ∀ a, mulConv_ZMod q (modProjection_pos N q f) (modProjection_pos N q g) a =
    mulConv_ZMod q (modProjection_arith N q (zeroAt0 f))
      (modProjection_arith N q (zeroAt0 g)) a := by
    intro a
    simp only [mulConv_ZMod]
    congr 1; ext b; congr 1; ext c
    split_ifs with h
    · congr 1
      · exact modProjection_pos_eq_arith_zeroAt0 N q f b
      · exact modProjection_pos_eq_arith_zeroAt0 N q g c
    · rfl
  funext a
  rw [lhs_eq, rhs_eq]
  exact congr_fun (modProjection_mulConv_arithFun' N q (zeroAt0 f) (zeroAt0 g)
    (zeroAt0_support f N hf) (zeroAt0_support g N hg)
    (zeroAt0_zero f) (zeroAt0_zero g)) a
end MultiplicativeConvolution



-- created on 2026-10-23
