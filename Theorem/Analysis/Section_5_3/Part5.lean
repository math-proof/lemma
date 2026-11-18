module

public import Mathlib
public import Theorem.Analysis.Section_5_2.Part2
public import Mathlib.Algebra.Group.MinimalAxioms
public import Theorem.Analysis.Section_5_1.Part5
public import Instance.Analysis.Section_5_3.Part3

public section
/-!
# Analysis I, Section 5.3: The construction of the real numbers

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Notion of a formal limit of a Cauchy sequence.
- Construction of a real number type `Chapter5.Real`.
- Basic arithmetic operations and properties.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/


namespace Chapter5

private theorem ofNatFun_n₀ (a : ℕ → ℚ) : (Sequence.ofNatFun a).n₀ = 0 := rfl

private theorem from_n₀ (a : Sequence) (n₁ : ℤ) :
    (a.from n₁).n₀ = max a.n₀ n₁ := rfl

private theorem from_seq (a : Sequence) {n₁ n : ℤ} (h : n ≥ max a.n₀ n₁) :
    (a.from n₁).seq n = a.seq n := by
  dsimp [Sequence.from, Sequence.mk']
  split
  · rfl
  · omega

private theorem ofNatFun_seq_of_nonneg (a : ℕ → ℚ) {n : ℤ} (hn : 0 ≤ n) :
    (Sequence.ofNatFun a).seq n = a n.toNat := by
  simp [Sequence.ofNatFun, hn]

private theorem ofNatFun_mul_seq (a b : ℕ → ℚ) (n : ℤ) :
    (Sequence.ofNatFun (a * b)).seq n =
      (Sequence.ofNatFun a).seq n * (Sequence.ofNatFun b).seq n := by
  by_cases hn : 0 ≤ n <;> simp [Sequence.ofNatFun, Pi.mul_apply, hn]

private theorem from_ofNatFun_n₀_le (a : ℕ → ℚ) (N n : ℤ)
    (hn : n ≥ ((Sequence.ofNatFun a).from N).n₀) : 0 ≤ n ∧ N ≤ n := by
  rw [from_n₀, ofNatFun_n₀] at hn
  constructor <;> omega

private theorem ge_from_n₀ (a : ℕ → ℚ) {N n : ℤ} (hN : N ≤ n) (hn0 : 0 ≤ n) :
    n ≥ max (Sequence.ofNatFun a).n₀ N := by
  rw [ofNatFun_n₀]
  omega

private theorem ofNatFun_bounded_of_isCauchy {b : ℕ → ℚ}
    (hb : (Sequence.ofNatFun b).IsCauchy) :
    ∃ M ≥ (0:ℚ), ∀ n : ℕ, |b n| ≤ M := by
  have hb' := (Sequence.IsCauchy.coe b).mp hb
  obtain ⟨N, hN⟩ := hb' 1 (by norm_num)
  obtain ⟨M₀, hM₀, hfront⟩ := IsBounded.finite (fun i : Fin N ↦ b i)
  refine ⟨max M₀ (|b N| + 1), le_trans hM₀ (le_max_left _ _), ?_⟩
  intro n
  by_cases hn : N ≤ n
  · have hdist := hN n hn N le_rfl
    rw [Section_4_3.dist_eq] at hdist
    have : |b n| ≤ |b N| + 1 :=
      calc
        |b n| = |(b n - b N) + b N| := by simp [sub_add_cancel]
        _ ≤ |b n - b N| + |b N| := abs_add_le _ _
        _ ≤ 1 + |b N| := add_le_add hdist le_rfl
        _ = |b N| + 1 := add_comm _ _
    exact this.trans (le_max_right _ _)
  · have hn' : n < N := Nat.lt_of_not_ge hn
    exact (hfront ⟨n, hn'⟩).trans (le_max_left _ _)

/-- Definition 5.3.4 (Addition of reals) -/
public theorem Real.LIM_add {a b:ℕ → ℚ}
    (ha: (Sequence.ofNatFun a).IsCauchy) (hb: (Sequence.ofNatFun b).IsCauchy) :
    LIM a + LIM b = LIM (a + b) := by
  change Real.add_inst.add (LIM a) (LIM b) = LIM (a + b)
  unfold Real.add_inst
  dsimp only
  rw [LIM_def ha, LIM_def hb, Quotient.liftOn₂_mk]
  have hfun : (CauchySequence.mk' ha : ℕ → ℚ) + (CauchySequence.mk' hb : ℕ → ℚ) = a + b := by
    rw [CauchySequence.coe_coe, CauchySequence.coe_coe]
  rw [hfun]

/-- Proposition 5.3.10 (Product of Cauchy sequences is Cauchy) -/
public theorem Sequence.IsCauchy.mul {a b:ℕ → ℚ}
    (ha: (Sequence.ofNatFun a).IsCauchy) (hb: (Sequence.ofNatFun b).IsCauchy) :
    (Sequence.ofNatFun (a * b)).IsCauchy := by
  obtain ⟨Ma, hMa0, hMa⟩ := ofNatFun_bounded_of_isCauchy ha
  obtain ⟨Mb, hMb0, hMb⟩ := ofNatFun_bounded_of_isCauchy hb
  rw [Sequence.IsCauchy.coe] at ha hb ⊢
  intro ε hε
  have hMa1 : 0 < Ma + 1 := by linarith
  have hMb1 : 0 < Mb + 1 := by linarith
  have h2 : (0:ℚ) < 2 := by norm_num
  obtain ⟨N1, hN1⟩ := ha (ε / (2 * (Mb + 1))) (div_pos hε (mul_pos h2 hMb1))
  obtain ⟨N2, hN2⟩ := hb (ε / (2 * (Ma + 1))) (div_pos hε (mul_pos h2 hMa1))
  refine ⟨max N1 N2, ?_⟩
  intro j hj k hk
  have hN1j : N1 ≤ j := le_trans (le_max_left N1 N2) hj
  have hN1k : N1 ≤ k := le_trans (le_max_left N1 N2) hk
  have hN2j : N2 ≤ j := le_trans (le_max_right N1 N2) hj
  have hN2k : N2 ≤ k := le_trans (le_max_right N1 N2) hk
  have haΔ := hN1 j hN1j k hN1k
  have hbΔ := hN2 j hN2j k hN2k
  rw [Section_4_3.dist_eq] at haΔ hbΔ ⊢
  simp only [Pi.mul_apply]
  have hid : a j * b j - a k * b k = a j * (b j - b k) + (a j - a k) * b k := by ring
  have hle1 : Ma * (ε / (2 * (Ma + 1))) ≤ ε / 2 := by
    have hfrac : Ma / (Ma + 1) ≤ 1 :=
      (div_le_one hMa1).mpr (le_add_of_nonneg_right (by norm_num))
    calc
      Ma * (ε / (2 * (Ma + 1))) = (Ma / (Ma + 1)) * (ε / 2) := by field_simp
      _ ≤ 1 * (ε / 2) :=
        mul_le_mul_of_nonneg_right hfrac (div_nonneg (le_of_lt hε) (by norm_num))
      _ = ε / 2 := one_mul _
  have hle2 : (ε / (2 * (Mb + 1))) * Mb ≤ ε / 2 := by
    have hfrac : Mb / (Mb + 1) ≤ 1 :=
      (div_le_one hMb1).mpr (le_add_of_nonneg_right (by norm_num))
    calc
      (ε / (2 * (Mb + 1))) * Mb = (Mb / (Mb + 1)) * (ε / 2) := by field_simp
      _ ≤ 1 * (ε / 2) :=
        mul_le_mul_of_nonneg_right hfrac (div_nonneg (le_of_lt hε) (by norm_num))
      _ = ε / 2 := one_mul _
  calc
    |a j * b j - a k * b k|
        = |a j * (b j - b k) + (a j - a k) * b k| := by rw [hid]
    _ ≤ |a j * (b j - b k)| + |(a j - a k) * b k| := abs_add_le _ _
    _ = |a j| * |b j - b k| + |a j - a k| * |b k| := by simp [abs_mul]
    _ ≤ Ma * |b j - b k| + |a j - a k| * Mb := by
      gcongr
      · exact hMa j
      · exact hMb k
    _ ≤ Ma * (ε / (2 * (Ma + 1))) + (ε / (2 * (Mb + 1))) * Mb := by
      gcongr
    _ ≤ ε / 2 + ε / 2 := add_le_add hle1 hle2
    _ = ε := add_halves ε

/-- Proposition 5.3.10 (Product of equivalent sequences is equivalent, left) / Exercise 5.3.2. -/
public theorem Sequence.mul_equiv_left {a a':ℕ → ℚ} (b:ℕ → ℚ)
    (hb : (Sequence.ofNatFun b).IsCauchy) (haa': Equiv a a') :
    Equiv (a * b) (a' * b) := by
  intro ε hε
  obtain ⟨M, hM0, hMb⟩ := ofNatFun_bounded_of_isCauchy hb
  by_cases hM : M = 0
  · refine ⟨0, ?_⟩
    intro n hn hn'
    have hn0 : 0 ≤ n := (from_ofNatFun_n₀_le (a * b) 0 n hn).1
    have hb0 : b n.toNat = 0 := by
      have := hMb n.toNat
      rw [hM, abs_nonpos_iff] at this
      exact this
    have hseq : ((Sequence.ofNatFun (a * b)).from 0).seq n = 0 := by
      rw [from_seq _ (ge_from_n₀ (a * b) (N := 0) hn0 hn0), ofNatFun_mul_seq,
          ofNatFun_seq_of_nonneg b hn0, hb0, mul_zero]
    have hseq' : ((Sequence.ofNatFun (a' * b)).from 0).seq n = 0 := by
      rw [from_seq _ (ge_from_n₀ (a' * b) (N := 0) hn0 hn0), ofNatFun_mul_seq,
          ofNatFun_seq_of_nonneg b hn0, hb0, mul_zero]
    rw [hseq, hseq', Section_4_3.close_iff]
    simpa using (le_of_lt hε)
  · have hMpos : 0 < M := lt_of_le_of_ne hM0 (Ne.symm hM)
    obtain ⟨N, hN⟩ := haa' (ε / M) (div_pos hε hMpos)
    refine ⟨N, ?_⟩
    intro n hn hn'
    have hnle := from_ofNatFun_n₀_le (a * b) N n hn
    have hna : n ≥ ((Sequence.ofNatFun a).from N).n₀ := by
      rw [from_n₀, ofNatFun_n₀]; omega
    have hna' : n ≥ ((Sequence.ofNatFun a').from N).n₀ := by
      rw [from_n₀, ofNatFun_n₀]; omega
    have hab := hN n hna hna'
    have hseq : ((Sequence.ofNatFun (a * b)).from N).seq n =
        ((Sequence.ofNatFun a).from N).seq n * b n.toNat := by
      rw [from_seq _ (ge_from_n₀ (a * b) hnle.2 hnle.1), ofNatFun_mul_seq,
          from_seq (Sequence.ofNatFun a) (ge_from_n₀ a hnle.2 hnle.1),
          ofNatFun_seq_of_nonneg b hnle.1]
    have hseq' : ((Sequence.ofNatFun (a' * b)).from N).seq n =
        ((Sequence.ofNatFun a').from N).seq n * b n.toNat := by
      rw [from_seq _ (ge_from_n₀ (a' * b) hnle.2 hnle.1), ofNatFun_mul_seq,
          from_seq (Sequence.ofNatFun a') (ge_from_n₀ a' hnle.2 hnle.1),
          ofNatFun_seq_of_nonneg b hnle.1]
    rw [hseq, hseq', Section_4_3.close_iff]
    rw [Section_4_3.close_iff] at hab
    have habs :
        |((Sequence.ofNatFun a).from N).seq n * b n.toNat -
            ((Sequence.ofNatFun a').from N).seq n * b n.toNat| =
          |((Sequence.ofNatFun a).from N).seq n -
            ((Sequence.ofNatFun a').from N).seq n| * |b n.toNat| := by
      rw [← sub_mul, abs_mul]
    rw [habs]
    have hble := hMb n.toNat
    calc
      |((Sequence.ofNatFun a).from N).seq n -
            ((Sequence.ofNatFun a').from N).seq n| * |b n.toNat|
          ≤ (ε / M) * M := mul_le_mul hab hble (abs_nonneg _) (le_of_lt (div_pos hε hMpos))
      _ = ε := div_mul_cancel₀ _ (ne_of_gt hMpos)

/-- Proposition 5.3.10 (Product of equivalent sequences is equivalent, right) / Exercise 5.3.2. -/
public theorem Sequence.mul_equiv_right {b b':ℕ → ℚ} (a:ℕ → ℚ)
    (ha : (Sequence.ofNatFun a).IsCauchy) (hbb': Equiv b b') :
    Equiv (a * b) (a * b') := by simp_rw [mul_comm]; exact mul_equiv_left a ha hbb'

/-- Proposition 5.3.10 (Product of equivalent sequences is equivalent) / Exercise 5.3.2. -/
public theorem Sequence.mul_equiv
    {a b a' b':ℕ → ℚ}
    (ha : (Sequence.ofNatFun a).IsCauchy)
    (hb' : (Sequence.ofNatFun b').IsCauchy)
    (haa': Equiv a a')
    (hbb': Equiv b b') : Equiv (a * b) (a' * b') :=
  equiv_trans (mul_equiv_right _ ha hbb') (mul_equiv_left _ hb' haa')

end Chapter5
