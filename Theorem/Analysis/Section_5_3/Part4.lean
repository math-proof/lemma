module

public import Mathlib
public import Theorem.Analysis.Section_5_2.Part2
public import Mathlib.Algebra.Group.MinimalAxioms
public import Abbrev.Analysis.Section_5_3.Part2

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

private theorem ofNatFun_add_seq (a b : ℕ → ℚ) (n : ℤ) :
    (Sequence.ofNatFun (a + b)).seq n =
      (Sequence.ofNatFun a).seq n + (Sequence.ofNatFun b).seq n := by
  simp [Sequence.ofNatFun, Pi.add_apply]
  split_ifs <;> ring

private theorem from_ofNatFun_n₀_le (a : ℕ → ℚ) (N n : ℤ)
    (hn : n ≥ ((Sequence.ofNatFun a).from N).n₀) : 0 ≤ n ∧ N ≤ n := by
  rw [from_n₀, ofNatFun_n₀] at hn
  constructor <;> omega

private theorem ge_from_n₀ (a : ℕ → ℚ) {N n : ℤ} (hN : N ≤ n) (hn0 : 0 ≤ n) :
    n ≥ max (Sequence.ofNatFun a).n₀ N := by
  rw [ofNatFun_n₀]
  omega

public theorem LIM_def {a:ℕ → ℚ} (ha: (Sequence.ofNatFun a).IsCauchy) :
    LIM a = Quotient.mk _ (CauchySequence.mk' ha) := by
  rw [LIM, dif_pos ha]

/-- Definition 5.3.1 (Real numbers) -/
public theorem Real.eq_lim (x:Real) : ∃ (a:ℕ → ℚ), (Sequence.ofNatFun a).IsCauchy ∧ x = LIM a := by
  apply Quotient.ind _ x
  intro a
  use (a : ℕ → ℚ)
  have hseq : Sequence.ofNatFun (a : ℕ → ℚ) = a.toSequence := CauchySequence.coe_to_sequence a
  have hcauchy : (Sequence.ofNatFun (a : ℕ → ℚ)).IsCauchy := by
    rw [hseq]
    exact a.cauchy
  refine ⟨hcauchy, ?_⟩
  rw [LIM_def hcauchy]
  congr
  apply CauchySequence.ext'
  have hmk : (CauchySequence.mk' hcauchy).seq = (Sequence.ofNatFun (a : ℕ → ℚ)).seq := rfl
  rw [hmk, hseq]

/-- Definition 5.3.1 (Real numbers) -/
public theorem Real.LIM_eq_LIM {a b:ℕ → ℚ} (ha: (Sequence.ofNatFun a).IsCauchy)
    (hb: (Sequence.ofNatFun b).IsCauchy) :
    LIM a = LIM b ↔ Sequence.Equiv a b := by
  constructor
  · intro h
    unfold LIM at h
    have h := Quotient.exact h
    rwa [dif_pos ha, dif_pos hb, CauchySequence.equiv_iff] at h
  · intro h
    unfold LIM
    apply Quotient.sound
    rwa [dif_pos ha, dif_pos hb, CauchySequence.equiv_iff]

/-- Lemma 5.3.6 (Sum of Cauchy sequences is Cauchy). -/
public theorem Sequence.IsCauchy.add {a b:ℕ → ℚ}
    (ha: (Sequence.ofNatFun a).IsCauchy) (hb: (Sequence.ofNatFun b).IsCauchy) :
    (Sequence.ofNatFun (a + b)).IsCauchy := by
  -- This proof is written to follow the structure of the original text.
  intro ε hε
  choose N1 hN1 ha using ha _ (half_pos hε)
  choose N2 hN2 hb using hb _ (half_pos hε)
  refine ⟨max N1 N2, ?_, ?_⟩
  · simpa [ofNatFun_n₀] using le_trans hN1 (le_max_left N1 N2)
  intro j hj k hk
  have hj' := from_ofNatFun_n₀_le (a + b) (max N1 N2) j hj
  have hk' := from_ofNatFun_n₀_le (a + b) (max N1 N2) k hk
  have hj1 : j ≥ ((Sequence.ofNatFun a).from N1).n₀ := by
    rw [from_n₀, ofNatFun_n₀]; omega
  have hk1 : k ≥ ((Sequence.ofNatFun a).from N1).n₀ := by
    rw [from_n₀, ofNatFun_n₀]; omega
  have hj2 : j ≥ ((Sequence.ofNatFun b).from N2).n₀ := by
    rw [from_n₀, ofNatFun_n₀]; omega
  have hk2 : k ≥ ((Sequence.ofNatFun b).from N2).n₀ := by
    rw [from_n₀, ofNatFun_n₀]; omega
  have h1 := ha j hj1 k hk1
  have h2 := hb j hj2 k hk2
  have hjseq : ((Sequence.ofNatFun (a + b)).from (max N1 N2)).seq j =
      ((Sequence.ofNatFun a).from N1).seq j + ((Sequence.ofNatFun b).from N2).seq j := by
    have hmax : j ≥ max (Sequence.ofNatFun (a + b)).n₀ (max N1 N2) := by
      rw [ofNatFun_n₀]; omega
    rw [from_seq _ hmax, ofNatFun_add_seq,
        from_seq (Sequence.ofNatFun a) (ge_from_n₀ a (le_trans (le_max_left N1 N2) hj'.2) hj'.1),
        from_seq (Sequence.ofNatFun b) (ge_from_n₀ b (le_trans (le_max_right N1 N2) hj'.2) hj'.1)]
  have hkseq : ((Sequence.ofNatFun (a + b)).from (max N1 N2)).seq k =
      ((Sequence.ofNatFun a).from N1).seq k + ((Sequence.ofNatFun b).from N2).seq k := by
    have hmax : k ≥ max (Sequence.ofNatFun (a + b)).n₀ (max N1 N2) := by
      rw [ofNatFun_n₀]; omega
    rw [from_seq _ hmax, ofNatFun_add_seq,
        from_seq (Sequence.ofNatFun a) (ge_from_n₀ a (le_trans (le_max_left N1 N2) hk'.2) hk'.1),
        from_seq (Sequence.ofNatFun b) (ge_from_n₀ b (le_trans (le_max_right N1 N2) hk'.2) hk'.1)]
  rw [hjseq, hkseq]
  convert Section_4_3.add_close h1 h2
  linarith

/-- Lemma 5.3.7 (Sum of equivalent sequences is equivalent, left). -/
public theorem Sequence.add_equiv_left {a a':ℕ → ℚ} (b:ℕ → ℚ) (haa': Equiv a a') :
    Equiv (a + b) (a' + b) := by
  -- This proof is written to follow the structure of the original text.
  intro ε hε
  obtain ⟨N, hN⟩ := haa' ε hε
  refine ⟨N, ?_⟩
  intro n hn hn'
  have hn0N := from_ofNatFun_n₀_le (a + b) N n hn
  have hna : n ≥ ((Sequence.ofNatFun a).from N).n₀ := by
    rw [from_n₀, ofNatFun_n₀]; omega
  have hna' : n ≥ ((Sequence.ofNatFun a').from N).n₀ := by
    rw [from_n₀, ofNatFun_n₀]; omega
  have hab := hN n hna hna'
  have hseq : ((Sequence.ofNatFun (a + b)).from N).seq n =
      ((Sequence.ofNatFun a).from N).seq n + (Sequence.ofNatFun b).seq n := by
    have hmax : n ≥ max (Sequence.ofNatFun (a + b)).n₀ N := by
      rw [ofNatFun_n₀]; omega
    rw [from_seq _ hmax, ofNatFun_add_seq,
        from_seq (Sequence.ofNatFun a) (ge_from_n₀ a hn0N.2 hn0N.1)]
  have hseq' : ((Sequence.ofNatFun (a' + b)).from N).seq n =
      ((Sequence.ofNatFun a').from N).seq n + (Sequence.ofNatFun b).seq n := by
    have hmax : n ≥ max (Sequence.ofNatFun (a' + b)).n₀ N := by
      rw [ofNatFun_n₀]; omega
    rw [from_seq _ hmax, ofNatFun_add_seq,
        from_seq (Sequence.ofNatFun a') (ge_from_n₀ a' hn0N.2 hn0N.1)]
  have hbval : (Sequence.ofNatFun b).seq n = b n.toNat :=
    ofNatFun_seq_of_nonneg b hn0N.1
  rw [hseq, hseq', hbval]
  convert Section_4_3.add_close hab (Section_4_3.close_refl (b n.toNat))
  simp

/-- Lemma 5.3.7 (Sum of equivalent sequences is equivalent, right). -/
public theorem Sequence.add_equiv_right {b b':ℕ → ℚ} (a:ℕ → ℚ) (hbb': Equiv b b') :
    Equiv (a + b) (a + b') := by simp_rw [add_comm]; exact add_equiv_left _ hbb'

/-- Proposition 5.3.3 / Exercise 5.3.1 -/
public theorem Sequence.equiv_trans {a b c:ℕ → ℚ} (hab: Equiv a b) (hbc: Equiv b c) :
    Equiv a c := by
  intro ε hε
  obtain ⟨N1, h1⟩ := hab (ε / 2) (half_pos hε)
  obtain ⟨N2, h2⟩ := hbc (ε / 2) (half_pos hε)
  refine ⟨max N1 N2, ?_⟩
  intro n hnA hnC
  have hn := from_ofNatFun_n₀_le a (max N1 N2) n hnA
  have hn1a : n ≥ ((Sequence.ofNatFun a).from N1).n₀ := by
    rw [from_n₀, ofNatFun_n₀]; omega
  have hn1b : n ≥ ((Sequence.ofNatFun b).from N1).n₀ := by
    rw [from_n₀, ofNatFun_n₀]; omega
  have hn2b : n ≥ ((Sequence.ofNatFun b).from N2).n₀ := by
    rw [from_n₀, ofNatFun_n₀]; omega
  have hn2c : n ≥ ((Sequence.ofNatFun c).from N2).n₀ := by
    rw [from_n₀, ofNatFun_n₀]; omega
  have habn := h1 n hn1a hn1b
  have hbcn := h2 n hn2b hn2c
  have haseq : ((Sequence.ofNatFun a).from (max N1 N2)).seq n =
      ((Sequence.ofNatFun a).from N1).seq n := by
    have hmax : n ≥ max (Sequence.ofNatFun a).n₀ (max N1 N2) :=
      ge_from_n₀ a hn.2 hn.1
    rw [from_seq _ hmax, from_seq (Sequence.ofNatFun a)
      (ge_from_n₀ a (le_trans (le_max_left N1 N2) hn.2) hn.1)]
  have hcseq : ((Sequence.ofNatFun c).from (max N1 N2)).seq n =
      ((Sequence.ofNatFun c).from N2).seq n := by
    have hmax : n ≥ max (Sequence.ofNatFun c).n₀ (max N1 N2) :=
      ge_from_n₀ c hn.2 hn.1
    rw [from_seq _ hmax, from_seq (Sequence.ofNatFun c)
      (ge_from_n₀ c (le_trans (le_max_right N1 N2) hn.2) hn.1)]
  have hbseq : ((Sequence.ofNatFun b).from N1).seq n =
      ((Sequence.ofNatFun b).from N2).seq n := by
    rw [from_seq (Sequence.ofNatFun b)
      (ge_from_n₀ b (le_trans (le_max_left N1 N2) hn.2) hn.1),
        from_seq (Sequence.ofNatFun b)
      (ge_from_n₀ b (le_trans (le_max_right N1 N2) hn.2) hn.1)]
  rw [haseq, hcseq]
  have hbcn' : (ε / 2).Close (((Sequence.ofNatFun b).from N1).seq n)
      (((Sequence.ofNatFun c).from N2).seq n) := by
    rwa [hbseq]
  convert Section_4_3.close_trans habn hbcn'
  linarith

/-- Lemma 5.3.7 (Sum of equivalent sequences is equivalent). -/
public theorem Sequence.add_equiv {a b a' b':ℕ → ℚ} (haa': Equiv a a')
    (hbb': Equiv b b') :
    Equiv (a + b) (a' + b') :=
  equiv_trans (add_equiv_left _ haa') (add_equiv_right _ hbb')

end Chapter5
