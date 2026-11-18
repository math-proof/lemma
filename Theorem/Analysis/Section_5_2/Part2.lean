module

public import Mathlib
public import Theorem.Analysis.Section_5_1.Part9
public import Abbrev.Analysis.Section_5_2.Part2
public import Theorem.Analysis.Section_4_3.Part2


public section

namespace Chapter5

private theorem ofNatFun_n₀ (a : ℕ → ℚ) : (Sequence.ofNatFun a).n₀ = 0 := rfl

private theorem from_n₀ (a : Sequence) (n₁ : ℤ) :
    (a.from n₁).n₀ = max a.n₀ n₁ := rfl

private theorem mk'_seq {n₀ n : ℤ} (b : {k // k ≥ n₀} → ℚ) (h : n ≥ n₀) :
    (Sequence.mk' n₀ b).seq n = b ⟨n, h⟩ := by
  dsimp [Sequence.mk']
  split
  · rfl
  · omega

/-- Definition 5.2.6 (Equivalent sequences) -/
public theorem Sequence.equiv_def (a b: ℕ → ℚ) :
    Equiv a b ↔ ∀ (ε:ℚ), ε > 0 → ε.EventuallyClose (Sequence.ofNatFun a) (Sequence.ofNatFun b) := by rfl

/-- Proposition 5.2.8 -/
public theorem Sequence.equiv_example :
  -- This proof is perhaps more complicated than it needs to be; a shorter version may be
  -- possible that is still faithful to the original text.
  Equiv (fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)) (fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)) := by
  set a := fun n:ℕ ↦ (1:ℚ)+10^(-(n:ℤ)-1)
  set b := fun n:ℕ ↦ (1:ℚ)-10^(-(n:ℤ)-1)
  rw [Sequence.equiv_def]
  intro ε hε
  have hab (n:ℕ) : |a n - b n| = 2 * 10 ^ (-(n:ℤ)-1) := calc
    _ = |((1:ℚ) + (10:ℚ)^(-(n:ℤ)-1)) - ((1:ℚ) - (10:ℚ)^(-(n:ℤ)-1))| := rfl
    _ = |2 * (10:ℚ)^(-(n:ℤ)-1)| := by ring_nf
    _ = _ := abs_of_nonneg (by positivity)
  have hab' (N:ℕ) : ∀ n ≥ N, |a n - b n| ≤ 2 * 10 ^(-(N:ℤ)-1) := by
    intro n hn; rw [hab n]; gcongr; norm_num
  have hN : ∃ N:ℕ, 2 * (10:ℚ) ^(-(N:ℤ)-1) ≤ ε := by
    have hN' (N:ℕ) : 2 * (10:ℚ)^(-(N:ℤ)-1) ≤ 2/(N+1) := calc
      _ = 2 / (10:ℚ)^(N+1) := by
        field_simp
        simp [←Section_4_3.pow_eq_zpow, ←zpow_add₀ (show 10 ≠ (0:ℚ) by norm_num)]
      _ ≤ _ := by
        gcongr
        apply le_trans _ (pow_le_pow_left₀ (show 0 ≤ (2:ℚ) by norm_num)
          (show (2:ℚ) ≤ 10 by norm_num) _)
        convert Nat.cast_le.mpr (Nat.le_of_lt (Nat.lt_two_pow_self (n := N+1))) using 1 <;> try infer_instance
        all_goals simp
    choose N hN using exists_nat_gt (2 / ε)
    refine ⟨ N, (hN' N).trans ?_ ⟩
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hε] at hN
    grind [mul_comm]
  choose N hN using hN
  refine ⟨(N : ℤ), ?_⟩
  intro n hnA hnB
  have hfroma : ((Sequence.ofNatFun a).from (N:ℤ)).n₀ = (N:ℤ) := by
    rw [from_n₀, ofNatFun_n₀]; simp
  have hfromb : ((Sequence.ofNatFun b).from (N:ℤ)).n₀ = (N:ℤ) := by
    rw [from_n₀, ofNatFun_n₀]; simp
  have hnN : (N:ℤ) ≤ n := by
    have hnA' := hnA
    rw [hfroma] at hnA'
    exact hnA'
  have hn0 : (0:ℤ) ≤ n := le_trans (Int.natCast_nonneg N) hnN
  have hNat : N ≤ n.toNat := by
    have hcast : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn0
    exact Nat.cast_le.mp (hcast ▸ hnN)
  have ha : ((Sequence.ofNatFun a).from (N:ℤ)).seq n = a n.toNat := by
    unfold Sequence.from
    have hmax : n ≥ max (Sequence.ofNatFun a).n₀ (N:ℤ) := by
      rw [ofNatFun_n₀]
      simp [hn0, hnN]
    rw [mk'_seq _ hmax]
    simp [Sequence.ofNatFun, hn0]
  have hbseq : ((Sequence.ofNatFun b).from (N:ℤ)).seq n = b n.toNat := by
    unfold Sequence.from
    have hmax : n ≥ max (Sequence.ofNatFun b).n₀ (N:ℤ) := by
      rw [ofNatFun_n₀]
      simp [hn0, hnN]
    rw [mk'_seq _ hmax]
    simp [Sequence.ofNatFun, hn0]
  rw [Section_4_3.close_iff, ha, hbseq]
  exact le_trans (hab' N n.toNat hNat) hN

end Chapter5
