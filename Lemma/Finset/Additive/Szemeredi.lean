import Mathlib
import sympy.Basic
import Def.Combinatorics.Additive.Szemeredi
open scoped Finset
open MathlibExt.Combinatorics.Additive.SzemerediWanted


namespace MathlibExt.Combinatorics.Additive.SzemerediWanted

/--
[szemWeight_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Additive/Szemeredi.lean)
-/
@[path]
private lemma szemWeight_le {k M : ℕ} (x : Fin M → Fin k) :
  szemWeight x ≤ (k - 1) * M := by
  classical
  rw [szemWeight]
  calc
    ∑ i, (x i : ℕ) ≤ ∑ _ : Fin M, (k - 1) := by
      apply Finset.sum_le_sum
      intro i _
      omega
    _ = (k - 1) * M := by simp [Nat.mul_comm]

end MathlibExt.Combinatorics.Additive.SzemerediWanted

namespace MathlibExt.Combinatorics.Additive.SzemerediWanted

/--
[szemWeight_line](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Additive/Szemeredi.lean)
-/
@[path]
private lemma szemWeight_line {k M : ℕ}
  (l : Combinatorics.Line (Fin k) (Fin M)) (a : Fin k) :
  szemWeight (l a) = (szemWildcards l).card * (a : ℕ) + szemFixed l := by
  classical
  rw [szemWeight, szemFixed, ← Finset.sum_add_sum_compl (szemWildcards l)]
  congr 1
  · rw [← Nat.nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_congr rfl
    intro i hi
    rw [szemWildcards, Finset.mem_filter] at hi
    rw [l.apply_none _ _ hi.right]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [szemWildcards, Finset.compl_filter, Finset.mem_filter] at hi
    obtain ⟨y, hy⟩ := Option.ne_none_iff_exists.mp hi.right
    simp [Combinatorics.Line.coe_apply, ← hy]

end MathlibExt.Combinatorics.Additive.SzemerediWanted

namespace MathlibExt.Combinatorics.Additive.SzemerediWanted

/--
[szemWildcards_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Additive/Szemeredi.lean)
-/
@[path]
private lemma szemWildcards_pos {k M : ℕ}
  (l : Combinatorics.Line (Fin k) (Fin M)) : 0 < (szemWildcards l).card := by
  apply Finset.card_pos.mpr
  obtain ⟨i, hi⟩ := l.proper
  exact ⟨i, by simp [szemWildcards, hi]⟩

end MathlibExt.Combinatorics.Additive.SzemerediWanted

namespace MathlibExt.Combinatorics.Additive.SzemerediWanted

/--
[szem_shift_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Additive/Szemeredi.lean)
-/
@[path]
private lemma szem_shift_card {n : ℕ} (A : Finset ℕ) (hA : A ⊆ Finset.range n)
  (s : ℕ) :
  (A.filter fun a => s ≤ a).card =
    ((Finset.range n).filter fun t => t + s ∈ A).card := by
  classical
  apply Finset.card_bij (fun a _ => a - s)
  · intro a ha
    rw [Finset.mem_filter] at ha ⊢
    have han : a < n := Finset.mem_range.mp (hA ha.1)
    exact ⟨Finset.mem_range.mpr (by omega), by simpa [Nat.sub_add_cancel ha.2] using ha.1⟩
  · intro a₁ ha₁ a₂ ha₂ heq
    rw [Finset.mem_filter] at ha₁ ha₂
    omega
  · intro t ht
    rw [Finset.mem_filter] at ht
    refine ⟨t + s, ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨ht.2, by omega⟩
    · omega

end MathlibExt.Combinatorics.Additive.SzemerediWanted

namespace MathlibExt.Combinatorics.Additive.SzemerediWanted

/--
[szem_card_le_shift_card_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Additive/Szemeredi.lean)
-/
@[path]
private lemma szem_card_le_shift_card_add {n : ℕ} (A : Finset ℕ)
  (hA : A ⊆ Finset.range n) (s C : ℕ) (hs : s ≤ C) :
  A.card ≤ ((Finset.range n).filter fun t => t + s ∈ A).card + C := by
  classical
  have hbad : (A.filter fun a => ¬s ≤ a).card ≤ s := by
    have hsubset : A.filter (fun a => ¬s ≤ a) ⊆ Finset.range s := by
      intro a ha
      rw [Finset.mem_filter] at ha
      exact Finset.mem_range.mpr (by omega)
    simpa using Finset.card_le_card hsubset
  have hpart := Finset.card_filter_add_card_filter_not (s := A) (fun a => s ≤ a)
  rw [szem_shift_card A hA s] at hpart
  omega

end MathlibExt.Combinatorics.Additive.SzemerediWanted

namespace MathlibExt.Combinatorics.Additive.SzemerediWanted

/--
[szem_double_count](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Additive/Szemeredi.lean)
-/
@[path]
private lemma szem_double_count (k M n : ℕ) (A : Finset ℕ) :
  ∑ t ∈ Finset.range n,
    (Finset.univ.filter fun x : Fin M → Fin k => t + szemWeight x ∈ A).card =
    ∑ x : Fin M → Fin k,
      ((Finset.range n).filter fun t => t + szemWeight x ∈ A).card := by
  classical
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]

end MathlibExt.Combinatorics.Additive.SzemerediWanted

namespace MathlibExt.Combinatorics.Additive.SzemerediWanted

/--
[szem_exists_dense_translate](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Additive/Szemeredi.lean)
-/
@[path]
private lemma szem_exists_dense_translate {k M n : ℕ} {δ : ℝ}
  (hk : 2 ≤ k) (hn : 0 < n) (A : Finset ℕ)
  (hA : A ⊆ Finset.range n) (hden : δ * (n : ℝ) ≤ (A.card : ℝ))
  (hloss : 2 * (((k - 1) * M : ℕ) : ℝ) ≤ δ * (n : ℝ)) :
  ∃ t ∈ Finset.range n,
    δ / 2 * ((k : ℝ) ^ M) ≤
      ((Finset.univ.filter fun x : Fin M → Fin k => t + szemWeight x ∈ A).card : ℝ) := by
  classical
  have hcount :
    k ^ M * A.card ≤
      (∑ t ∈ Finset.range n,
        (Finset.univ.filter fun x : Fin M → Fin k => t + szemWeight x ∈ A).card) +
        k ^ M * ((k - 1) * M) := by
    rw [szem_double_count]
    calc
      k ^ M * A.card = ∑ _x : Fin M → Fin k, A.card := by
        simp
      _ ≤ ∑ x : Fin M → Fin k,
        (((Finset.range n).filter fun t => t + szemWeight x ∈ A).card +
          (k - 1) * M) := by
        apply Finset.sum_le_sum
        intro x _
        exact szem_card_le_shift_card_add A hA (szemWeight x) ((k - 1) * M)
          (szemWeight_le x)
      _ = (∑ x : Fin M → Fin k,
        ((Finset.range n).filter fun t => t + szemWeight x ∈ A).card) +
        k ^ M * ((k - 1) * M) := by
        simp [Finset.sum_add_distrib]
  have hcountReal :
    (k : ℝ) ^ M * (A.card : ℝ) ≤
      ((∑ t ∈ Finset.range n,
        (Finset.univ.filter fun x : Fin M → Fin k => t + szemWeight x ∈ A).card : ℕ) : ℝ) +
        (k : ℝ) ^ M * (((k - 1) * M : ℕ) : ℝ) := by
    exact_mod_cast hcount
  have hpow : 0 ≤ (k : ℝ) ^ M := by positivity
  have hdenMul := mul_le_mul_of_nonneg_left hden hpow
  have hlossHalf : (((k - 1) * M : ℕ) : ℝ) ≤ δ * (n : ℝ) / 2 := by
    linarith
  have hlossMul := mul_le_mul_of_nonneg_left hlossHalf hpow
  have havg :
    (n : ℝ) * (δ / 2 * (k : ℝ) ^ M) ≤
      ((∑ t ∈ Finset.range n,
        (Finset.univ.filter fun x : Fin M → Fin k => t + szemWeight x ∈ A).card : ℕ) : ℝ) := by
    nlinarith [hdenMul, hlossMul, hcountReal]
  have hsum :
    ∑ _t ∈ Finset.range n, δ / 2 * ((k : ℝ) ^ M) ≤
      ∑ t ∈ Finset.range n,
        ((Finset.univ.filter fun x : Fin M → Fin k => t + szemWeight x ∈ A).card : ℝ) := by
    simpa using havg
  exact Finset.exists_le_of_sum_le ⟨0, Finset.mem_range.mpr hn⟩ hsum

end MathlibExt.Combinatorics.Additive.SzemerediWanted

namespace MathlibExt.Combinatorics.Additive.SzemerediWanted

/--
[szemeredi](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Additive/Szemeredi.lean)
-/
@[path]
lemma szemeredi
  :
-- imply
  ∀ k : ℕ, 0 < k → ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ A : Finset ℕ, A ⊆ Finset.range n → δ * (n : ℝ) ≤ (A.card : ℝ) →
    ∃ a d : ℕ, 0 < d ∧ ∀ i : ℕ, i < k → a + i * d ∈ A := by
-- proof
  intro k hk δ hδ
  by_cases hk1 : k = 1
  · subst k
    refine ⟨1, ?_⟩
    intro n hn A _ hden
    have hnpos : 0 < n := by omega
    have hcardReal : 0 < (A.card : ℝ) :=
      lt_of_lt_of_le (mul_pos hδ (Nat.cast_pos.mpr hnpos)) hden
    have hcard : 0 < A.card := by exact_mod_cast hcardReal
    obtain ⟨a, ha⟩ := Finset.card_pos.mp hcard
    refine ⟨a, 1, by omega, ?_⟩
    intro i hi
    have : i = 0 := by omega
    subst i
    simpa using ha
  · have hk2 : 2 ≤ k := by omega
    obtain ⟨M, hM⟩ :=
      MathlibExt.Combinatorics.DensityHalesJewettWanted.density_hales_jewett
        k hk2 (δ / 2) (by positivity)
    obtain ⟨N₀, hN₀⟩ :=
      exists_nat_ge (2 * (((k - 1) * M : ℕ) : ℝ) / δ)
    refine ⟨N₀ + 1, ?_⟩
    intro n hn A hA hden
    have hnpos : 0 < n := by omega
    have hN₀n : N₀ ≤ n := by omega
    have hN₀nReal : (N₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hN₀n
    have hratio : 2 * (((k - 1) * M : ℕ) : ℝ) / δ ≤ (n : ℝ) :=
      hN₀.trans hN₀nReal
    have hloss : 2 * (((k - 1) * M : ℕ) : ℝ) ≤ δ * (n : ℝ) := by
      simpa [mul_comm] using (div_le_iff₀ hδ).mp hratio
    obtain ⟨t, _ht, hB⟩ :=
      szem_exists_dense_translate hk2 hnpos A hA hden hloss
    let B : Finset (Fin M → Fin k) :=
      Finset.univ.filter fun x => t + szemWeight x ∈ A
    have hBden : δ / 2 * ((k : ℝ) ^ M) ≤ (B.card : ℝ) := by
      simpa [B] using hB
    obtain ⟨l, hl⟩ := hM B hBden
    refine ⟨t + szemFixed l, (szemWildcards l).card, szemWildcards_pos l, ?_⟩
    intro i hi
    let a : Fin k := ⟨i, hi⟩
    have hla := hl a
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hla
    rw [szemWeight_line] at hla
    simpa [a, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hla

end MathlibExt.Combinatorics.Additive.SzemerediWanted


-- created on 2026-10-20
-- updated on 2026-10-23
