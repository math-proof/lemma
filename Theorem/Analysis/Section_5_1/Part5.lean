module

public import Mathlib
public import Theorem.Analysis.Section_4_3.Part2
public import Abbrev.Analysis.Section_5_1.Part5
set_option doc.verso.suggestions false

/-!
# Analysis I, Section 5.1: Cauchy sequences

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Notion of a sequence of rationals
- Notions of `ε`-steadiness, eventual `ε`-steadiness, and Cauchy sequences

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/

public section


namespace Chapter5

public theorem Sequence.isCauchy_def (a:Sequence) :
  a.IsCauchy ↔ ∀ ε > (0:ℚ), ε.EventuallySteady a := by rfl

private theorem ofNatFun_n₀ (a : ℕ → ℚ) : (Sequence.ofNatFun a).n₀ = 0 := rfl

private theorem ofNatFun_seq (a : ℕ → ℚ) (n : ℕ) :
    (Sequence.ofNatFun a).seq n = a n := by
  simp [Sequence.ofNatFun]

private theorem from_n₀ (a : Sequence) (n₁ : ℤ) :
    (a.from n₁).n₀ = max a.n₀ n₁ := rfl

private theorem mk'_n₀ (n₀ : ℤ) (b : {k // k ≥ n₀} → ℚ) :
    (Sequence.mk' n₀ b).n₀ = n₀ := rfl

private theorem mk'_seq {n₀ n : ℤ} (b : {k // k ≥ n₀} → ℚ) (h : n ≥ n₀) :
    (Sequence.mk' n₀ b).seq n = b ⟨n, h⟩ := by
  dsimp [Sequence.mk']
  split
  · rfl
  · omega

/-- Definition of Cauchy sequences, for a sequence starting at {lean}`0` -/
public theorem Sequence.IsCauchy.coe (a:ℕ → ℚ) :
    (Sequence.ofNatFun a).IsCauchy ↔ ∀ ε > (0:ℚ), ∃ N, ∀ j ≥ N, ∀ k ≥ N,
    Section_4_3.dist (a j) (a k) ≤ ε := by
  constructor
  · intro h ε hε
    obtain ⟨N, hN, hSteady⟩ := h ε hε
    have hN0 : 0 ≤ N := by simpa [ofNatFun_n₀] using hN
    lift N to ℕ using hN0
    refine ⟨N, ?_⟩
    intro j hj k hk
    have hb_j : ((Sequence.ofNatFun a).from (N:ℤ)).n₀ ≤ (j:ℤ) := by
      rw [from_n₀, ofNatFun_n₀]; exact_mod_cast hj
    have hb_k : ((Sequence.ofNatFun a).from (N:ℤ)).n₀ ≤ (k:ℤ) := by
      rw [from_n₀, ofNatFun_n₀]; exact_mod_cast hk
    have hclose := hSteady (j:ℤ) hb_j (k:ℤ) hb_k
    have seq_from (t : ℕ) (ht : N ≤ t) :
        ((Sequence.ofNatFun a).from (N:ℤ)).seq (t:ℤ) = a t := by
      have hb : ((Sequence.ofNatFun a).from (N:ℤ)).n₀ ≤ (t:ℤ) := by
        rw [from_n₀, ofNatFun_n₀]; exact_mod_cast ht
      unfold Sequence.from
      rw [mk'_seq _ hb, ofNatFun_seq]
    rw [seq_from j hj, seq_from k hk] at hclose
    rw [Section_4_3.dist_eq]
    exact (Section_4_3.close_iff ε (a j) (a k)).mp hclose
  · intro h ε hε
    obtain ⟨N, h'⟩ := h ε hε
    refine ⟨(N:ℤ), ?hN0, ?hSteady⟩
    · simp [ofNatFun_n₀]
    intro n hn m hm
    have hfrom0 : ((Sequence.ofNatFun a).from (N:ℤ)).n₀ = (N:ℤ) := by
      rw [from_n₀, ofNatFun_n₀]; simp
    have npos : 0 ≤ n := by rw [hfrom0] at hn; linarith
    have mpos : 0 ≤ m := by rw [hfrom0] at hm; linarith
    have hnN : (N:ℤ) ≤ n := by rwa [hfrom0] at hn
    have hmN : (N:ℤ) ≤ m := by rwa [hfrom0] at hm
    lift n to ℕ using npos
    lift m to ℕ using mpos
    have hdist : Section_4_3.dist (a n) (a m) ≤ ε :=
      h' n (by exact_mod_cast hnN) m (by exact_mod_cast hmN)
    have seq_from (t : ℕ) (ht : (N:ℤ) ≤ (t:ℤ)) :
        ((Sequence.ofNatFun a).from (N:ℤ)).seq (t:ℤ) = a t := by
      have hb : ((Sequence.ofNatFun a).from (N:ℤ)).n₀ ≤ (t:ℤ) := by
        rwa [hfrom0]
      unfold Sequence.from
      rw [mk'_seq _ hb, ofNatFun_seq]
    rw [seq_from n hnN, seq_from m hmN]
    rw [Section_4_3.dist_eq] at hdist
    exact (Section_4_3.close_iff ε (a n) (a m)).mpr hdist

public theorem Sequence.IsCauchy.mk {n₀:ℤ} (a: {n // n ≥ n₀} → ℚ) :
    (Sequence.mk' n₀ a).IsCauchy ↔ ∀ ε > (0:ℚ), ∃ N ≥ n₀, ∀ j ≥ N, ∀ k ≥ N,
    Section_4_3.dist ((Sequence.mk' n₀ a).seq j) ((Sequence.mk' n₀ a).seq k) ≤ ε := by
  constructor
  · intro h ε hε
    obtain ⟨N, hN, hSteady⟩ := h ε hε
    have hn0 : (Sequence.mk' n₀ a).n₀ = n₀ := mk'_n₀ n₀ a
    have hN' : N ≥ n₀ := by rwa [hn0] at hN
    refine ⟨N, hN', ?_⟩
    intro j hj k hk
    have hmax : max n₀ N = N := by omega
    have hb_j : ((Sequence.mk' n₀ a).from N).n₀ ≤ j := by
      rw [from_n₀, hmax]; exact hj
    have hb_k : ((Sequence.mk' n₀ a).from N).n₀ ≤ k := by
      rw [from_n₀, hmax]; exact hk
    have hclose := hSteady j hb_j k hb_k
    have seq_from (t : ℤ) (ht : N ≤ t) :
        ((Sequence.mk' n₀ a).from N).seq t = (Sequence.mk' n₀ a).seq t := by
      have hb : ((Sequence.mk' n₀ a).from N).n₀ ≤ t := by
        rw [from_n₀, hmax]; exact ht
      unfold Sequence.from
      rw [mk'_seq _ hb]
    rw [seq_from j hj, seq_from k hk] at hclose
    rw [Section_4_3.dist_eq]
    exact (Section_4_3.close_iff ε ((Sequence.mk' n₀ a).seq j) ((Sequence.mk' n₀ a).seq k)).mp hclose
  · intro h ε hε
    obtain ⟨N, hN, h'⟩ := h ε hε
    refine ⟨max n₀ N, ?_, ?_⟩
    · rw [mk'_n₀]; exact le_max_left n₀ N
    intro n hn m hm
    have hfrom : ((Sequence.mk' n₀ a).from (max n₀ N)).n₀ = max n₀ N := by
      rw [from_n₀, mk'_n₀]
      simp
    have hn' : max n₀ N ≤ n := by rwa [hfrom] at hn
    have hm' : max n₀ N ≤ m := by rwa [hfrom] at hm
    have hjN : N ≤ n := le_trans (le_max_right _ _) hn'
    have hkN : N ≤ m := le_trans (le_max_right _ _) hm'
    have hdist : Section_4_3.dist ((Sequence.mk' n₀ a).seq n) ((Sequence.mk' n₀ a).seq m) ≤ ε :=
      h' n hjN m hkN
    have seq_from (t : ℤ) (ht : max n₀ N ≤ t) :
        ((Sequence.mk' n₀ a).from (max n₀ N)).seq t = (Sequence.mk' n₀ a).seq t := by
      have hb : ((Sequence.mk' n₀ a).from (max n₀ N)).n₀ ≤ t := by
        rwa [hfrom]
      unfold Sequence.from
      rw [mk'_seq _ hb]
    rw [seq_from n hn', seq_from m hm']
    rw [Section_4_3.dist_eq] at hdist
    exact (Section_4_3.close_iff ε ((Sequence.mk' n₀ a).seq n) ((Sequence.mk' n₀ a).seq m)).mpr hdist

end Chapter5
