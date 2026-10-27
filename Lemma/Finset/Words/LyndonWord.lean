import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Combinatorics.Words.LyndonWord.Part14
open scoped BigOperators
open MetaMathlibExt


namespace MetaMathlibExt

/--
[wittWordContent_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/LyndonWord.lean)
-/
@[path]
lemma wittWordContent_singleton
  {r : ℕ}
  {i : Fin r} :
-- imply
  wittWordContent [i] = Function.update (fun _ => 0) i 1 := by
-- proof
  funext j
  by_cases h : j = i
  · subst j
    simp [wittWordContent]
  · simp [wittWordContent, h, Ne.symm h]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[sum_wittDegreePred](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/LyndonWord.lean)
-/
@[path]
private lemma sum_wittDegreePred {r : ℕ} (degree : Fin r → ℕ) (i : Fin r)
  (hi : 0 < degree i) :
  (∑ j, wittDegreePred degree i j) = (∑ j, degree j) - 1 := by
  rw [wittDegreePred, Finset.sum_update_of_mem (Finset.mem_univ i)]
  rw [Finset.sdiff_singleton_eq_erase]
  have hsum := Finset.sum_erase_add Finset.univ degree (Finset.mem_univ i)
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[card_wordsOfContent_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/LyndonWord.lean)
-/
@[path]
private lemma card_wordsOfContent_eq_sum {r : ℕ} (degree : Fin r → ℕ)
  (hdegree : 0 < ∑ i, degree i) :
  Fintype.card (WordsOfContent degree) =
    ∑ i : WittPositiveLetter degree,
      Fintype.card (WordsOfContent (wittDegreePred degree i.1)) := by
  rwa [Fintype.card_congr (wittWordsConsEquiv degree hdegree)]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[sum_wittPositiveLetter](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/LyndonWord.lean)
-/
@[path]
private lemma sum_wittPositiveLetter {r : ℕ} (degree : Fin r → ℕ) :
  (∑ i : WittPositiveLetter degree, degree i.1) = ∑ i, degree i := by
  rw [← Finset.sum_subtype (Finset.univ.filter fun i => 0 < degree i) (by simp)]
  apply Finset.sum_subset (Finset.filter_subset (fun i => 0 < degree i) Finset.univ)
  intro i _ hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hi
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[prod_factorial_wittDegreePred](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/LyndonWord.lean)
-/
@[path]
private lemma prod_factorial_wittDegreePred {r : ℕ} (degree : Fin r → ℕ)
  (i : Fin r) (hi : 0 < degree i) :
  degree i * (∏ j, Nat.factorial (wittDegreePred degree i j)) =
    ∏ j, Nat.factorial (degree j) := by
  rw [wittDegreePred]
  have hfun : (fun j => Nat.factorial (Function.update degree i (degree i - 1) j)) =
    Function.update (fun j => Nat.factorial (degree j)) i (Nat.factorial (degree i - 1)) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [hji]
  rw [hfun, Finset.prod_update_of_mem (Finset.mem_univ i)]
  rw [Finset.sdiff_singleton_eq_erase]
  rw [← Finset.prod_erase_mul Finset.univ (fun j => Nat.factorial (degree j))
    (Finset.mem_univ i)]
  have hsucc : degree i - 1 + 1 = degree i := by omega
  have hfac : Nat.factorial (degree i) = degree i * Nat.factorial (degree i - 1) := by
    calc
      Nat.factorial (degree i) = Nat.factorial (degree i - 1 + 1) :=
        congr_arg Nat.factorial hsucc.symm
      _ = (degree i - 1 + 1) * Nat.factorial (degree i - 1) :=
        Nat.factorial_succ (degree i - 1)
      _ = degree i * Nat.factorial (degree i - 1) := by rw [hsucc]
  rw [hfac]
  ac_rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[prod_factorial_mul_multinomial_pred](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/LyndonWord.lean)
-/
@[path]
private lemma prod_factorial_mul_multinomial_pred {r : ℕ} (degree : Fin r → ℕ)
  (i : Fin r) (hi : 0 < degree i) :
  (∏ j, Nat.factorial (degree j)) *
    Nat.multinomial Finset.univ (wittDegreePred degree i) =
    degree i * Nat.factorial ((∑ j, degree j) - 1) := by
  calc
    (∏ j, Nat.factorial (degree j)) *
      Nat.multinomial Finset.univ (wittDegreePred degree i) =
      (degree i * ∏ j, Nat.factorial (wittDegreePred degree i j)) *
        Nat.multinomial Finset.univ (wittDegreePred degree i) := by
          rw [prod_factorial_wittDegreePred degree i hi]
    _ = degree i * ((∏ j, Nat.factorial (wittDegreePred degree i j)) *
      Nat.multinomial Finset.univ (wittDegreePred degree i)) := by ac_rfl
    _ = degree i * Nat.factorial (∑ j, wittDegreePred degree i j) := by
      rw [Nat.multinomial_spec]
    _ = degree i * Nat.factorial ((∑ j, degree j) - 1) := by
      rw [sum_wittDegreePred degree i hi]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[multinomial_eq_sum_pred](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/LyndonWord.lean)
-/
@[path]
private lemma multinomial_eq_sum_pred {r : ℕ} (degree : Fin r → ℕ)
  (hdegree : 0 < ∑ i, degree i) :
  Nat.multinomial Finset.univ degree =
    ∑ i : WittPositiveLetter degree,
      Nat.multinomial Finset.univ (wittDegreePred degree i.1) := by
  apply Nat.mul_left_cancel (n := ∏ j, Nat.factorial (degree j)) (by positivity)
  rw [Nat.multinomial_spec]
  rw [Finset.mul_sum]
  conv_rhs =>
    rw [Finset.sum_congr rfl fun i _ =>
      prod_factorial_mul_multinomial_pred degree i.1 i.2]
    rw [← Finset.sum_mul, sum_wittPositiveLetter]
  let n := ∑ i, degree i
  have hsucc : n - 1 + 1 = n := by dsimp [n]; omega
  calc
    Nat.factorial n = Nat.factorial (n - 1 + 1) := congr_arg Nat.factorial hsucc.symm
    _ = (n - 1 + 1) * Nat.factorial (n - 1) := Nat.factorial_succ (n - 1)
    _ = n * Nat.factorial (n - 1) := by rw [hsucc]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[card_wordsOfContent_eq_multinomial](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/LyndonWord.lean)
-/
@[path]
lemma card_wordsOfContent_eq_multinomial
  {r : ℕ}
  {degree : Fin r → ℕ} :
-- imply
  Fintype.card (WordsOfContent degree) = Nat.multinomial Finset.univ degree := by
-- proof
  induction hn : (∑ i, degree i) using Nat.strong_induction_on generalizing degree with
  | h n ih =>
    by_cases hn0 : n = 0
    · have hdegree : degree = fun _ => 0 := by
      funext i
      exact ((Finset.sum_eq_zero_iff_of_nonneg fun _ _ => Nat.zero_le _).mp
        (hn.trans hn0)) i (Finset.mem_univ i)
      subst degree
      have hcard : Fintype.card (WordsOfContent (fun _ : Fin r => 0)) = 1 := by
        apply Fintype.card_eq_one_iff.mpr
        refine ⟨⟨[], by funext i; simp [wittWordContent]⟩, fun w => ?_⟩
        apply Subtype.ext
        apply List.eq_nil_of_length_eq_zero
        rw [← sum_wittWordContent, w.2]
        simp
      rw [hcard]
      simp [Nat.multinomial]
    · have hdegree : 0 < ∑ i, degree i := hn.symm ▸ Nat.pos_of_ne_zero hn0
      rw [card_wordsOfContent_eq_sum degree hdegree]
      rw [multinomial_eq_sum_pred degree hdegree]
      apply Finset.sum_congr rfl
      intro i _
      apply ih ((∑ j, degree j) - 1)
      · omega
      · exact sum_wittDegreePred degree i.1 i.2

end MetaMathlibExt

namespace MetaMathlibExt

/--
[card_primitiveWords_eq_mul_lyndonWords](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/LyndonWord.lean)
-/
@[path]
private lemma card_primitiveWords_eq_mul_lyndonWords {r : ℕ}
  (degree : Fin r → ℕ) :
  Fintype.card (PrimitiveWordsOfContent degree) =
    (∑ i, degree i) * Fintype.card (LyndonWordsOfContent degree) := by
  rw [← Fintype.card_congr (wittLyndonRotationEquivPrimitive degree)]
  simp [mul_comm]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[card_words_eq_sum_primitive](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/LyndonWord.lean)
-/
@[path]
private lemma card_words_eq_sum_primitive {r : ℕ} (degree : Fin r → ℕ)
  (hdegree : 0 < ∑ i, degree i) :
  Fintype.card (WordsOfContent degree) =
    ∑ d ∈ Nat.divisors (Finset.univ.gcd degree),
      Fintype.card (PrimitiveWordsOfContent (fun i => degree i / d)) := by
  rw [Fintype.card_congr (wittWordsRootDataEquiv degree hdegree)]
  rw [Fintype.card_sigma]
  exact Finset.sum_attach (Nat.divisors (Finset.univ.gcd degree))
    (fun d => Fintype.card (PrimitiveWordsOfContent (fun i => degree i / d)))

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wittGcd_div](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/LyndonWord.lean)
-/
@[path]
private lemma wittGcd_div {r : ℕ} (degree : Fin r → ℕ) {k : ℕ}
  (hk : k ∣ Finset.univ.gcd degree) :
  Finset.univ.gcd (fun i => degree i / k) = Finset.univ.gcd degree / k := by
  apply Nat.dvd_antisymm
  · apply (Nat.dvd_div_iff_mul_dvd hk).2
    apply Finset.dvd_gcd
    intro i _
    have hkdi : k ∣ degree i := hk.trans (Finset.gcd_dvd (Finset.mem_univ i))
    have hdiv := Nat.mul_dvd_mul_left k
      (Finset.gcd_dvd (s := Finset.univ) (f := fun j => degree j / k)
        (Finset.mem_univ i))
    simpa [Nat.mul_div_cancel' hkdi] using hdiv
  · apply Finset.dvd_gcd
    intro i _
    have hkdi : k ∣ degree i := hk.trans (Finset.gcd_dvd (Finset.mem_univ i))
    exact (Nat.div_dvd_div_iff_right hk hkdi).2
      (Finset.gcd_dvd (Finset.mem_univ i))

end MetaMathlibExt

namespace MetaMathlibExt

/--
[wittSum_div_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/LyndonWord.lean)
-/
@[path]
private lemma wittSum_div_pos {r : ℕ} (degree : Fin r → ℕ)
  (hdegree : 0 < ∑ i, degree i) {k : ℕ} (hk0 : 0 < k)
  (hk : ∀ i, k ∣ degree i) : 0 < ∑ i, degree i / k := by
  obtain ⟨i, _, hi⟩ := Finset.sum_pos_iff.mp hdegree
  apply Finset.sum_pos_iff.mpr
  exact ⟨i, Finset.mem_univ i, Nat.div_pos (Nat.le_of_dvd hi (hk i)) hk0⟩

end MetaMathlibExt

/--
[wittWordContent_append](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/LyndonWord.lean)
-/
@[path]
private lemma wittWordContent_append_eq
  {r : ℕ}
  {u v : List (Fin r)} :
-- imply
  wittWordContent (u ++ v) = fun i => wittWordContent u i + wittWordContent v i := by
-- proof
  apply MetaMathlibExt.wittWordContent_append u v

/--
[wittWordContent_cons](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/LyndonWord.lean)
-/
@[path]
private lemma wittWordContent_cons_eq
  {r : ℕ}
  {i : Fin r}
  {w : List (Fin r)} :
-- imply
  wittWordContent (i :: w) =
    Function.update (wittWordContent w) i (wittWordContent w i + 1) := by
-- proof
  apply MetaMathlibExt.wittWordContent_cons i w

/--
[sum_wittWordContent](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/LyndonWord.lean)
-/
@[path]
private lemma sum_wittWordContent_eq
  {r : ℕ}
  {w : List (Fin r)} :
-- imply
  (∑ i, wittWordContent w i) = w.length := by
-- proof
  apply MetaMathlibExt.sum_wittWordContent w

/--
[isPrimitiveWord_iff_nodup_cyclicPermutations](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/LyndonWord.lean)
-/
@[path]
private lemma isPrimitiveWord_iff_nodup_cyclicPermutations_eq
  {w : List α} :
-- imply
  IsPrimitiveWord w ↔ w ≠ [] ∧ w.cyclicPermutations.Nodup := by
-- proof
  apply MetaMathlibExt.isPrimitiveWord_iff_nodup_cyclicPermutations

/--
[rotate_ne_of_isPrimitiveWord](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/LyndonWord.lean)
-/
@[path]
private lemma rotate_ne_of_isPrimitiveWord_eq
  {w : List α}
  {k : ℕ}
-- given
  (hw : IsPrimitiveWord w)
  (hk0 : 0 < k)
  (hk : k < w.length) :
-- imply
  w.rotate k ≠ w := by
-- proof
  apply MetaMathlibExt.rotate_ne_of_isPrimitiveWord hw hk0 hk

/--
[isPrimitiveWord_of_isLyndonWord](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/LyndonWord.lean)
-/
@[path]
private lemma isPrimitiveWord_of_isLyndonWord_eq
  [LinearOrder α]
  {w : List α}
-- given
  (hw : IsLyndonWord w) :
-- imply
  IsPrimitiveWord w := by
-- proof
  apply MetaMathlibExt.isPrimitiveWord_of_isLyndonWord hw

/--
[card_lyndonWordsOfContent_eq_wittMultigradedValue](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/LyndonWord.lean)
-/
@[path]
private lemma card_lyndonWordsOfContent_eq_wittMultigradedValue_eq
  {r : ℕ}
  {degree : Fin r → ℕ}
-- given
  (hdegree : 0 < ∑ i, degree i) :
-- imply
  (Fintype.card (LyndonWordsOfContent degree) : ℚ) = wittMultigradedValue degree := by
-- proof
  apply MetaMathlibExt.card_lyndonWordsOfContent_eq_wittMultigradedValue degree hdegree


-- created on 2026-10-20
-- updated on 2026-10-26
