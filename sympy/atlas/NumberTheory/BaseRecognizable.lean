/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BaseRecognizable.lean -/

import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic.Ring

/-!
# Base-`k` recognizable sets of natural numbers

A finite-automaton interface for subsets of `ℕ` recognizable in base `k`, shared by Cobham's
theorem on base dependence and Cobham's gap theorem.
-/

namespace MetaMathlibExt

/-- The value of a base-`k` digit word, with its most significant digit first. -/
def baseWordValue {k : ℕ} (w : List (Fin k)) : ℕ :=
  w.foldl (fun value digit ↦ value * k + digit.val) 0

/-- A canonical base expansion is empty for zero and otherwise has no leading zero. -/
def IsCanonicalBaseWord {k : ℕ} : List (Fin k) → Prop
  | [] => True
  | digit :: _ => digit.val ≠ 0

/-- A subset of `ℕ` is recognizable in base `k` when a finite deterministic
automaton accepts exactly its canonical base-`k` expansions. -/
def IsBaseRecognizable (k : ℕ) (S : Set ℕ) : Prop :=
  2 ≤ k ∧
    ∃ numStates : ℕ, 0 < numStates ∧
      ∃ init : Fin numStates,
        ∃ transition : Fin numStates → Fin k → Fin numStates,
          ∃ accept : Fin numStates → Bool,
            ∀ w : List (Fin k),
              (accept (w.foldl transition init) = true ↔
                IsCanonicalBaseWord w ∧ baseWordValue w ∈ S)

@[simp]
theorem baseWordValue_nil {k : ℕ} : baseWordValue ([] : List (Fin k)) = 0 :=
  rfl

private lemma foldl_baseValue {k : ℕ} (w : List (Fin k)) (a : ℕ) :
    w.foldl (fun value digit ↦ value * k + digit.val) a =
      a * k ^ w.length + baseWordValue w := by
  induction w generalizing a with
  | nil => simp [baseWordValue]
  | cons d w ih =>
    rw [List.foldl_cons, ih, show baseWordValue (d :: w) =
      w.foldl (fun value digit ↦ value * k + digit.val) d.val by
        simp [baseWordValue]]
    rw [ih]
    simp only [List.length_cons, pow_succ]
    ring

theorem baseWordValue_append {k : ℕ} (u v : List (Fin k)) :
    baseWordValue (u ++ v) =
      baseWordValue u * k ^ v.length + baseWordValue v := by
  simp only [baseWordValue, List.foldl_append]
  exact foldl_baseValue v _

@[simp]
theorem isCanonicalBaseWord_nil {k : ℕ} : IsCanonicalBaseWord ([] : List (Fin k)) :=
  trivial

@[simp]
theorem isCanonicalBaseWord_cons {k : ℕ} (d : Fin k) (w : List (Fin k)) :
    IsCanonicalBaseWord (d :: w) ↔ d.val ≠ 0 :=
  Iff.rfl

theorem IsCanonicalBaseWord.append {k : ℕ} {u v : List (Fin k)}
    (hu : IsCanonicalBaseWord u) (hne : u ≠ []) :
    IsCanonicalBaseWord (u ++ v) := by
  cases u with
  | nil => contradiction
  | cons d u => simpa [IsCanonicalBaseWord] using hu

/-- The canonical base-`k` expansion of `n`, most significant digit first. -/
def baseDigits {k : ℕ} (hk : 2 ≤ k) (n : ℕ) : List (Fin k) :=
  (Nat.digits k n).reverse.map fun d ↦ ⟨d % k, Nat.mod_lt _ (by omega)⟩

private lemma baseWordValue_reverse_digits {k : ℕ} (hk : 2 ≤ k)
    (ds : List ℕ) (hds : ∀ d ∈ ds, d < k) :
    baseWordValue (ds.reverse.map fun d ↦ (⟨d % k, Nat.mod_lt _ (by omega)⟩ : Fin k)) =
      Nat.ofDigits k ds := by
  induction ds with
  | nil => simp [baseWordValue]
  | cons d ds ih =>
    rw [List.reverse_cons, List.map_append, baseWordValue_append]
    simp only [List.map_singleton, List.length_singleton, pow_one]
    rw [ih (fun e he ↦ hds e (by simp [he]))]
    simp [Nat.mod_eq_of_lt (hds d (by simp)), Nat.ofDigits, baseWordValue]
    ring

@[simp]
theorem baseDigits_zero {k : ℕ} (hk : 2 ≤ k) : baseDigits hk 0 = [] := by
  simp [baseDigits]

@[simp]
theorem baseWordValue_baseDigits {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    baseWordValue (baseDigits hk n) = n := by
  rw [baseDigits, baseWordValue_reverse_digits hk]
  · exact Nat.ofDigits_digits k n
  · intro d hd
    exact Nat.digits_lt_base (by omega) hd

theorem baseDigits_length {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    (baseDigits hk n).length = (Nat.digits k n).length := by
  simp [baseDigits]

theorem baseDigits_ne_nil {k : ℕ} (hk : 2 ≤ k) {n : ℕ} (hn : n ≠ 0) :
    baseDigits hk n ≠ [] := by
  simp [baseDigits, Nat.digits_eq_nil_iff_eq_zero, hn]

theorem isCanonicalBaseWord_baseDigits {k : ℕ} (hk : 2 ≤ k) (n : ℕ) :
    IsCanonicalBaseWord (baseDigits hk n) := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hd : Nat.digits k n ≠ [] := by
      simpa [Nat.digits_eq_nil_iff_eq_zero] using hn
    have hdr : (Nat.digits k n).reverse ≠ [] := by simpa
    rw [baseDigits]
    cases hrev : (Nat.digits k n).reverse with
    | nil => simp_all
    | cons d ds =>
      simp only [List.map_cons, IsCanonicalBaseWord]
      have hdlast : d = (Nat.digits k n).getLast hd := by
        have := List.head_reverse (l := Nat.digits k n) hdr
        simpa [hrev] using this
      rw [Nat.mod_eq_of_lt (Nat.digits_lt_base (by omega)
        (hdlast.symm ▸ List.getLast_mem hd))]
      simpa [hdlast] using Nat.getLast_digit_ne_zero k hn

end MetaMathlibExt
