import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.BaseRecognizable
open MetaMathlibExt


namespace MetaMathlibExt

/--
[baseWordValue_nil](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BaseRecognizable.lean)
-/
@[path]
lemma baseWordValue_nil
  {k : ℕ} :
-- imply
  baseWordValue ([] : List (Fin k)) = 0 :=
-- proof
  rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[foldl_baseValue](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BaseRecognizable.lean)
-/
@[path]
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

end MetaMathlibExt

namespace MetaMathlibExt

/--
[baseWordValue_append](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BaseRecognizable.lean)
-/
@[path]
lemma baseWordValue_append
  {k : ℕ}
  {u v : List (Fin k)} :
-- imply
  baseWordValue (u ++ v) =
    baseWordValue u * k ^ v.length + baseWordValue v := by
-- proof
  simp only [baseWordValue, List.foldl_append]
  exact foldl_baseValue v _

end MetaMathlibExt

namespace MetaMathlibExt

/--
[isCanonicalBaseWord_nil](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BaseRecognizable.lean)
-/
@[path]
lemma isCanonicalBaseWord_nil
  {k : ℕ} :
-- imply
  IsCanonicalBaseWord ([] : List (Fin k)) :=
-- proof
  trivial

end MetaMathlibExt

namespace MetaMathlibExt

/--
[isCanonicalBaseWord_cons](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BaseRecognizable.lean)
-/
@[path]
lemma isCanonicalBaseWord_cons
  {k : ℕ}
  {d : Fin k}
  {w : List (Fin k)} :
-- imply
  IsCanonicalBaseWord (d :: w) ↔ d.val ≠ 0 :=
-- proof
  Iff.rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[IsCanonicalBaseWord.append](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BaseRecognizable.lean)
-/
@[path]
lemma IsCanonicalBaseWord.append
  {k : ℕ}
  {u v : List (Fin k)}
-- given
  (hu : IsCanonicalBaseWord u)
  (hne : u ≠ []) :
-- imply
  IsCanonicalBaseWord (u ++ v) := by
-- proof
  cases u with
  | nil => contradiction
  | cons d u => simpa [IsCanonicalBaseWord] using hu

end MetaMathlibExt

namespace MetaMathlibExt

/--
[baseWordValue_reverse_digits](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BaseRecognizable.lean)
-/
@[path]
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

end MetaMathlibExt

namespace MetaMathlibExt

/--
[baseDigits_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BaseRecognizable.lean)
-/
@[path]
lemma baseDigits_zero
  {k : ℕ}
-- given
  (hk : 2 ≤ k) :
-- imply
  baseDigits hk 0 = [] := by
-- proof
  simp [baseDigits]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[baseWordValue_baseDigits](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BaseRecognizable.lean)
-/
@[path]
lemma baseWordValue_baseDigits
  {k n : ℕ}
-- given
  (hk : 2 ≤ k) :
-- imply
  baseWordValue (baseDigits hk n) = n := by
-- proof
  rw [baseDigits, baseWordValue_reverse_digits hk]
  · exact Nat.ofDigits_digits k n
  · intro d hd
    exact Nat.digits_lt_base (by omega) hd

end MetaMathlibExt

namespace MetaMathlibExt

/--
[baseDigits_length](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BaseRecognizable.lean)
-/
@[path]
lemma baseDigits_length
  {k n : ℕ}
-- given
  (hk : 2 ≤ k) :
-- imply
  (baseDigits hk n).length = (Nat.digits k n).length := by
-- proof
  simp [baseDigits]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[baseDigits_ne_nil](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BaseRecognizable.lean)
-/
@[path]
lemma baseDigits_ne_nil
  {k n : ℕ}
-- given
  (hk : 2 ≤ k)
  (hn : n ≠ 0) :
-- imply
  baseDigits hk n ≠ [] := by
-- proof
  simp [baseDigits, Nat.digits_eq_nil_iff_eq_zero, hn]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[isCanonicalBaseWord_baseDigits](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BaseRecognizable.lean)
-/
@[path]
lemma isCanonicalBaseWord_baseDigits
  {k n : ℕ}
-- given
  (hk : 2 ≤ k) :
-- imply
  IsCanonicalBaseWord (baseDigits hk n) := by
-- proof
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

/--
[on](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BaseRecognizable.lean)
-/
@[path]
private lemma on_eq
  {k : ℕ} :
-- imply
  baseWordValue ([] : List (Fin k)) = 0 := by
-- proof
  apply on


-- created on 2026-10-20
-- updated on 2026-10-26
