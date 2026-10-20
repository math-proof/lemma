import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.BaseRecognizable
open MetaMathlibExt


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

/--
[baseWordValue_nil](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BaseRecognizable.lean)
-/
@[path]
private lemma baseWordValue_nil_eq
  {k : ℕ} :
-- imply
  baseWordValue ([] : List (Fin k)) = 0 := by
-- proof
  apply MetaMathlibExt.baseWordValue_nil

/--
[baseWordValue_append](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BaseRecognizable.lean)
-/
@[path]
private lemma baseWordValue_append_eq
  {k : ℕ}
  {u v : List (Fin k)} :
-- imply
  baseWordValue (u ++ v) =
    baseWordValue u * k ^ v.length + baseWordValue v := by
-- proof
  apply MetaMathlibExt.baseWordValue_append u v

/--
[isCanonicalBaseWord_nil](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BaseRecognizable.lean)
-/
@[path]
private lemma isCanonicalBaseWord_nil_eq
  {k : ℕ} :
-- imply
  IsCanonicalBaseWord ([] : List (Fin k)) := by
-- proof
  apply MetaMathlibExt.isCanonicalBaseWord_nil

/--
[isCanonicalBaseWord_cons](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BaseRecognizable.lean)
-/
@[path]
private lemma isCanonicalBaseWord_cons_eq
  {k : ℕ}
  {d : Fin k}
  {w : List (Fin k)} :
-- imply
  IsCanonicalBaseWord (d :: w) ↔ d.val ≠ 0 := by
-- proof
  apply MetaMathlibExt.isCanonicalBaseWord_cons d w

/--
[IsCanonicalBaseWord.append](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BaseRecognizable.lean)
-/
@[path]
private lemma IsCanonicalBaseWord_append_eq
  {k : ℕ}
  {u v : List (Fin k)}
-- given
  (hu : IsCanonicalBaseWord u)
  (hne : u ≠ []) :
-- imply
  IsCanonicalBaseWord (u ++ v) := by
-- proof
  apply MetaMathlibExt.IsCanonicalBaseWord.append hu hne

/--
[baseDigits_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BaseRecognizable.lean)
-/
@[path]
private lemma baseDigits_zero_eq
  {k : ℕ}
-- given
  (hk : 2 ≤ k) :
-- imply
  baseDigits hk 0 = [] := by
-- proof
  apply MetaMathlibExt.baseDigits_zero hk

/--
[baseWordValue_baseDigits](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BaseRecognizable.lean)
-/
@[path]
private lemma baseWordValue_baseDigits_eq
  {k n : ℕ}
-- given
  (hk : 2 ≤ k) :
-- imply
  baseWordValue (baseDigits hk n) = n := by
-- proof
  apply MetaMathlibExt.baseWordValue_baseDigits hk n

/--
[baseDigits_length](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BaseRecognizable.lean)
-/
@[path]
private lemma baseDigits_length_eq
  {k n : ℕ}
-- given
  (hk : 2 ≤ k) :
-- imply
  (baseDigits hk n).length = (Nat.digits k n).length := by
-- proof
  apply MetaMathlibExt.baseDigits_length hk n

/--
[baseDigits_ne_nil](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BaseRecognizable.lean)
-/
@[path]
private lemma baseDigits_ne_nil_eq
  {k n : ℕ}
-- given
  (hk : 2 ≤ k)
  (hn : n ≠ 0) :
-- imply
  baseDigits hk n ≠ [] := by
-- proof
  apply MetaMathlibExt.baseDigits_ne_nil hk hn

/--
[isCanonicalBaseWord_baseDigits](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BaseRecognizable.lean)
-/
@[path]
private lemma isCanonicalBaseWord_baseDigits_eq
  {k n : ℕ}
-- given
  (hk : 2 ≤ k) :
-- imply
  IsCanonicalBaseWord (baseDigits hk n) := by
-- proof
  apply MetaMathlibExt.isCanonicalBaseWord_baseDigits hk n


-- created on 2026-10-20
