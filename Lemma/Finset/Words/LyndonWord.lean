import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Words.LyndonWord
open scoped BigOperators
open MetaMathlibExt


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
[wittWordContent_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/LyndonWord.lean)
-/
@[path]
private lemma wittWordContent_singleton_eq
  {r : ℕ}
  {i : Fin r} :
-- imply
  wittWordContent [i] = Function.update (fun _ => 0) i 1 := by
-- proof
  apply MetaMathlibExt.wittWordContent_singleton i

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
[card_wordsOfContent_eq_multinomial](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/LyndonWord.lean)
-/
@[path]
private lemma card_wordsOfContent_eq_multinomial_eq
  {r : ℕ}
  {degree : Fin r → ℕ} :
-- imply
  Fintype.card (WordsOfContent degree) = Nat.multinomial Finset.univ degree := by
-- proof
  apply MetaMathlibExt.card_wordsOfContent_eq_multinomial degree

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
