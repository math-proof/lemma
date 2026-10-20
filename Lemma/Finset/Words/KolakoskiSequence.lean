import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Words.KolakoskiSequence
open MetaMathlibExt
open IsKolakoski


/--
[one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/KolakoskiSequence.lean)
-/
@[path]
private lemma one_eq
  {K : ℕ → ℕ}
-- given
  (h : IsKolakoski K) :
-- imply
  K 1 = 1 := by
-- proof
  apply MetaMathlibExt.IsKolakoski.one h

/--
[value_eq_one_or_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/KolakoskiSequence.lean)
-/
@[path]
private lemma value_eq_one_or_two_eq
  {K : ℕ → ℕ}
  {n : ℕ}
-- given
  (h : IsKolakoski K)
  (hn : 1 ≤ n) :
-- imply
  K n = 1 ∨ K n = 2 := by
-- proof
  apply MetaMathlibExt.IsKolakoski.value_eq_one_or_two h hn

/--
[eq_on_block](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/KolakoskiSequence.lean)
-/
@[path]
private lemma eq_on_block_eq
  {K : ℕ → ℕ}
  {n i : ℕ}
-- given
  (h : IsKolakoski K)
  (hn : 1 ≤ n)
  (hstart : kolakoskiBlockStart K n ≤ i)
  (hend : i < kolakoskiBlockStart K n + K n) :
-- imply
  K i = if n % 2 = 1 then 1 else 2 := by
-- proof
  apply MetaMathlibExt.IsKolakoski.eq_on_block h hn hstart hend

/--
[two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/KolakoskiSequence.lean)
-/
@[path]
private lemma two_eq
  {K : ℕ → ℕ}
-- given
  (h : IsKolakoski K) :
-- imply
  K 2 = 2 := by
-- proof
  apply MetaMathlibExt.IsKolakoski.two h

/--
[three](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/KolakoskiSequence.lean)
-/
@[path]
private lemma three_eq
  {K : ℕ → ℕ}
-- given
  (h : IsKolakoski K) :
-- imply
  K 3 = 2 := by
-- proof
  apply MetaMathlibExt.IsKolakoski.three h

/--
[four](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/KolakoskiSequence.lean)
-/
@[path]
private lemma four_eq
  {K : ℕ → ℕ}
-- given
  (h : IsKolakoski K) :
-- imply
  K 4 = 1 := by
-- proof
  apply MetaMathlibExt.IsKolakoski.four h


-- created on 2026-10-20
