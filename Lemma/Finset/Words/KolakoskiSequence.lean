import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Words.KolakoskiSequence
open MetaMathlibExt
open IsKolakoski


namespace MetaMathlibExt.IsKolakoski

/--
[one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/KolakoskiSequence.lean)
-/
@[path]
lemma one
  {K : ℕ → ℕ}
-- given
  (h : IsKolakoski K) :
-- imply
  K 1 = 1 :=
-- proof
  h.1

end MetaMathlibExt.IsKolakoski

namespace MetaMathlibExt.IsKolakoski

/--
[value_eq_one_or_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/KolakoskiSequence.lean)
-/
@[path]
lemma value_eq_one_or_two
  {K : ℕ → ℕ}
  {n : ℕ}
-- given
  (h : IsKolakoski K)
  (hn : 1 ≤ n) :
-- imply
  K n = 1 ∨ K n = 2 :=
-- proof
  h.2.1 n hn

end MetaMathlibExt.IsKolakoski

namespace MetaMathlibExt.IsKolakoski

/--
[eq_on_block](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/KolakoskiSequence.lean)
-/
@[path]
lemma eq_on_block
  {K : ℕ → ℕ}
  {n i : ℕ}
-- given
  (h : IsKolakoski K)
  (hn : 1 ≤ n)
  (hstart : kolakoskiBlockStart K n ≤ i)
  (hend : i < kolakoskiBlockStart K n + K n) :
-- imply
  K i = if n % 2 = 1 then 1 else 2 :=
-- proof
  h.2.2 n hn i hstart hend

end MetaMathlibExt.IsKolakoski

namespace MetaMathlibExt.IsKolakoski

/--
[two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/KolakoskiSequence.lean)
-/
@[path]
lemma two
  {K : ℕ → ℕ}
-- given
  (h : IsKolakoski K) :
-- imply
  K 2 = 2 := by
-- proof
  have hpositive : 0 < K 2 := by
    obtain hK | hK <;> simp [hK] := h.value_eq_one_or_two (n := 2) (by decide)
  have hblock := h.eq_on_block (n := 2) (i := kolakoskiBlockStart K 2)
    (by decide) le_rfl (Nat.lt_add_of_pos_right hpositive)
  simpa [kolakoskiBlockStart, h.one] using hblock

end MetaMathlibExt.IsKolakoski

namespace MetaMathlibExt.IsKolakoski

/--
[three](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/KolakoskiSequence.lean)
-/
@[path]
lemma three
  {K : ℕ → ℕ}
-- given
  (h : IsKolakoski K) :
-- imply
  K 3 = 2 := by
-- proof
  have hblock := h.eq_on_block (n := 2) (i := 3) (by decide)
    (by simp [kolakoskiBlockStart, h.one])
    (by simp [kolakoskiBlockStart, h.one, h.two])
  simpa using hblock

end MetaMathlibExt.IsKolakoski

namespace MetaMathlibExt.IsKolakoski

/--
[four](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/KolakoskiSequence.lean)
-/
@[path]
lemma four
  {K : ℕ → ℕ}
-- given
  (h : IsKolakoski K) :
-- imply
  K 4 = 1 := by
-- proof
  have hblock := h.eq_on_block (n := 3) (i := 4) (by decide)
    (by simp [kolakoskiBlockStart, h.one, h.two])
    (by simp [kolakoskiBlockStart, h.one, h.two, h.three])
  simpa using hblock

end MetaMathlibExt.IsKolakoski


-- created on 2026-10-20
-- updated on 2026-10-26
