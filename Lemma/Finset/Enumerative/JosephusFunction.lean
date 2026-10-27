import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.JosephusFunction
open MetaMathlibExt


namespace MetaMathlibExt

/--
[josephus_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/JosephusFunction.lean)
-/
@[path]
lemma josephus_one
  {k : Nat}
-- given
  (hk : 2 ≤ k) :
-- imply
  josephus k 1 = 1 := by
-- proof
  simp only [josephus]
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[josephus_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/JosephusFunction.lean)
-/
@[path]
lemma josephus_succ
  {k n : Nat}
-- given
  (hk : 2 ≤ k)
  (hn : 1 ≤ n) :
-- imply
  josephus k (n + 1) = ((josephus k n + k - 1) % (n + 1)) + 1 := by
-- proof
  simp only [josephus]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[josephus_range](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/JosephusFunction.lean)
-/
@[path]
lemma josephus_range
  {k n : Nat}
-- given
  (hk : 2 ≤ k)
  (hn : 1 ≤ n) :
-- imply
  1 ≤ josephus k n ∧ josephus k n ≤ n := by
-- proof
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h : josephus k (m + 1) = ((josephus k m + k - 1) % (m + 1)) + 1 := by
    simp only [josephus]
  rw [h]
  constructor
  · omega
  · have hpos : 0 < m + 1 := by omega
    have hmod : (josephus k m + k - 1) % (m + 1) < m + 1 :=
      Nat.mod_lt _ hpos
    omega

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
