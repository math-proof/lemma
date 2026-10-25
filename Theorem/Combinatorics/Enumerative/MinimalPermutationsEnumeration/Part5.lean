/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MinimalPermutationsEnumeration.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Fin.Rev
import Mathlib.Order.Fin.Basic
import Def.Combinatorics.Enumerative.MinimalPermutationsEnumeration.Part4


section

namespace MetaMathlibExt

theorem topSmall_card (d : ℕ) (a : Fin (d + 1)) (hpos : 0 < a.val) :
    (topSmall d a hpos).card = a.val := by
  simp only [topSmall, Fin.card_Ici]
  have ha := a.isLt
  omega

end MetaMathlibExt
end
