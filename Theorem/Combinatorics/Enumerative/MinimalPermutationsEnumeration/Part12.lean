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
import Def.Combinatorics.Enumerative.MinimalPermutationsEnumeration.Part11


section

namespace MetaMathlibExt

theorem mpeAscentPos_spec (d : ℕ) (σ : Equiv.Perm (Fin (d + 2)))
    (hgood : mpeGood d σ) :
    ∃ hpos : 0 < (mpeAscentPos d σ).val,
      (mpeAscentPos d σ).val < d ∧
      (Finset.univ.filter fun i : Fin (d + 1) =>
        σ i.castSucc < σ i.succ) = {mpeAscentPos d σ} ∧
      firstVals d σ (mpeAscentPos d σ) ∉
        exclA d (mpeAscentPos d σ) hpos ∪ exclB d (mpeAscentPos d σ) := by
  unfold mpeAscentPos
  simp only [hgood, ↓reduceDIte]
  exact (mpeGood_forward d σ hgood).choose_spec

end MetaMathlibExt
end
