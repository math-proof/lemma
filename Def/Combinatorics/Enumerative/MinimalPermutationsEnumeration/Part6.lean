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
import Theorem.Combinatorics.Enumerative.MinimalPermutationsEnumeration.Part6


section

namespace MetaMathlibExt

def mpeGood (d : ℕ) (σ : Equiv.Perm (Fin (d + 2))) : Prop :=
  (Finset.univ.filter fun i : Fin (d + 1) =>
    σ i.castSucc > σ i.succ).card = d ∧
  ∀ j : Fin (d + 2),
    (Finset.univ.filter fun i : Fin d =>
      σ (j.succAbove i.castSucc) > σ (j.succAbove i.succ)).card < d

end MetaMathlibExt
end
