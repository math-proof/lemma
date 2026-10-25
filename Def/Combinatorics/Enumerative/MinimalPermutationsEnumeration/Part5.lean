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
import Theorem.Combinatorics.Enumerative.MinimalPermutationsEnumeration.Part5


section

namespace MetaMathlibExt

def exclA (d : ℕ) (a : Fin (d + 1)) (hpos : 0 < a.val) :
    Finset (Finset (Fin (d + 2))) :=
  (Finset.powersetCard (a.val + 1) Finset.univ).filter
    (fun L => topSmall d a hpos ⊆ L)

def exclB (d : ℕ) (a : Fin (d + 1)) :
    Finset (Finset (Fin (d + 2))) :=
  (Finset.powersetCard (a.val + 1) Finset.univ).filter
    (fun L => L ⊆ topLarge d a)

end MetaMathlibExt
end
