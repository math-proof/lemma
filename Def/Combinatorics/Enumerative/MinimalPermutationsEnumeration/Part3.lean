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
import Theorem.Combinatorics.Enumerative.MinimalPermutationsEnumeration.Part3


section

namespace MetaMathlibExt

def firstVals (d : ℕ) (σ : Equiv.Perm (Fin (d + 2))) (a : Fin (d + 1)) :
    Finset (Fin (d + 2)) :=
  Finset.image (fun i : Fin (a.val + 1) => σ (block1Pos d a i)) Finset.univ

def secondVals (d : ℕ) (σ : Equiv.Perm (Fin (d + 2))) (a : Fin (d + 1)) :
    Finset (Fin (d + 2)) :=
  Finset.image (fun i : Fin ((d - a.val) + 1) => σ (block2Pos d a i)) Finset.univ

end MetaMathlibExt
end
