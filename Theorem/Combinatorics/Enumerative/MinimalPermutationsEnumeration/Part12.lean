module
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Data.Fin.Rev
public import Mathlib.Order.Fin.Basic
public import Def.Combinatorics.Enumerative.MinimalPermutationsEnumeration.Part11


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MinimalPermutationsEnumeration.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
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
