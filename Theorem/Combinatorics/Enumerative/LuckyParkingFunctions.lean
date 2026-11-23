/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LuckyParkingFunctions.lean -/
module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Rat.Star
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Instance.Combinatorics.Enumerative.LuckyParkingFunctions.Part2

public section

section

namespace MetaMathlibExt

lemma park_zero_val (m : ℕ) (a : Park m) (hm : 0 < m) :
    (a.1 ⟨0, hm⟩).val = 0 := by
  have h := a.2.2 ⟨0, hm⟩
  simp only at h
  omega

end MetaMathlibExt
end
