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
public import Def.Combinatorics.Enumerative.LuckyParkingFunctions.Part6


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LuckyParkingFunctions.lean -/
section

namespace MetaMathlibExt

lemma plain_no_fixed (n : ℕ) (a : Park n) (k : Fin (n + 1))
    (hpos : 0 < k.val) : (embedPlain n a).1 k ≠ k := by
  intro heq
  have hval : ((embedPlain n a).1 k).val = k.val := congrArg Fin.val heq
  have hne : k.val ≠ 0 := by
    omega
  have hB := plainFun_val_of_ne n a.1 k hne
  have hb := a.2.2 ⟨k.val - 1, by omega⟩
  simp only [embedPlain] at hval hB
  simp only at hb
  omega

end MetaMathlibExt
end
