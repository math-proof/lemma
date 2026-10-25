/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LuckyParkingFunctions.lean -/

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Rat.Star
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.LuckyParkingFunctions.Part6


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
