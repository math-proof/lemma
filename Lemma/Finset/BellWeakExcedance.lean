import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.BellWeakExcedance
open MetaMathlibExt


/--
[bell_count_perm_increasing_weakExcedance_letters](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/BellWeakExcedance.lean)
-/
@[path]
private lemma bell_count_perm_increasing_weakExcedance_letters_eq
  {n : ℕ} :
-- imply
  Fintype.card { σ : Equiv.Perm (Fin n) //
    ∀ i j : Fin n, i < j → i ≤ σ i → j ≤ σ j → σ i < σ j } = Nat.bell n := by
-- proof
  apply MetaMathlibExt.bell_count_perm_increasing_weakExcedance_letters n


-- created on 2026-10-20
