import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.Nontrivial1234_3412Classes
open MetaMathlibExt


/--
[card_nontrivial_1234_3412_classes](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean)
-/
@[path]
private lemma card_nontrivial_1234_3412_classes_eq
  :
-- imply
  ∀ (n : ℕ), 7 ≤ n →
    let OneMove : Equiv.Perm (Fin n) → Equiv.Perm (Fin n) → Prop := by
-- proof
  apply MetaMathlibExt.card_nontrivial_1234_3412_classes


-- created on 2026-10-20
