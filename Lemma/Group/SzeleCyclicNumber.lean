import Mathlib
import sympy.Basic
import sympy.atlas.GroupTheory.SzeleCyclicNumber
open MetaMathlibExt


/--
[szele_cyclic_number_criterion](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/SzeleCyclicNumber.lean)
-/
@[path]
private lemma szele_cyclic_number_criterion_eq
  {n : ℕ}
-- given
  (hn : 0 < n) :
-- imply
  (∀ (G : Type*) [Group G] [Fintype G], Fintype.card G = n → IsCyclic G) ↔
    Nat.gcd n (Nat.totient n) = 1 := by
-- proof
  apply MetaMathlibExt.szele_cyclic_number_criterion n hn


-- created on 2026-10-20
