import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Lists.RaneyCycleLemma
open MetaMathlibExt


/--
[raney_cycle_lemma_sum_neg_one_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Lists/RaneyCycleLemma.lean)
-/
@[path]
private lemma raney_cycle_lemma_sum_neg_one_general_eq
  {a : List Int}
-- given
  (hsum : a.sum = -1) :
-- imply
  ∃! r : Fin a.length, ∀ t : Nat, t < a.length → 0 ≤ ((a.rotate r.val).take t).sum := by
-- proof
  apply MetaMathlibExt.raney_cycle_lemma_sum_neg_one_general a hsum

/--
[raney_cycle_lemma_sum_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Lists/RaneyCycleLemma.lean)
-/
@[path]
private lemma raney_cycle_lemma_sum_neg_one_eq
  {a : List Int}
-- given
  (hlower : ∀ x ∈ a, -1 ≤ x)
  (hsum : a.sum = -1) :
-- imply
  ∃! r : Fin a.length, ∀ t : Nat, t < a.length → 0 ≤ ((a.rotate r.val).take t).sum := by
-- proof
  apply MetaMathlibExt.raney_cycle_lemma_sum_neg_one a hlower hsum


-- created on 2026-10-20
