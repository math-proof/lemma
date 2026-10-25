/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.GroupTheory.Perm.Fin
import Def.Combinatorics.Enumerative.Stirling.Part4
import Lemma.Finset.Enumerative.Stirling
import Structure.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part3
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

theorem zagMarkedTriple_heq_of_toFinset {n : ℕ}
    {e π e' π' : Equiv.Perm (Fin n)} {m : ZagMarkedTriple e π}
    {m' : ZagMarkedTriple e' π'} (he : e = e') (hπ : π = π')
    (hset : m.toFinset = m'.toFinset) : HEq m m' := by
  subst e'
  subst π'
  apply heq_of_eq
  apply (zagMarkedTripleEquivPowerset e π).injective
  apply Subtype.ext
  exact hset

theorem zagMarkedTriple_heq_of_fields {n : ℕ}
    {e π e' π' : Equiv.Perm (Fin n)} {m : ZagMarkedTriple e π}
    {m' : ZagMarkedTriple e' π'} (he : e = e') (hπ : π = π')
    (hfirst : m.first = m'.first) (hmiddle : m.middle = m'.middle)
    (hthird : m.third = m'.third) : HEq m m' := by
  subst e'
  subst π'
  apply heq_of_eq
  exact zagMarkedTriple_ext hfirst hmiddle hthird

theorem zagMarkedPlane_ext {n : ℕ} {p q : ZagMarkedPlane n}
    (horder : p.order = q.order) (hvertical : p.vertical = q.vertical)
    (hmarked : HEq p.marked q.marked) : p = q := by
  cases p
  cases q
  simp_all

end MetaMathlibExt
