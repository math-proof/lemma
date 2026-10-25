/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LunnonDimensionDecomposition.lean -/

import Mathlib.Order.Interval.Finset.Nat
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.Choose.Sum
import Def.Combinatorics.Enumerative.LunnonDimensionDecomposition.Part4


section

namespace MetaMathlibExt

open scoped BigOperators

lemma encodeCell_eq_of_bounds_aux (d n : ℕ) [NeZero n] (x y : latticeCell d)
    (hxb : ∀ k : Fin d, 0 ≤ x k ∧ x k < (n : ℤ))
    (hyb : ∀ k : Fin d, 0 ≤ y k ∧ y k < (n : ℤ))
    (hxy : encodeCell_aux d n x = encodeCell_aux d n y) : x = y := by
  funext k
  have hxyk : (encodeCell_aux d n x) k = (encodeCell_aux d n y) k := by rw [hxy]
  simp only [encodeCell_aux] at hxyk
  have hmod : (x k).toNat % n = (y k).toNat % n := Fin.mk.injEq .. ▸ hxyk
  have h1 : (x k).toNat < n := by
    have h0 := (hxb k).1
    have h2 := (hxb k).2
    have h3 : ((x k).toNat : ℤ) = x k := Int.toNat_of_nonneg h0
    omega
  have h2 : (y k).toNat < n := by
    have h0 := (hyb k).1
    have h3 := (hyb k).2
    have h4 : ((y k).toNat : ℤ) = y k := Int.toNat_of_nonneg h0
    omega
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hmod
  have hxnn := (hxb k).1
  have hynn := (hyb k).1
  have e1 : ((x k).toNat : ℤ) = x k := Int.toNat_of_nonneg hxnn
  have e2 : ((y k).toNat : ℤ) = y k := Int.toNat_of_nonneg hynn
  omega

end MetaMathlibExt
end
