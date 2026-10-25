/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/IdentityProductNecklace.lean -/

import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Torsor.Defs
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.IdentityProductNecklace


section

namespace MetaMathlibExt

/-- Modular arithmetic helper for shift composition. -/
lemma mod_add_wrap (i a b n : ℕ) : (i + (a + b) % n) % n = ((i + a) % n + b) % n := by
  have e1 : (i + (a + b) % n) % n = (i + (a + b)) % n := by
    conv_lhs => rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  have e2 : ((i + a) % n + b) % n = ((i + a) + b) % n := by
    conv_lhs => rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  have hassoc : i + (a + b) = (i + a) + b := by ring
  rw [e1, e2, hassoc]

lemma rotShift_zero (G : Type*)
    (n : ℕ) [NeZero n] (x : Fin n → G) : rotShift G n 0 x = x := by
  funext i
  have hval : (i.val + (0 : ZMod n).val) % n = i.val := by
    rw [ZMod.val_zero, Nat.add_zero, Nat.mod_eq_of_lt i.isLt]
  change x ⟨(i.val + (0 : ZMod n).val) % n, _⟩ = x i
  exact congrArg x (Fin.ext hval)

lemma rotShift_add (G : Type*)
    (n : ℕ) [NeZero n] (k l : ZMod n) (x : Fin n → G) :
    rotShift G n (k + l) x = rotShift G n k (rotShift G n l x) := by
  funext i
  have hval : (i.val + (k + l).val) % n
      = (((i.val + k.val) % n) + l.val) % n := by
    rw [ZMod.val_add]
    exact mod_add_wrap i.val k.val l.val n
  change x ⟨(i.val + (k + l).val) % n, _⟩
    = x ⟨(((i.val + k.val) % n) + l.val) % n, _⟩
  exact congrArg x (Fin.ext hval)

/-- The rotated tuple, as a list, is `drop ++ take`. -/
lemma rotShift_list_eq (G : Type*)
    (n : ℕ) [NeZero n] (k : ZMod n) (x : Fin n → G) :
    List.ofFn (rotShift G n k x)
      = (List.ofFn x).drop k.val ++ (List.ofFn x).take k.val := by
  have hkle : k.val ≤ n := Nat.le_of_lt (ZMod.val_lt k)
  have hnpos : 0 < n := NeZero.pos n
  refine List.ext_getElem ?_ ?_
  · rw [List.length_ofFn, List.length_append, List.length_drop, List.length_take,
      List.length_ofFn, Nat.min_eq_left hkle, Nat.sub_add_cancel hkle]
  · intro j h1 h2
    have h1n : j < n := by simpa [List.length_ofFn] using h1
    have hLHS : (List.ofFn (rotShift G n k x))[j]'h1
        = x ⟨(j + k.val) % n, Nat.mod_lt _ hnpos⟩ :=
      List.getElem_ofFn h1
    rw [hLHS]
    by_cases hj : j < ((List.ofFn x).drop k.val).length
    · have hjlt : j < n - k.val := by
        simpa [List.length_drop, List.length_ofFn] using hj
      rw [List.getElem_append_left hj, List.getElem_drop, List.getElem_ofFn]
      have hlt : j + k.val < n := by omega
      have hmod : (j + k.val) % n = k.val + j := by
        rw [Nat.mod_eq_of_lt hlt]; omega
      change x ⟨(j + k.val) % n, _⟩ = x ⟨k.val + j, _⟩
      exact congrArg x (Fin.ext hmod)
    · have hdrop : ((List.ofFn x).drop k.val).length = n - k.val := by
        rw [List.length_drop, List.length_ofFn]
      have hle : ((List.ofFn x).drop k.val).length ≤ j := not_lt.mp hj
      rw [List.getElem_append_right hle, List.getElem_take, List.getElem_ofFn]
      have hmod : (j + k.val) % n = j - ((List.ofFn x).drop k.val).length := by
        have h2n : j < n := by
          have hlen : ((List.ofFn x).drop k.val
            ++ (List.ofFn x).take k.val).length = n := by
            rw [List.length_append, hdrop, List.length_take, List.length_ofFn,
              Nat.min_eq_left hkle, Nat.sub_add_cancel hkle]
          omega
        have heq : j + k.val = n + (j - ((List.ofFn x).drop k.val).length) := by
          omega
        have hlt2 : j - ((List.ofFn x).drop k.val).length < n := by omega
        rw [heq, Nat.add_comm n _, Nat.add_mod_right, Nat.mod_eq_of_lt hlt2]
      change x ⟨(j + k.val) % n, _⟩ = x ⟨j - ((List.ofFn x).drop k.val).length, _⟩
      exact congrArg x (Fin.ext hmod)

/-- Rotation preserves the identity-product property (rotated product is conjugate). -/
lemma rotShift_prod_eq_one (G : Type*) [Group G]
    (n : ℕ) [NeZero n] (k : ZMod n) (x : Fin n → G) :
    (List.ofFn (rotShift G n k x)).prod = 1 ↔ (List.ofFn x).prod = 1 := by
  have hcomm : ∀ a b : G, a * b = 1 ↔ b * a = 1 := by
    intro a b
    constructor
    · intro h
      have h1 : a = b⁻¹ := eq_inv_of_mul_eq_one_left h
      rw [h1, mul_inv_cancel]
    · intro h
      have h1 : b = a⁻¹ := eq_inv_of_mul_eq_one_left h
      rw [h1, mul_inv_cancel]
  have hPx : (List.ofFn x).prod
      = ((List.ofFn x).take k.val).prod * ((List.ofFn x).drop k.val).prod := by
    conv_lhs => rw [← List.take_append_drop k.val (List.ofFn x), List.prod_append]
  rw [rotShift_list_eq G n k x, List.prod_append, hPx]
  exact hcomm _ _

end MetaMathlibExt
end
