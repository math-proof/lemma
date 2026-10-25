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
import Theorem.Combinatorics.Enumerative.IdentityProductNecklace.Part3


section

namespace MetaMathlibExt

/-- Fixed points of a rotation are transversal tuples with constrained product. -/
def fixedBy_equiv_gcd (G : Type*) [Group G]
    (n : ℕ) [NeZero n] (k : ZMod n) :
    ↥(AddAction.fixedBy {x : Fin n → G // (List.ofFn x).prod = 1} k)
    ≃ {a : Fin (Nat.gcd n k.val) → G //
      ((List.ofFn a).prod) ^ (n / Nat.gcd n k.val) = 1} := by
  classical
  have hnpos : 0 < n := NeZero.pos n
  have hddpos : 0 < Nat.gcd n k.val := Nat.gcd_pos_of_pos_left _ hnpos
  have hddvd_n : Nat.gcd n k.val ∣ n := Nat.gcd_dvd_left _ _
  have hddvd_k : Nat.gcd n k.val ∣ k.val := Nat.gcd_dvd_right _ _
  have hdn : Nat.gcd n k.val ≤ n := Nat.gcd_le_left _ hnpos
  have hnde : n / Nat.gcd n k.val * Nat.gcd n k.val = n :=
    Nat.div_mul_cancel hddvd_n
  refine ⟨?toFun, ?invFun, ?left_inv, ?right_inv⟩
  · refine fun x => ⟨fun j => x.val.val ⟨j.val, Nat.lt_of_lt_of_le j.isLt hdn⟩,
      ?_⟩
    have hfix : ∀ j : Fin n,
        x.val.val ⟨(j.val + k.val) % n, Nat.mod_lt _ hnpos⟩ = x.val.val j := by
      have hkeq : k +ᵥ x.val = x.val := x.prop
      exact fun j => congrFun (congrArg Subtype.val hkeq) j
    have hshape : ∀ i : Fin n, x.val.val i
        = (fun j : Fin (Nat.gcd n k.val) =>
          x.val.val ⟨j.val, Nat.lt_of_lt_of_le j.isLt hdn⟩)
          ⟨i.val % Nat.gcd n k.val, Nat.mod_lt _ hddpos⟩ := by
      intro i
      change x.val.val i = x.val.val ⟨(i.val % Nat.gcd n k.val : ℕ), _⟩
      exact path_lemma G n k x.val.val hfix i
    have hblock := block_prod G (Nat.gcd n k.val) hddpos (n / Nat.gcd n k.val)
      (fun j : Fin (Nat.gcd n k.val) =>
        x.val.val ⟨j.val, Nat.lt_of_lt_of_le j.isLt hdn⟩)
      n x.val.val hnde hshape
    rw [← hblock]
    exact x.val.prop
  · refine fun a => ⟨⟨fun i : Fin n =>
      a.val ⟨i.val % Nat.gcd n k.val, Nat.mod_lt _ hddpos⟩, ?_⟩, ?_⟩
    · have hshape2 : ∀ i : Fin n,
          (fun i : Fin n => a.val ⟨i.val % Nat.gcd n k.val, Nat.mod_lt _ hddpos⟩)
            i = a.val ⟨i.val % Nat.gcd n k.val, Nat.mod_lt _ hddpos⟩ :=
        fun i => rfl
      have hblock2 := block_prod G _ hddpos _ a.val n _ hnde hshape2
      rw [hblock2]
      exact a.prop
    · apply Subtype.ext
      funext i
      change a.val ⟨((i.val + k.val) % n) % Nat.gcd n k.val, _⟩
        = a.val ⟨i.val % Nat.gcd n k.val, _⟩
      exact congrArg a.val
        (Fin.ext (mod_shift_eq i.val k.val _ n hddvd_n hddvd_k))
  · intro x
    have hfix : ∀ j : Fin n,
        x.val.val ⟨(j.val + k.val) % n, Nat.mod_lt _ hnpos⟩ = x.val.val j := by
      have hkeq : k +ᵥ x.val = x.val := x.prop
      exact fun j => congrFun (congrArg Subtype.val hkeq) j
    apply Subtype.ext
    apply Subtype.ext
    funext i
    change x.val.val ⟨(i.val % Nat.gcd n k.val : ℕ), _⟩ = x.val.val i
    exact (path_lemma G n k x.val.val hfix i).symm
  · intro a
    apply Subtype.ext
    funext j
    change ((fun j : Fin (Nat.gcd n k.val) => (fun i : Fin n =>
      a.val ⟨i.val % Nat.gcd n k.val, Nat.mod_lt _ hddpos⟩)
      ⟨j.val, Nat.lt_of_lt_of_le j.isLt hdn⟩)) j = a.val j
    have hmod : j.val % Nat.gcd n k.val = j.val := Nat.mod_eq_of_lt j.isLt
    change a.val ⟨j.val % Nat.gcd n k.val, _⟩ = a.val j
    exact congrArg a.val (Fin.ext hmod)

end MetaMathlibExt
end
