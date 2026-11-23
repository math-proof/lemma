module

public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.AdicCompletion.RingHom
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Algebra.Group.Subgroup.Finite

@[expose] public section

def TateModule (p : ℕ) (M : Type) [AddCommGroup M] : AddSubgroup (ℕ → M) where
  carrier := {x | ∀ n, ((p ^ n : ℕ) : ℤ) • x n = 0 ∧ ((p : ℕ) : ℤ) • x (n + 1) = x n}
  add_mem' := fun {x y} hx hy n =>
    ⟨by rw [Pi.add_apply, smul_add, (hx n).1, (hy n).1, add_zero],
     by rw [Pi.add_apply, Pi.add_apply, smul_add, (hx n).2, (hy n).2]⟩
  zero_mem' := fun n => ⟨smul_zero _, by rw [Pi.zero_apply, Pi.zero_apply, smul_zero]⟩
  neg_mem' := fun {x} hx n =>
    ⟨by rw [Pi.neg_apply, smul_neg, (hx n).1, neg_zero],
     by rw [Pi.neg_apply, Pi.neg_apply, smul_neg, (hx n).2]⟩

end
