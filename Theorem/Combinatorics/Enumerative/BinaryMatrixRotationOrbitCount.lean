/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/BinaryMatrixRotationOrbitCount.lean -/
module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Nat.Totient
public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.Combinatorics.Colex
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Tactic.Abel

public section

namespace MetaMathlibExt

open scoped BigOperators

/-- Invariance of a `Bool`-valued function under adding `g` extends to all integer
multiples of `g`. -/
theorem inv_zsmul {G : Type*} [AddCommGroup G] (g : G) (f : G → Bool)
    (hf : ∀ x, f (x + g) = f x) : ∀ (k : ℤ) (x : G), f (x + k • g) = f x := by
  have hneg : ∀ x, f (x - g) = f x := by
    intro x; have := hf (x - g); simpa using this.symm
  intro k
  induction k using Int.induction_on with
  | zero => intro x; simp
  | succ k ih =>
      intro x
      have h1 : x + ((k : ℤ) + 1) • g = (x + (k : ℤ) • g) + g := by rw [add_one_zsmul]; abel
      rw [h1, hf]; exact ih x
  | pred k ih =>
      intro x
      have h1 : x + (-(k : ℤ) - 1) • g = (x + (-(k : ℤ)) • g) - g := by rw [sub_one_zsmul]; abel
      rw [h1, hneg]; exact ih x

end MetaMathlibExt
