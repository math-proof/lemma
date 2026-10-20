/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/GeneralPosition.lean -/

import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.LinearAlgebra.Projectivization.Independence

/-!
# General position

This file defines general position for indexed families of points in affine and projective spaces.
A family is in general position through dimension `d` when each subfamily of at most `d + 1`
points is independent.
-/

noncomputable section

open Function
open scoped Affine LinearAlgebra.Projectivization

universe u v w

variable {k : Type u} {V : Type v} {P : Type w} {ι ι' : Type*}

section Affine

/-- An indexed family of affine points is in general position through dimension `d` if every
subfamily of at most `d + 1` points is affinely independent. -/
def IsGeneralPosition (k : Type u) [DivisionRing k] {V : Type v} {P : Type w} [AddCommGroup V]
    [Module k V] [AffineSpace V P] {ι : Type*} (d : ℕ) (p : ι → P) : Prop :=
  ∀ s : Finset ι, s.card ≤ d + 1 → AffineIndependent k (s.restrict p)

variable [DivisionRing k] [AddCommGroup V] [Module k V] [AffineSpace V P]

/-- An affinely independent family is in general position in every dimension. -/
theorem AffineIndependent.isGeneralPosition {p : ι → P} (hp : AffineIndependent k p) (d : ℕ) :
    IsGeneralPosition k d p :=
  fun s _ ↦ hp.subtype s

/-- General position through a larger dimension implies general position through a smaller one. -/
theorem IsGeneralPosition.mono {d e : ℕ} {p : ι → P} (hp : IsGeneralPosition k e p)
    (hde : d ≤ e) : IsGeneralPosition k d p :=
  fun s hs ↦ hp s (hs.trans (Nat.add_le_add_right hde 1))

section Examples

/-- The empty family is in general position in every dimension. -/
example (p : Empty → P) (d : ℕ) : IsGeneralPosition k d p :=
  (affineIndependent_of_subsingleton k p).isGeneralPosition d

/-- Two distinct affine points are in general position through dimension one. -/
example (p q : P) (hpq : p ≠ q) : IsGeneralPosition k 1 ![p, q] :=
  (affineIndependent_of_ne k hpq).isGeneralPosition 1

end Examples

end Affine

namespace Projectivization

/-- An indexed family of projective points is in general position through dimension `d` if every
subfamily of at most `d + 1` points is projectively independent. -/
def IsGeneralPosition {k : Type u} [DivisionRing k] {V : Type v} [AddCommGroup V] [Module k V]
    {ι : Type*} (d : ℕ) (p : ι → ℙ k V) : Prop :=
  ∀ s : Finset ι, s.card ≤ d + 1 → Independent (s.restrict p)

variable [DivisionRing k] [AddCommGroup V] [Module k V]

/-- A projectively independent family is in general position in every dimension. -/
theorem Independent.isGeneralPosition {p : ι → ℙ k V} (hp : Independent p) (d : ℕ) :
    IsGeneralPosition d p := by
  intro s _
  rw [independent_iff] at hp ⊢
  simpa [Finset.restrict_def, Function.comp_def] using
    hp.comp (fun i : s ↦ (i : ι)) Subtype.val_injective

/-- General position through a larger dimension implies general position through a smaller one. -/
theorem IsGeneralPosition.mono {d e : ℕ} {p : ι → ℙ k V} (hp : IsGeneralPosition e p)
    (hde : d ≤ e) : IsGeneralPosition d p :=
  fun s hs ↦ hp s (hs.trans (Nat.add_le_add_right hde 1))

section Examples

/-- Two distinct projective points are in general position through dimension one. -/
example (p q : ℙ k V) (hpq : p ≠ q) : IsGeneralPosition 1 ![p, q] :=
  ((independent_pair_iff_ne p q).2 hpq).isGeneralPosition 1

end Examples

end Projectivization
