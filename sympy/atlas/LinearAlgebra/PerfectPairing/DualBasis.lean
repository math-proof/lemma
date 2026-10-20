/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/PerfectPairing/DualBasis.lean -/

import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.PerfectPairing.Basic

open Module

/-!
# Dual bases for perfect pairings

Given a perfect pairing `B : M →ₗ[A] N →ₗ[A] A` between `A`-modules `M`
and `N`, and a basis `b` of `N` indexed by a finite decidable type, the
canonical left dual basis is obtained by transporting the ordinary dual
basis along the inverse of the pairing equivalence.

## Main definitions

* `LinearMap.IsPerfPair.dualBasis`: the canonical left dual basis,
  `b.dualBasis.map B.toPerfPair.symm`.

## Main results

* `LinearMap.IsPerfPair.dualBasis_apply`: evaluation formula
  `B (dualBasis B b i) (b j) = if j = i then 1 else 0`.
* `LinearMap.IsPerfPair.eq_dualBasis_of`: uniqueness of any basis
  satisfying that formula.
* `LinearMap.IsPerfPair.exists_dualBasis` and
  `LinearMap.IsPerfPair.existsUnique_dualBasis`: existence and unique
  existence wrappers.
-/

namespace LinearMap.IsPerfPair

variable {A M N ι : Type*} [CommRing A] [AddCommGroup M] [Module A M]
  [AddCommGroup N] [Module A N]
variable [DecidableEq ι] [Finite ι]
variable (B : M →ₗ[A] N →ₗ[A] A) [B.IsPerfPair]

/-- The canonical left dual basis of `b` with respect to the perfect pairing
`B`: transport the ordinary dual basis `b.dualBasis` along the inverse of
the pairing equivalence `B.toPerfPair`. -/
noncomputable def dualBasis (b : Basis ι A N) : Basis ι A M :=
  b.dualBasis.map B.toPerfPair.symm

/-- Evaluation formula for the canonical left dual basis. -/
@[simp]
theorem dualBasis_apply (b : Basis ι A N) (i j : ι) :
    B (dualBasis B b i) (b j) = if j = i then 1 else 0 := by
  rw [dualBasis, Basis.map_apply, ← LinearMap.toPerfPair_apply,
    LinearEquiv.apply_symm_apply, Basis.dualBasis_apply_self]

/-- Uniqueness: any basis satisfying the dual evaluation formula against
`b` coincides with the canonical left dual basis. -/
theorem eq_dualBasis_of (b : Basis ι A N) (b' : Basis ι A M)
    (h : ∀ i j, B (b' i) (b j) = if j = i then 1 else 0) :
    b' = dualBasis B b := by
  refine Basis.eq_of_apply_eq fun i => ?_
  have key : B.toPerfPair (b' i) = b.dualBasis i := by
    apply b.ext
    intro j
    rw [LinearMap.toPerfPair_apply, h i j, b.dualBasis_apply_self]
  calc b' i = B.toPerfPair.symm (B.toPerfPair (b' i)) :=
        (B.toPerfPair.symm_apply_apply (b' i)).symm
    _ = B.toPerfPair.symm (b.dualBasis i) := by rw [key]
    _ = dualBasis B b i := by simp only [dualBasis, Basis.map_apply]

/-- Existence of a basis of `M` dual to `b` with respect to `B`. -/
theorem exists_dualBasis (b : Basis ι A N) :
    ∃ b' : Basis ι A M, ∀ i j, B (b' i) (b j) = if j = i then 1 else 0 :=
  ⟨dualBasis B b, fun i j => dualBasis_apply B b i j⟩

/-- Unique existence of a basis of `M` dual to `b` with respect to `B`. -/
theorem existsUnique_dualBasis (b : Basis ι A N) :
    ∃! b' : Basis ι A M, ∀ i j, B (b' i) (b j) = if j = i then 1 else 0 := by
  refine ⟨dualBasis B b, fun i j => dualBasis_apply B b i j, fun b' hb' => ?_⟩
  exact eq_dualBasis_of B b b' hb'

end LinearMap.IsPerfPair
