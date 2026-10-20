/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Fourier/PrincipalMinor.lean -/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Principal minors of cyclic Fourier matrices

Given a chosen primitive `M`-th root of unity and a finite subset of
`ZMod M`, this file defines the corresponding principal Fourier minor and its
determinant.
-/

namespace Fourier

/-- A chosen primitive `M`-th root of unity, with the source condition `M ≥ 2`. -/
structure RootData (M : ℕ) (R : Type*) [CommRing R] where
  zeta : R
  order_ge : 2 ≤ M
  isPrimitiveRoot : IsPrimitiveRoot zeta M

/-- The principal Fourier minor indexed by `S`, with `(i,j)` entry `ζ ^ (i*j)`. -/
noncomputable def principalMinorMatrix (M : ℕ) {R : Type*} [CommRing R]
    (root : RootData M R) (S : Finset (ZMod M)) : Matrix S S R := by
  letI : NeZero M := ⟨by have := root.order_ge; omega⟩
  exact fun i j ↦ root.zeta ^ (i.val * j.val).val

/-- The determinant of the principal Fourier minor indexed by `S`. -/
noncomputable def principalMinorDet (M : ℕ) {R : Type*} [CommRing R]
    (root : RootData M R) (S : Finset (ZMod M)) : R :=
  (principalMinorMatrix M root S).det

/-- Entry formula for a principal Fourier minor. -/
@[simp]
theorem principalMinorMatrix_apply (M : ℕ) {R : Type*} [CommRing R]
    (root : RootData M R) (S : Finset (ZMod M)) (i j : S) :
    principalMinorMatrix M root S i j = root.zeta ^ (i.val * j.val).val := by
  simp [principalMinorMatrix]

/-- The determinant of the empty principal minor is one. -/
@[simp]
theorem principalMinorDet_empty (M : ℕ) {R : Type*} [CommRing R]
    (root : RootData M R) : principalMinorDet M root ∅ = 1 := by
  simp [principalMinorDet]

/-- Formula for the determinant of a singleton principal minor. -/
@[simp]
theorem principalMinorDet_singleton (M : ℕ) {R : Type*} [CommRing R]
    (root : RootData M R) (a : ZMod M) :
    principalMinorDet M root {a} = root.zeta ^ (a * a).val := by
  simp [principalMinorDet]

end Fourier
