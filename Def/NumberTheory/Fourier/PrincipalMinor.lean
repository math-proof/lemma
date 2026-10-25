/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Fourier/PrincipalMinor.lean -/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Structure.NumberTheory.Fourier.PrincipalMinor
/-!
# Principal minors of cyclic Fourier matrices

Given a chosen primitive `M`-th root of unity and a finite subset of
`ZMod M`, this file defines the corresponding principal Fourier minor and its
determinant.
-/


namespace Fourier

/-- The principal Fourier minor indexed by `S`, with `(i,j)` entry `ζ ^ (i*j)`. -/
noncomputable def principalMinorMatrix (M : ℕ) {R : Type*} [CommRing R]
    (root : RootData M R) (S : Finset (ZMod M)) : Matrix S S R := by
  letI : NeZero M := ⟨by have := root.order_ge; omega⟩
  exact fun i j ↦ root.zeta ^ (i.val * j.val).val

/-- The determinant of the principal Fourier minor indexed by `S`. -/
noncomputable def principalMinorDet (M : ℕ) {R : Type*} [CommRing R]
    (root : RootData M R) (S : Finset (ZMod M)) : R :=
  (principalMinorMatrix M root S).det

end Fourier
