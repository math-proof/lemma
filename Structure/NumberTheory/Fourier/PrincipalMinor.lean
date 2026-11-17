/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Fourier/PrincipalMinor.lean -/

module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
/-!
# Principal minors of cyclic Fourier matrices

Given a chosen primitive `M`-th root of unity and a finite subset of
`ZMod M`, this file defines the corresponding principal Fourier minor and its
determinant.
-/
public section




namespace Fourier

/-- A chosen primitive `M`-th root of unity, with the source condition `M ≥ 2`. -/
structure RootData (M : ℕ) (R : Type*) [CommRing R] where
  zeta : R
  order_ge : 2 ≤ M
  isPrimitiveRoot : IsPrimitiveRoot zeta M

end Fourier
