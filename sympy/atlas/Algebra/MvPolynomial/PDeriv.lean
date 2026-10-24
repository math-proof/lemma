/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/MvPolynomial/PDeriv.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Algebra.MvPolynomial.PDeriv

namespace MvPolynomial

/-- Apply the operators `1 - ∂ᵢ`, in list order, to a multivariate polynomial. -/
noncomputable def mixedDifferential {σ R : Type*} [CommRing R]
    (indices : List σ) (p : MvPolynomial σ R) : MvPolynomial σ R :=
  indices.foldl (fun q i ↦ q - pderiv i q) p
end MvPolynomial
