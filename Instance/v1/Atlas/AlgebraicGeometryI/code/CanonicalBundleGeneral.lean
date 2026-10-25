/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalBundleGeneral.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.LinearAlgebra.ExteriorPower.Basis


noncomputable section

open KaehlerDifferential Module

universe u

section RankComputation

variable (k : Type u) [Field k] (n : ℕ)

/-- The Kähler differential module is finitely generated. -/
instance kahler_mvpoly_finite :
    Module.Finite (MvPolynomial (Fin (n+1)) k)
      (Ω[MvPolynomial (Fin (n+1)) k⁄k]) :=
  Module.Finite.of_basis (mvPolynomialBasis k (Fin (n + 1)))

end RankComputation
end
