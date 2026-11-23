/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec5BezoutPascal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Def.v1.Atlas.AlgebraicGeometryI.code.BezoutMultiplicitySum.Part2
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.BezoutMultiplicitySum
public import Theorem.v1.Atlas.AlgebraicGeometryI.code.Lec5BezoutPascal

@[expose] public section

open MvPolynomial Classical


noncomputable section

namespace Lec5BezoutPascal

variable (k : Type*) [Field k]

/-- Multiplicity of a hypersurface `V(g)` at a point `p`: the smallest degree at which the
translate `g(x + p)` has a nonzero homogeneous component. -/
def hypersurfaceMultiplicity {n : ℕ} (g : MvPolynomial (Fin n) k) (p : Fin n → k)
    (hg : g ≠ 0) : ℕ :=
  Nat.find (exists_homogeneousComponent_ne_zero k (translatePoly k g p)
    (translatePoly_ne_zero k g p hg))

end Lec5BezoutPascal
end
