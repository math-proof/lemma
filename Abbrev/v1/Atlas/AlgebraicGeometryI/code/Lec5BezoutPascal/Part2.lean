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
public import Def.v1.Atlas.AlgebraicGeometryI.code.Lec5BezoutPascal.Part2
open MvPolynomial Classical


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec5BezoutPascal.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

namespace Lec5BezoutPascal

variable (k : Type*) [Field k]

/-- The coordinate ring of the intersection scheme of two affine plane curves `V(f)` and `V(g)`:
the quotient `k[x, y] / (f, g)`. -/
abbrev CurveQuotient (f g : MvPolynomial (Fin 2) k) :=
  MvPolynomial (Fin 2) k ⧸ (Ideal.span {f, g})

end Lec5BezoutPascal
end
