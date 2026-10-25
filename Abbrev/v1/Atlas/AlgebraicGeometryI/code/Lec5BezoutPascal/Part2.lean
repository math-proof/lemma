/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec5BezoutPascal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.BezoutMultiplicitySum.Part2
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.BezoutMultiplicitySum
import Def.v1.Atlas.AlgebraicGeometryI.code.Lec5BezoutPascal.Part2
open MvPolynomial Classical


noncomputable section

namespace Lec5BezoutPascal

variable (k : Type*) [Field k]

/-- The coordinate ring of the intersection scheme of two affine plane curves `V(f)` and `V(g)`:
the quotient `k[x, y] / (f, g)`. -/
abbrev CurveQuotient (f g : MvPolynomial (Fin 2) k) :=
  MvPolynomial (Fin 2) k ⧸ (Ideal.span {f, g})

end Lec5BezoutPascal
end
