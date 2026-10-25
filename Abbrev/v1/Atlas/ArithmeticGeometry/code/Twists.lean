/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Twists.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Def.v1.Atlas.ArithmeticGeometry.code.JInvariant.Part3
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.JInvariant
open AlgebraicGeometry CategoryTheory Limits

universe u


namespace ArithmeticGeometry

/-- The affine scheme $\mathrm{Spec}\, R$ for a commutative ring $R$. -/
noncomputable abbrev specOf (R : Type u) [CommRing R] : Scheme.{u} := Spec (.of R)

end ArithmeticGeometry
