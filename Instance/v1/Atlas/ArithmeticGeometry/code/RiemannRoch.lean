/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Finite
import Def.v1.Atlas.ArithmeticGeometry.code.EffectiveDivisors
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.EffectiveDivisors
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.CanonicalDivisors
import Def.v1.Atlas.ArithmeticGeometry.code.CanonicalDivisors.Part2
import Def.v1.Atlas.ArithmeticGeometry.code.RiemannRoch
open scoped RestrictedProduct

variable {F : Type*} [Field F] {P : Type*} {O : P → ValuationSubring F}


namespace FunctionFieldAdeleRing

/-- The adele ring inherits a commutative ring structure from the restricted product. -/
noncomputable instance instCommRing : CommRing (FunctionFieldAdeleRing F P O) :=
  inferInstanceAs (CommRing (Πʳ _p : P, [(fun _ => F) _p, (O _p : ValuationSubring F)]))

/-- Adeles act as functions $P \to F$ via the underlying restricted product. -/
instance instDFunLike :
    DFunLike (FunctionFieldAdeleRing F P O) P (fun _ => F) :=
  inferInstanceAs <|
    DFunLike (Πʳ _p : P, [(fun _ => F) _p, (O _p : ValuationSubring F)]) P (fun _ => F)

end FunctionFieldAdeleRing
