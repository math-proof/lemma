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
import Class.v1.Atlas.ArithmeticGeometry.code.RiemannRoch
open scoped RestrictedProduct

variable {F : Type*} [Field F] {P : Type*} {O : P → ValuationSubring F}


namespace FunctionFieldAdeleRing

variable [ConstantField k (O := O)]

/-- The diagonal embedding $k \hookrightarrow \mathbb{A}_F$ sending a constant $c$ to the
constant adele $(c, c, c, \dots)$. -/
noncomputable def diagonalRingHom : k →+* FunctionFieldAdeleRing F P O where
  toFun c := ⟨fun _ => algebraMap k F c, Filter.Eventually.of_forall
    (fun p => ConstantField.algebraMap_mem (k := k) p c)⟩
  map_one' := ext fun _ => map_one (algebraMap k F)
  map_mul' x y := ext fun _ => map_mul (algebraMap k F) x y
  map_zero' := ext fun _ => map_zero (algebraMap k F)
  map_add' x y := ext fun _ => map_add (algebraMap k F) x y

end FunctionFieldAdeleRing
