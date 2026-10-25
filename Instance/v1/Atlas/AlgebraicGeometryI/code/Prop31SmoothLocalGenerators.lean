/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Prop31SmoothLocalGenerators.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Ideal.Maps
import Def.v1.Atlas.AlgebraicGeometryI.code.Prop31SmoothLocalGenerators


noncomputable section

/-- The maximal ideal at a point is genuinely maximal. -/
instance maxIdealOfPoint_P31_isMaximal {k : Type*} [Field k] {n : ℕ}
    (x : Fin n → k) : (maxIdealOfPoint_P31 x).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _
    (fun c => ⟨MvPolynomial.C c, MvPolynomial.eval_C c⟩)

end
