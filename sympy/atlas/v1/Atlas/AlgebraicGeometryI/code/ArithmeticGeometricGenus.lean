/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ArithmeticGeometricGenus.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.SheafCohomology
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.SheafCohomology
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.DedekindCurve
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.DedekindCurve
import Mathlib.LinearAlgebra.Dual.Lemmas

noncomputable section

namespace ArithmeticGeometricGenus

/-- The arithmetic genus of `ℙ¹_k`: `g_a := dim_k H¹(ℙ¹, O)`. -/
def arithmeticGenusP1 (k : Type) [Field k] : ℕ :=
  Module.finrank k (SheafCohomology.H1 k 0)

/-- The geometric genus of `ℙ¹_k`: `g_m := dim_k Γ(ℙ¹, ω) = dim_k H⁰(ℙ¹, O(-2))`. -/
def geometricGenusP1 (k : Type) [Field k] : ℕ :=
  Module.finrank k (SheafCohomology.H0 k (-2))
