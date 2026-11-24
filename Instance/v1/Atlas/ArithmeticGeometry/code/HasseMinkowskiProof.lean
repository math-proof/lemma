module
public import Def.v1.Atlas.ArithmeticGeometry.code.HilbertSymbol.Part2
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.HilbertSymbol
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.HilbertPrimitiveSolutions
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.Theorem11_1
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.HilbertProductFormula
public import Theorem.v1.Atlas.ArithmeticGeometry.code.HilbertPrimitiveSolutions.Part2
public import Def.v1.Atlas.ArithmeticGeometry.code.Theorem11_1
public import Def.v1.Atlas.ArithmeticGeometry.code.HilbertProductFormula
public import Mathlib.NumberTheory.Padics.PadicNorm
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.QuadraticForm.Radical
public import Def.v1.Atlas.ArithmeticGeometry.code.HasseMinkowskiProof.Part2
open scoped Classical


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HasseMinkowskiProof.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-- The element $2 \in \mathbb{Q}$ is invertible (needed for converting between quadratic forms
and their associated symmetric matrices over $\mathbb{Q}$). -/
noncomputable instance invertibleTwoQ : Invertible (2 : ℚ) :=
  invertibleOfNonzero (by norm_num : (2 : ℚ) ≠ 0)

