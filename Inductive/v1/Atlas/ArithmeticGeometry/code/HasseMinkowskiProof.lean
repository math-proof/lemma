/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HasseMinkowskiProof.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.ArithmeticGeometry.code.HilbertSymbol.Part2
public import Theorem.v1.Atlas.ArithmeticGeometry.code.HilbertPrimitiveSolutions.Part2
public import Def.v1.Atlas.ArithmeticGeometry.code.Theorem11_1
public import Def.v1.Atlas.ArithmeticGeometry.code.HilbertProductFormula
public import Mathlib.NumberTheory.Padics.PadicNorm
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.QuadraticForm.Radical
public import Def.v1.Atlas.ArithmeticGeometry.code.HasseMinkowskiProof
open scoped Classical

/-- The set of places of $\mathbb{Q}$: either the archimedean (infinite) place $\infty$
or a finite place $p$ given by a prime. -/
public inductive Place where
  | infty : Place
  | finite : Nat.Primes → Place
  deriving DecidableEq

