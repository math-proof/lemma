module
public import Def.v1.Atlas.ArithmeticGeometry.code.HilbertSymbol.Part2
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.HilbertSymbol
public import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.HilbertPrimitiveSolutions
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.Theorem11_1
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.HilbertProductFormula
public import Theorem.v1.Atlas.ArithmeticGeometry.code.HilbertPrimitiveSolutions.Part2
public import Def.v1.Atlas.ArithmeticGeometry.code.Theorem11_1
public import Def.v1.Atlas.ArithmeticGeometry.code.HilbertProductFormula
public import Mathlib.NumberTheory.Padics.PadicNorm
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.QuadraticForm.Radical
public import Inductive.v1.Atlas.ArithmeticGeometry.code.HasseMinkowskiProof
open scoped Classical


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HasseMinkowskiProof.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
/-- The Hilbert symbol $(a, b)_v$ at the place $v$ of $\mathbb{Q}$, taking values in
$\{1, -1\}$. -/
def hilbertAt (v : Place) (a b : ℚˣ) : ℤ :=
  match v with
  | Place.infty => Corollary115.hilbertAtInfty a b
  | Place.finite p =>
    haveI : Fact (Nat.Prime p.val) := ⟨p.property⟩
    Corollary115.hilbertAtPrime p.val a b

