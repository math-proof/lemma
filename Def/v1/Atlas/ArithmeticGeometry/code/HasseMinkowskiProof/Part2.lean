/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/HasseMinkowskiProof.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.HilbertSymbol.Part2
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.HilbertSymbol
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.HilbertPrimitiveSolutions
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Theorem11_1
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.HilbertProductFormula
import Theorem.v1.Atlas.ArithmeticGeometry.code.HilbertPrimitiveSolutions.Part2
import Def.v1.Atlas.ArithmeticGeometry.code.Theorem11_1
import Def.v1.Atlas.ArithmeticGeometry.code.HilbertProductFormula
import Mathlib.NumberTheory.Padics.PadicNorm
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.QuadraticForm.Radical
import Inductive.v1.Atlas.ArithmeticGeometry.code.HasseMinkowskiProof
open scoped Classical


/-- The Hilbert symbol $(a, b)_v$ at the place $v$ of $\mathbb{Q}$, taking values in
$\{1, -1\}$. -/
def hilbertAt (v : Place) (a b : ℚˣ) : ℤ :=
  match v with
  | Place.infty => Corollary115.hilbertAtInfty a b
  | Place.finite p =>
    haveI : Fact (Nat.Prime p.val) := ⟨p.property⟩
    Corollary115.hilbertAtPrime p.val a b

