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
import Instance.v1.Atlas.ArithmeticGeometry.code.HasseMinkowskiProof
open scoped Classical


/-- A symmetric matrix $M$ over $\mathbb{Q}$ defines a quadratic form $x \mapsto x^T M x$, and
**represents zero $p$-adically** if there exists a nonzero vector $x \in \mathbb{Q}_p^n$ with
$x^T M x = 0$. -/
def QuadraticForm.RepresentsZeroPadically {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ)
    (p : ℕ) [Fact (Nat.Prime p)] : Prop :=
  ∃ x : Fin n → ℚ_[p], (∃ i, x i ≠ 0) ∧
    dotProduct x (mulVec (M.map (fun q : ℚ => (q : ℚ_[p]))) x) = 0

