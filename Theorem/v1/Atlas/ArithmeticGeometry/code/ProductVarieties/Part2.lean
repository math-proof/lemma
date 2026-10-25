/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProductVarieties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.Varieties.Part9
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Varieties
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Morphisms
import Def.v1.Atlas.ArithmeticGeometry.code.Morphisms.Part6
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Topology.NoetherianSpace
import Mathlib.RingTheory.MvPolynomial.Basic
import Def.v1.Atlas.ArithmeticGeometry.code.ProductVarieties.Part3
variable (k : Type*) [Field k]


/-- Evaluating $\mathrm{embedHomogPolyLeft}(p)$ at `Fin.append a b` equals evaluating $p$
at $a$. -/
theorem eval_embedHomogPolyLeft {k : Type*} [Field k] (m n : ℕ)
    (p : MvPolynomial (Fin (m + 1)) (AlgebraicClosure k))
    (a : Fin (m + 1) → AlgebraicClosure k) (b : Fin (n + 1) → AlgebraicClosure k) :
    eval (Fin.append a b) (embedHomogPolyLeft m n p) = eval a p := by
  simp only [embedHomogPolyLeft, eval_rename]
  have : Fin.append a b ∘ Fin.castAdd (n + 1) = a := by
    funext i; exact Fin.append_left a b i
  rw [this]

/-- Evaluating $\mathrm{embedHomogPolyRight}(p)$ at `Fin.append a b` equals evaluating $p$
at $b$. -/
theorem eval_embedHomogPolyRight {k : Type*} [Field k] (m n : ℕ)
    (p : MvPolynomial (Fin (n + 1)) (AlgebraicClosure k))
    (a : Fin (m + 1) → AlgebraicClosure k) (b : Fin (n + 1) → AlgebraicClosure k) :
    eval (Fin.append a b) (embedHomogPolyRight m n p) = eval b p := by
  simp only [embedHomogPolyRight, eval_rename]
  have : Fin.append a b ∘ Fin.natAdd (m + 1) = b := by
    funext i; exact Fin.append_right a b i
  rw [this]

