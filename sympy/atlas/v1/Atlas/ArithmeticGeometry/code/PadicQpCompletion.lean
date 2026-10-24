/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicQpCompletion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.WithVal

noncomputable section

open scoped Padic

variable (p : ℕ) [hp : Fact p.Prime]


/-- Canonical ring homomorphism from $\mathbb{Q}$ into the uniform-space completion with respect to
the $p$-adic valuation, obtained by composing the `WithVal` identification with the completion's
coercion ring hom. -/
def ratEmbedPadicCompletion : ℚ →+* (Rat.padicValuation p).Completion :=
  (UniformSpace.Completion.coeRingHom).comp (WithVal.equiv (Rat.padicValuation p)).symm.toRingHom

/-- Ring isomorphism between the uniform completion of $\mathbb{Q}$ under the $p$-adic valuation and
Mathlib's $\mathbb{Q}_p$. -/
def padic_completion_ringEquiv :
    (Rat.padicValuation p).Completion ≃+* ℚ_[p] :=
  Padic.withValRingEquiv

/-- Uniform-space isomorphism between the uniform completion of $\mathbb{Q}$ under the $p$-adic
valuation and Mathlib's $\mathbb{Q}_p$, witnessing that the two completions agree as uniform
spaces. -/
def padic_completion_uniformEquiv :
    (Rat.padicValuation p).Completion ≃ᵤ ℚ_[p] :=
  Padic.withValUniformEquiv


end
