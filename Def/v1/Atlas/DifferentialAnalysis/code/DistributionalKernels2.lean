/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DistributionalKernels2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.MvPolynomial.Basic
import Def.v1.Atlas.DifferentialAnalysis.code.TemperedDistributions
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.TemperedDistributions
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.TestFunctions
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SobolevEmbedding
import Instance.v1.Atlas.DifferentialAnalysis.code.TestFunctions
import Def.v1.Atlas.DifferentialAnalysis.code.SobolevEmbedding.Part5


noncomputable section

open scoped BigOperators SchwartzMap LineDeriv

namespace DistributionalKernels

variable {n : ℕ}

/-- The size `|γ| = ∑ γ i` of a multi-index `γ : Fin n → ℕ`. -/
def multiIndexSize (γ : Fin n → ℕ) : ℕ := ∑ i, γ i

/-- The finite set of multi-indices `α` that are componentwise at most `γ`. -/
def multiIndexLeqFinset (γ : Fin n → ℕ) : Finset (Fin n → ℕ) :=
  Fintype.piFinset fun i => Finset.range (γ i + 1)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The `m`-fold distributional partial derivative in coordinate `j`, acting on a tempered distribution. -/
def iterCoordDeriv (j : Fin n) (m : ℕ)
    (v : 𝓢'(EuclideanSpace ℝ (Fin n), F)) :
    𝓢'(EuclideanSpace ℝ (Fin n), F) :=
  (fun u => TemperedDistributions.distribDerivCLM
    (EuclideanSpace.single j (1 : ℝ)) u)^[m] v

/-- The multi-index distributional derivative `D^γ v`, taken coordinate by coordinate. -/
def multiIndexDistribDeriv (γ : Fin n → ℕ)
    (v : 𝓢'(EuclideanSpace ℝ (Fin n), F)) :
    𝓢'(EuclideanSpace ℝ (Fin n), F) :=
  (List.finRange n).foldl (fun w j => iterCoordDeriv j (γ j) w) v

/-- Multiplication of a tempered distribution by the power `⟨x⟩^k` of the Japanese bracket. -/
def distribMulBracketPow (k : ℤ)
    (v : 𝓢'(EuclideanSpace ℝ (Fin n), F)) :
    𝓢'(EuclideanSpace ℝ (Fin n), F) :=
  TemperedDistributions.distribMulCLM
    (fun (x : EuclideanSpace ℝ (Fin n)) =>
      ((TestFunctions.japaneseBracket n x : ℝ) : ℂ) ^ k) v

/-- Multiplication of a tempered distribution by a real polynomial evaluated at `x`. -/
def distribMulPoly (p : MvPolynomial (Fin n) ℝ)
    (v : 𝓢'(EuclideanSpace ℝ (Fin n), F)) :
    𝓢'(EuclideanSpace ℝ (Fin n), F) :=
  TemperedDistributions.distribMulCLM
    (fun (x : EuclideanSpace ℝ (Fin n)) =>
      ((MvPolynomial.eval (fun i => x i) p : ℝ) : ℂ)) v

/-- The right-hand side of the Leibniz expansion `D^γ (p ⟨x⟩^k v)`: a sum over `α ≤ γ` of `D^{γ-α}` applied to polynomial-times-bracket-power multiples of `v`. -/
def weightedDerivRHS (γ : Fin n → ℕ) (k : ℤ)
    (coeffs : (Fin n → ℕ) → MvPolynomial (Fin n) ℝ)
    (v : 𝓢'(EuclideanSpace ℝ (Fin n), F)) :
    𝓢'(EuclideanSpace ℝ (Fin n), F) :=
  ∑ α ∈ multiIndexLeqFinset γ,
    multiIndexDistribDeriv (γ - α)
      (distribMulPoly (coeffs α)
        (distribMulBracketPow (k - 2 * ↑(multiIndexSize (γ - α))) v))

end DistributionalKernels
end
