/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSeminorms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Fintype.BigOperators

open scoped SchwartzMap

noncomputable section

namespace TemperedDistributions

variable
  {𝕜 : Type*} [NormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

/-- The Japanese bracket `⟨x⟩ = √(1 + ‖x‖²)` on a normed space, a smooth weight comparable to `1 + ‖x‖`. -/
noncomputable def japaneseBracket {E : Type*} [NormedAddCommGroup E] (x : E) : ℝ :=
  Real.sqrt (1 + ‖x‖ ^ 2)

/-- The weighted `C^k` norm of a Schwartz function: the infimum of constants `c ≥ 0` bounding `(1 + ‖x‖)^K · ‖∂^n f(x)‖` uniformly in `x`. -/
noncomputable def weightedCkNorm (K n : ℕ) (f : 𝓢(E, F)) : ℝ :=
  sInf { c | 0 ≤ c ∧ ∀ x, (1 + ‖x‖) ^ K * ‖iteratedFDeriv ℝ n (⇑f) x‖ ≤ c }

/-- The maximum of `weightedCkNorm K n f` over derivative orders `n ≤ K`. -/
noncomputable def weightedCkNormSup (K : ℕ) (f : 𝓢(E, F)) : ℝ :=
  (Finset.range (K + 1)).sup' Finset.nonempty_range_add_one
    (fun n => weightedCkNorm (E := E) (F := F) K n f)

/-- The sum of all Schwartz seminorms of order at most `(K, K)` applied to `f`. -/
noncomputable def monomialDerivNormSum (K : ℕ) (f : 𝓢(E, F)) : ℝ :=
  (Finset.Iic (K, K)).sum (fun m => (SchwartzMap.seminorm 𝕜 m.1 m.2) f)

/-- The order `|α| = ∑ αᵢ` of a multi-index `α : Fin m → ℕ`. -/
def multiIndexOrder (α : Fin m → ℕ) : ℕ := ∑ i, α i

/-- From a tuple `σ : Fin n → Fin m` build the multi-index counting fibers of `σ`. -/
def tupleToMultiIndex {n : ℕ} (σ : Fin n → Fin m) : Fin m → ℕ :=
  fun i => (Finset.univ.filter (fun k => σ k = i)).card

/-- Canonical tuple of unit direction vectors corresponding to a multi-index `β`, indexed by `Fin |β|`. -/
noncomputable def multiIndexDirections (β : Fin m → ℕ) :
    Fin (multiIndexOrder β) → EuclideanSpace ℝ (Fin m) :=
  fun k => EuclideanSpace.single ((finSigmaFinEquiv (n := β)).symm k).1 1

/-- The real monomial `x^α = ∏ᵢ (xᵢ)^(αᵢ)` associated to a multi-index `α`. -/
def realMonomial (α : Fin m → ℕ) (x : EuclideanSpace ℝ (Fin m)) : ℝ :=
  ∏ i : Fin m, (x i) ^ (α i)

/-- The mixed partial derivative `∂^β f(x)` of order `β`, expressed via the iterated Fréchet derivative applied to the canonical direction tuple. -/
noncomputable def multiIndexPartialDeriv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (β : Fin m → ℕ)
    (f : EuclideanSpace ℝ (Fin m) → F) (x : EuclideanSpace ℝ (Fin m)) : F :=
  (iteratedFDeriv ℝ (multiIndexOrder β) f x) (multiIndexDirections β)

/-- Single-coordinate multi-index: `k` at position `i`, zero elsewhere. -/
def coordMultiIndex (k : ℕ) (i : Fin m) : Fin m → ℕ :=
  fun j => if j = i then k else 0

/-- The finset of all multi-indices `α : Fin m → ℕ` with each `αᵢ ≤ K`. -/
def boundedMultiIndices (m K : ℕ) : Finset (Fin m → ℕ) :=
  Fintype.piFinset (fun _ : Fin m => Finset.range (K + 1))

/-- Multi-indices `α` with total order `|α| ≤ K`. -/
def totalOrderBoundedMultiIndices (m K : ℕ) : Finset (Fin m → ℕ) :=
  (boundedMultiIndices m K).filter (fun α => multiIndexOrder α ≤ K)

/-- The monomial-mixed-derivative `sup` norm: the infimum of `c ≥ 0` with `|x^α| · ‖∂^β f(x)‖ ≤ c` for all `x`. -/
noncomputable def monomialDerivSupNorm
    (α β : Fin m → ℕ)
    (f : 𝓢(EuclideanSpace ℝ (Fin m), F)) : ℝ :=
  sInf { c | 0 ≤ c ∧ ∀ x, |realMonomial α x| * ‖multiIndexPartialDeriv β (⇑f) x‖ ≤ c }

/-- The book-style multi-index norm: sum of `monomialDerivSupNorm α β f` over all `|α|, |β| ≤ K`. -/
noncomputable def bookMultiIndexNorm (K : ℕ)
    (f : 𝓢(EuclideanSpace ℝ (Fin m), F)) : ℝ :=
  ∑ α ∈ totalOrderBoundedMultiIndices m K, ∑ β ∈ totalOrderBoundedMultiIndices m K,
    monomialDerivSupNorm α β f

/-- The `⟨x⟩^K`-weighted `C^k` norm of a Schwartz function: the infimum of `c ≥ 0` bounding `⟨x⟩^K · ‖∂^n f(x)‖` uniformly. -/
noncomputable def japaneseBracketCkNorm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K n : ℕ) (f : 𝓢(E, F)) : ℝ :=
  sInf { c | 0 ≤ c ∧ ∀ x, japaneseBracket x ^ K * ‖iteratedFDeriv ℝ n (⇑f) x‖ ≤ c }

/-- The supremum of `japaneseBracketCkNorm K n f` over `n ≤ K`. -/
noncomputable def japaneseBracketCkNormSup {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : ℕ) (f : 𝓢(E, F)) : ℝ :=
  (Finset.range (K + 1)).sup' Finset.nonempty_range_add_one
    (fun n => japaneseBracketCkNorm (E := E) (F := F) K n f)
