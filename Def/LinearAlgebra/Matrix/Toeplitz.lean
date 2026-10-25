/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/Toeplitz.lean -/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Order


namespace MetaMathlibExt

/-- Toeplitz matrix, JIS VOL18/Felsner `felsner2.tex`, lines 271-283, Definition
(Toeplitz matrix): a real `(n + 1)` by `(n + 1)` matrix `A = (aᵢⱼ)` is Toeplitz
iff there exist real coefficients `c₋ₙ, …, cₙ` such that `aᵢⱼ = cᵢ₋ⱼ` for all
indices (equivalently, `A` is constant on every diagonal).

The witness `c` is total on `ℤ`; only the offsets in `[-n, n]` are observed.

Concept id: `jis_term_af166143477154e55b2be88d`.
Source: https://cs.uwaterloo.ca/journals/JIS/VOL18/Felsner/felsner2.tex
Source SHA-256: `f9b167508df14b8b3fa97556d04b3fd2fca3fc7939a1c23904e576e73f0a58c2`.
Definition block SHA-256: `17bf8967c8c4965db527869b4efe74d630e63681258d740ad2f98a54e2ed8008`. -/
def IsToeplitzMatrix {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : Prop :=
  ∃ c : ℤ → ℝ, ∀ i j, A i j = c ((i.val : ℤ) - (j.val : ℤ))

/-- Symmetric Toeplitz matrix, same source (`felsner2.tex`, lines 271-283): a
Toeplitz matrix whose witnessing coefficients satisfy `c₋ₖ = cₖ` for every
integer `k`. The same witness `c` both satisfies the symmetry condition and
represents the entries.

Concept id: `jis_term_af166143477154e55b2be88d`.
Source: https://cs.uwaterloo.ca/journals/JIS/VOL18/Felsner/felsner2.tex
Source SHA-256: `f9b167508df14b8b3fa97556d04b3fd2fca3fc7939a1c23904e576e73f0a58c2`.
Definition block SHA-256: `17bf8967c8c4965db527869b4efe74d630e63681258d740ad2f98a54e2ed8008`. -/
def IsSymmetricToeplitzMatrix {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : Prop :=
  ∃ c : ℤ → ℝ, (∀ k : ℤ, c (-k) = c k) ∧
    ∀ i j, A i j = c ((i.val : ℤ) - (j.val : ℤ))

end MetaMathlibExt
