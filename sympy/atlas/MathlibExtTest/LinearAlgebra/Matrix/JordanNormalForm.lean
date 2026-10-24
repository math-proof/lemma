/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/LinearAlgebra/Matrix/JordanNormalForm.lean -/


import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Basis
import sympy.atlas.LinearAlgebra.Matrix.JordanNormalForm
import Lemma.Matrix.JordanNormalForm

open MathlibExt.LinearAlgebra.Matrix.JordanNormalFormWanted
open Module

-- A two-vector Jordan chain puts one in the superdiagonal entry.
example {V : Type*} [AddCommGroup V] [Module ℚ V]
    (b : Basis (Fin 2) ℚ V) (f : Module.End ℚ V) (μ : ℚ)
    (hzero : f (b 0) = μ • b 0) (hsucc : f (b 1) = μ • b 1 + b 0) :
    LinearMap.toMatrix b b f 0 1 = 1 ∧ jordanBlock 2 μ 0 1 = 1 := by
  have hs : ∀ j : Fin 1, f (b j.succ) = μ • b j.succ + b j.castSucc := by
    intro j
    fin_cases j
    simpa using hsucc
  have hm := LinearMap.toMatrix_eq_jordanBlock 1 b f μ hzero hs
  constructor
  · rw [hm, jordanBlock_apply]
    norm_num
  · rw [jordanBlock_apply]
    norm_num

-- A nilpotent endomorphism admits a basis with zero diagonal entries.
example {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (N : Module.End ℚ V) (hnil : IsNilpotent N) :
    ∃ (k : ℕ) (d : Fin k → ℕ) (b : Basis (Σ i, Fin (d i + 1)) ℚ V),
      ∀ i, LinearMap.toMatrix b b N ⟨i, 0⟩ ⟨i, 0⟩ = 0 := by
  obtain ⟨k, d, b, hzero, hsucc, _⟩ :=
    Module.End.exists_jordanBasis_of_isNilpotent N hnil
  refine ⟨k, d, b, ?_⟩
  have hm := LinearMap.toMatrix_eq_blockDiagonal_jordanBlock d b N (fun _ ↦ 0)
    (by simpa using hzero) (by simpa using hsucc)
  intro i
  rw [hm, Matrix.blockDiagonal'_apply_eq, jordanBlock_apply]
  simp

-- A split endomorphism admits a Jordan basis whose diagonal records its eigenvalues.
example {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : Module.End K V) (hf : f.charpoly.Splits) :
    ∃ (k : ℕ) (d : Fin k → ℕ) (μ : Fin k → K)
      (b : Basis (Σ i, Fin (d i + 1)) K V),
      ∀ i (j : Fin (d i + 1)), LinearMap.toMatrix b b f ⟨i, j⟩ ⟨i, j⟩ = μ i := by
  obtain ⟨k, d, μ, b, _, _, hJ⟩ :=
    Module.End.exists_jordanBasis_of_charpoly_splits f hf
  refine ⟨k, d, μ, b, fun i j ↦ ?_⟩
  rw [hJ, Matrix.blockDiagonal'_apply_eq, jordanBlock_apply]
  simp

-- The block sizes in a Jordan normal form account for every matrix index.
example {K n : Type*} [Field K] [Fintype n] [DecidableEq n]
    (A : Matrix n n K) (h : A.charpoly.Splits) :
    ∃ (k : ℕ) (s : Fin k → ℕ) (μ : Fin k → K) (P : Matrix n n K)
      (e : (Σ i, Fin (s i)) ≃ n),
      (∀ i, 0 < s i) ∧ IsUnit P ∧
        A = P * Matrix.reindex e e
          (Matrix.blockDiagonal' (fun i => jordanBlock (s i) (μ i))) * P⁻¹ ∧
        ∑ i, s i = Fintype.card n := by
  obtain ⟨k, s, μ, P, e, hpos, hP, hA⟩ := exists_jordan_normal_form_of_splits A h
  refine ⟨k, s, μ, P, e, hpos, hP, hA, ?_⟩
  simpa only [Fintype.card_sigma, Fintype.card_fin] using Fintype.card_congr e
