/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/LinearAlgebra/Matrix/RealSVD.lean -/


import Def.LinearAlgebra.Matrix.RealSVD
import Lemma.Matrix.RealSVD
open MathlibExt.LinearAlgebra.Matrix.RealSVDWanted


-- The full SVD has nonincreasing singular values that vanish beyond the codomain dimension.
example (A : Matrix (Fin 2) (Fin 3) ℝ) :
    ∃ (U : Matrix.orthogonalGroup (Fin 2) ℝ) (V : Matrix.orthogonalGroup (Fin 3) ℝ)
        (σ : Fin 3 → ℝ),
      A = (U : Matrix (Fin 2) (Fin 2) ℝ) *
        Matrix.of (fun i j => if i.val = j.val then σ j else 0) *
        Matrix.transpose (V : Matrix (Fin 3) (Fin 3) ℝ) ∧
      (∀ j, σ j ≤ σ 0) ∧ σ 2 = 0 := by
  obtain ⟨U, V, σ, -, hσ, hzero, hA⟩ :=
    Matrix.exists_orthogonalGroup_rectangularDiagonal_antitone 2 3 A
  refine ⟨U, V, σ, hA, ?_, hzero 2 (by decide)⟩
  intro j
  exact hσ (Fin.zero_le j)

-- A right orthogonal change of basis kills every column beyond the codomain dimension.
example {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) (hj : m ≤ j.val) :
    ∃ V : Matrix.orthogonalGroup (Fin n) ℝ,
      ∀ i, (A * (V : Matrix (Fin n) (Fin n) ℝ)) i j = 0 := by
  obtain ⟨U, V, σ, -, -, hzero, hAV⟩ :=
    Matrix.exists_orthogonalGroup_mul_eq_rectangularDiagonal m n A
  refine ⟨V, fun i => ?_⟩
  rw [hAV, Matrix.mul_apply]
  simp [hzero j hj]

-- The full factorization makes the second rotated column of a `1 × 2` matrix vanish.
example (A : Matrix (Fin 1) (Fin 2) ℝ) :
    ∃ V : Matrix (Fin 2) (Fin 2) ℝ, V ∈ Matrix.orthogonalGroup (Fin 2) ℝ ∧
      (A * V) 0 1 = 0 := by
  obtain ⟨U, V, σ, -, -, -, hV, hA⟩ := real_singular_value_decomposition 1 2 A
  refine ⟨V, hV, ?_⟩
  have hVtV : V.transpose * V = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin 2) ℝ).mp hV
  calc
    (A * V) 0 1 =
        ((U * Matrix.of (fun (i : Fin 1) (j : Fin 2) =>
          if i.val = j.val then σ j else 0) * V.transpose) * V) 0 1 := by rw [hA]
    _ = (U * Matrix.of (fun (i : Fin 1) (j : Fin 2) =>
          if i.val = j.val then σ j else 0) *
          (V.transpose * V)) 0 1 := by rw [Matrix.mul_assoc]
    _ = (U * Matrix.of (fun (i : Fin 1) (j : Fin 2) =>
          if i.val = j.val then σ j else 0)) 0 1 := by
      rw [hVtV, Matrix.mul_one]
    _ = 0 := by simp [Matrix.mul_apply]

