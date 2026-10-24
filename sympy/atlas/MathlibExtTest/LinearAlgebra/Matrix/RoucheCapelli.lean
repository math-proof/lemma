/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/LinearAlgebra/Matrix/RoucheCapelli.lean -/


import Lemma.Matrix.RoucheCapelli

open scoped Matrix

-- The explicit solution `[1, 1]` gives equal ranks for this singular rational system.
example :
    let A : Matrix (Fin 2) (Fin 2) ℚ := !![1, 2; 2, 4]
    let b : Fin 2 → ℚ := ![3, 6]
    A.rank =
      (Matrix.of (fun i => Sum.elim (A i) (fun _ : Fin 1 => b i)) :
        Matrix (Fin 2) (Fin 2 ⊕ Fin 1) ℚ).rank := by
  dsimp only
  apply (MetaMathlibExt.rouche_capelli _ _).mp
  refine ⟨![1, 1], ?_⟩
  ext i
  fin_cases i <;> norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

-- The inconsistent right-hand side forces a rank mismatch.
example :
    let A : Matrix (Fin 2) (Fin 2) ℚ := !![1, 2; 2, 4]
    let b : Fin 2 → ℚ := ![1, 3]
    A.rank ≠
      (Matrix.of (fun i => Sum.elim (A i) (fun _ : Fin 1 => b i)) :
        Matrix (Fin 2) (Fin 2 ⊕ Fin 1) ℚ).rank := by
  dsimp only
  have hno : ¬∃ x : Fin 2 → ℚ, !![1, 2; 2, 4] *ᵥ x = ![1, 3] := by
    rintro ⟨x, hx⟩
    have h0 := congr_fun hx 0
    have h1 := congr_fun hx 1
    norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
    linarith
  intro hrank
  exact hno ((MetaMathlibExt.rouche_capelli _ _).mpr hrank)

-- A full-row-rank matrix makes every right-hand side solvable.
example {m n K : Type*} [Fintype m] [Fintype n] [Field K]
    (A : Matrix m n K) (b : m → K) (hA : A.rank = Fintype.card m) :
    ∃ x : n → K, A *ᵥ x = b := by
  apply (MetaMathlibExt.rouche_capelli A b).mpr
  apply Nat.le_antisymm
  · have hsub :
        (Matrix.of (fun i => Sum.elim (A i) (fun _ : Fin 1 => b i)) :
          Matrix m (n ⊕ Fin 1) K).submatrix id Sum.inl = A := by
      ext i j
      rfl
    calc
      A.rank =
          ((Matrix.of (fun i => Sum.elim (A i) (fun _ : Fin 1 => b i)) :
            Matrix m (n ⊕ Fin 1) K).submatrix id Sum.inl).rank :=
        congrArg Matrix.rank hsub.symm
      _ ≤ _ := Matrix.rank_submatrix_le
        (Matrix.of (fun i => Sum.elim (A i) (fun _ : Fin 1 => b i)) :
          Matrix m (n ⊕ Fin 1) K) id Sum.inl
  · rw [hA]
    exact Matrix.rank_le_card_height _
