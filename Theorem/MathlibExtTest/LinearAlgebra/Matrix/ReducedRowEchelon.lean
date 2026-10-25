/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/LinearAlgebra/Matrix/ReducedRowEchelon.lean -/


import Def.LinearAlgebra.Matrix.ReducedRowEchelon
import Lemma.Matrix.ReducedRowEchelon


namespace MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted

example (A : Matrix (Fin 2) (Fin 1) ℕ) (hA : A.IsReducedRowEchelon)
    (hc : A.IsLeadingEntry 0 0) : A.col 0 = Pi.single 0 1 :=
  hA.col_eq_single_of_isLeadingEntry hc

-- Reindexing an RREF exposes its pivot column, while uniqueness identifies invertible RREFs.
example (R : Matrix (Fin 2) Bool ℚ) (P : Matrix (Fin 2) (Fin 2) ℚ)
    (hR : R.IsReducedRowEchelon) (hP : P.IsReducedRowEchelon) (hPunit : IsUnit P) :
    let e : Fin (Fintype.card Bool) ≃o Bool := Fintype.orderIsoFinOfCardEq Bool rfl
    let T : Matrix (Fin 2) (Fin (Fintype.card Bool)) ℚ := R.submatrix id e
    T.IsLeadingEntry 0 0 → T 1 0 = 0 ∧ P = 1 := by
  dsimp only
  intro hlead
  let e : Fin (Fintype.card Bool) ≃o Bool := Fintype.orderIsoFinOfCardEq Bool rfl
  have hT := hR.submatrix_orderIso e
  constructor
  · have hcol := hT.col_eq_single_of_isLeadingEntry hlead
    exact congrFun hcol 1
  · have hI : (1 : Matrix (Fin 2) (Fin 2) ℚ).IsReducedRowEchelon := by
      refine ⟨?_, ?_, ?_⟩
      · intro i₁ i₂ hi j hz
        rw [Matrix.one_apply]
        split
        · rename_i h
          subst j
          have hzero := hz i₁ hi
          simp at hzero
        · rfl
      · intro i c hc
        have hic : i = c := by
          by_contra hne
          apply hc.2
          rw [Matrix.one_apply, ite_eq_right hne]
        rw [Matrix.one_apply, ite_eq_left hic]
      · intro i₁ i₂ c hi hc
        have hi₂c : i₂ = c := by
          by_contra hne
          apply hc.2
          rw [Matrix.one_apply, ite_eq_right hne]
        subst c
        rw [Matrix.one_apply, ite_eq_right (ne_of_lt hi)]
    exact (isReducedRowEchelon_unique_of_rowEquivalent 1 P hI hP P hPunit (by simp)).symm

-- The constructed RREF has the same homogeneous solution space as the input matrix.
example (A : Matrix (Fin 2) (Fin 2) ℚ) :
    ∃ R P, R.IsReducedRowEchelon ∧ IsUnit P ∧ R = P * A ∧
      LinearMap.ker R.mulVecLin = LinearMap.ker A.mulVecLin := by
  obtain ⟨R, P, hR, hP, hRA⟩ := exists_isReducedRowEchelon_rowEquivalent A
  refine ⟨R, P, hR, hP, hRA, ?_⟩
  rw [hRA]
  exact ker_mulVecLin_mul_left_isUnit P A hP

end MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted
