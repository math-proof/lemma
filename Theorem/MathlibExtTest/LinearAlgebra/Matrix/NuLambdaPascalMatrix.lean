/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/LinearAlgebra/Matrix/NuLambdaPascalMatrix.lean -/


import Mathlib.Tactic
import Def.LinearAlgebra.Matrix.NuLambdaPascalMatrix
import Lemma.Matrix.NuLambdaPascalMatrix
import Def.MathlibExtTest.LinearAlgebra.Matrix.NuLambdaPascalMatrix


namespace MetaMathlibExt

example (nu lam : ℂ) :
    IsNuLambdaPascalMatrix 0 1 nu lam Fin.elim0 unitSkewTwo (by omega) := by
  constructor
  · intro i j hij
    rcases hij with hi | hj
    · have hi0 : i ≠ 0 := by omega
      have hi1 : i ≠ 1 := by omega
      simp [unitSkewTwo, hi0, hi1]
    · have hj0 : j ≠ 0 := by omega
      have hj1 : j ≠ 1 := by omega
      simp [unitSkewTwo, hj0, hj1]
  constructor
  · intro i j
    simp only [unitSkewTwo]
    split_ifs <;> norm_num <;> omega
  constructor
  · norm_num [unitSkewTwo]
  constructor
  · omega
  · intro i j hi hj
    have hi0 : i = 0 := by omega
    have hj0 : j = 0 := by omega
    subst i
    subst j
    norm_num [unitSkewTwo]

/-- With one nonzero beta coefficient, the last-column sum is non-vacuous. -/
example (nu lam : ℂ) (S : ℕ → ℕ → ℂ)
    (h : IsNuLambdaPascalMatrix 1 2 nu lam (fun _ => 2) S (by omega)) :
    S 0 3 = 2 * S 1 3 := by
  simpa using h.last_column 1 2 nu lam (fun _ => 2) S (by omega) 0 (by omega)

#print axioms IsNuLambdaPascalMatrix

end MetaMathlibExt
