import Mathlib
import sympy.Basic
import sympy.Analysis.CStarAlgebra.Bicommutant

/--
[bicommutant_finiteDimensional_matrix](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/Bicommutant.lean)
-/
@[path]
private lemma bicommutant_finiteDimensional_matrix_eq
-- given
  (n : ℕ)
  (S : StarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ)) :
-- imply
  (StarSubalgebra.centralizer ℂ
    ((StarSubalgebra.centralizer ℂ (S : Set (Matrix (Fin n) (Fin n) ℂ)) :
      Set (Matrix (Fin n) (Fin n) ℂ))) = S) :=
-- proof
  Complex.CStarAlgebra.Bicommutant.bicommutant_finiteDimensional_matrix n S


-- created on 2026-10-09
