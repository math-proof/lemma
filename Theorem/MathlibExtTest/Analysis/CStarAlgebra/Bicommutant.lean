/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/CStarAlgebra/Bicommutant.lean -/

/-
Author: @toskua, Avocado
-/
import Theorem.Analysis.CStarAlgebra.Bicommutant.Part6
open MathlibExt.Analysis.CStarAlgebra.Bicommutant

/-!
# Tests for the finite-dimensional matrix bicommutant theorem.
-/


-- Ordinary finite case: an arbitrary star subalgebra equals its own bicommutant.
example (S : StarSubalgebra ℂ (Matrix (Fin 2) (Fin 2) ℂ)) :
    StarSubalgebra.centralizer ℂ
        ((StarSubalgebra.centralizer ℂ (S : Set (Matrix (Fin 2) (Fin 2) ℂ)) :
          Set (Matrix (Fin 2) (Fin 2) ℂ))) = S :=
  bicommutant_finiteDimensional_matrix 2 S

-- Degenerate boundary: the statement also holds for `n = 0`.
example (S : StarSubalgebra ℂ (Matrix (Fin 0) (Fin 0) ℂ)) :
    StarSubalgebra.centralizer ℂ
        ((StarSubalgebra.centralizer ℂ (S : Set (Matrix (Fin 0) (Fin 0) ℂ)) :
          Set (Matrix (Fin 0) (Fin 0) ℂ))) = S :=
  bicommutant_finiteDimensional_matrix 0 S

-- The full algebra is its own bicommutant at another ordinary size.
example :
    StarSubalgebra.centralizer ℂ
        ((StarSubalgebra.centralizer ℂ
          ((⊤ : StarSubalgebra ℂ (Matrix (Fin 3) (Fin 3) ℂ)) :
            Set (Matrix (Fin 3) (Fin 3) ℂ)) :
          Set (Matrix (Fin 3) (Fin 3) ℂ))) =
      (⊤ : StarSubalgebra ℂ (Matrix (Fin 3) (Fin 3) ℂ)) :=
  bicommutant_finiteDimensional_matrix 3 ⊤

