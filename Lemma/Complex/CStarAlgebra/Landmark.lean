import Mathlib
import sympy.Basic
import sympy.Analysis.CStarAlgebra.Landmark

universe u

/--
[cStarAlgebra_gelfandNaimark](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/Landmark.lean)
-/
@[path]
private lemma cStarAlgebra_gelfandNaimark_eq
-- given
  (A : Type u) [CStarAlgebra A] :
-- imply
  (∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H) (π : StarAlgHom ℂ A (H →L[ℂ] H)), Function.Injective π ∧ ∀ a : A, ‖π a‖ = ‖a‖) :=
-- proof
  Analysis.CStarAlgebra.LandmarkWanted.cStarAlgebra_gelfandNaimark A


-- created on 2026-10-09
