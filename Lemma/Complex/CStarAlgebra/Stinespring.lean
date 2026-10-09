import Mathlib
import sympy.Basic
import sympy.Analysis.CStarAlgebra.Stinespring

universe u

/--
[stinespring_dilation](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/Stinespring.lean)
-/
@[path]
private lemma stinespring_dilation_eq
-- given
  {A H : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (φ : CompletelyPositiveMap A (H →L[ℂ] H)) :
-- imply
  (∃ (K : Type u) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K) (_ : CompleteSpace K) (π : StarAlgHom ℂ A (K →L[ℂ] K)) (V : H →L[ℂ] K), ∀ a : A, ∀ x : H, φ a x = ContinuousLinearMap.adjoint V (π a (V x))) :=
-- proof
  Analysis.CStarAlgebra.StinespringWanted.stinespring_dilation φ


-- created on 2026-10-09
