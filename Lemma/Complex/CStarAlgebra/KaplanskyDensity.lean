import Mathlib
import sympy.Basic
import sympy.Analysis.CStarAlgebra.KaplanskyDensity

open Analysis.CStarAlgebra.KaplanskyDensityWanted

/--
[kaplansky_density_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/KaplanskyDensity.lean)
-/
@[path]
private lemma kaplansky_density_theorem_eq
-- given
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
-- imply
  (closure ({x : PointwiseConvergenceCLM (RingHom.id ℂ) H H |
      toBounded x ∈ (S : Set (H →L[ℂ] H)) ∧ ‖toBounded x‖ ≤ 1} :
    Set (PointwiseConvergenceCLM (RingHom.id ℂ) H H))
  = {y : PointwiseConvergenceCLM (RingHom.id ℂ) H H |
    y ∈ closure ({p : PointwiseConvergenceCLM (RingHom.id ℂ) H H |
        toBounded p ∈ (S : Set (H →L[ℂ] H))} :
      Set (PointwiseConvergenceCLM (RingHom.id ℂ) H H)) ∧
    ‖toBounded y‖ ≤ 1}) :=
-- proof
  kaplansky_density_theorem S


-- created on 2026-10-09
