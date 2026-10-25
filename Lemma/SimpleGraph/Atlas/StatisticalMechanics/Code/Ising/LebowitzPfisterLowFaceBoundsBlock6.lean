import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterLowFaceBoundsBlock6
open StatMech StatMech.Ising StatMech.Ising.LowFaceCertificate


/--
[radializedCrossCoeff_bounds_at_six](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceBoundsBlock6.lean)
-/
@[path]
private lemma radializedCrossCoeff_bounds_at_six_eq :
-- imply
  forall (j k : Fin 8) (t : TriTerm), t ∈ (radialize (crossCoeffPoly 6 j k)).terms -> t.ex <= 6 ∧ t.ey <= 6 ∧ t.ez <= 3 := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.radializedCrossCoeff_bounds_at_six

/--
[crossCoeff_bounds_at_six](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceBoundsBlock6.lean)
-/
@[path]
private lemma crossCoeff_bounds_at_six_eq :
-- imply
  forall (j k : Fin 8) (t : TriTerm), t ∈ (crossCoeffPoly 6 j k).terms -> 3 <= t.ex + t.ey + t.ez ∧ t.ex + t.ey + t.ez <= 6 := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.crossCoeff_bounds_at_six


-- created on 2026-10-23
