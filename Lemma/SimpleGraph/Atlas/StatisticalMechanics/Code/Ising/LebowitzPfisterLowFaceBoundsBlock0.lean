import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.LebowitzPfisterLowFaceBoundsBlock0
open StatMech StatMech.Ising StatMech.Ising.LowFaceCertificate


/--
[radializedCrossCoeff_bounds_at_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceBoundsBlock0.lean)
-/
@[path]
private lemma radializedCrossCoeff_bounds_at_zero_eq :
-- imply
  forall (j k : Fin 8) (t : TriTerm), t ∈ (radialize (crossCoeffPoly 0 j k)).terms -> t.ex <= 6 ∧ t.ey <= 6 ∧ t.ez <= 3 := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.radializedCrossCoeff_bounds_at_zero

/--
[crossCoeff_bounds_at_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceBoundsBlock0.lean)
-/
@[path]
private lemma crossCoeff_bounds_at_zero_eq :
-- imply
  forall (j k : Fin 8) (t : TriTerm), t ∈ (crossCoeffPoly 0 j k).terms -> 3 <= t.ex + t.ey + t.ez ∧ t.ex + t.ey + t.ez <= 6 := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.crossCoeff_bounds_at_zero


-- created on 2026-10-23
