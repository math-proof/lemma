import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.LebowitzPfisterLowFaceCertificate
open StatMech StatMech.Ising StatMech.Ising.LowFaceCertificate


/--
[radialBernCoeff_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceCertificate.lean)
-/
@[path]
private lemma radialBernCoeff_nonneg_eq :
-- imply
  ∀ (i j k : Fin 8) (a : Fin 13) (b : Fin 8) (c : Fin 4), 0 <= radialBernCoeff i j k a b c := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.radialBernCoeff_nonneg

/--
[radializedCrossCoeff_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceCertificate.lean)
-/
@[path]
private lemma radializedCrossCoeff_bounds_eq :
-- imply
  ∀ (i j k : Fin 8) (t : TriTerm), t ∈ (radialize (crossCoeffPoly i j k)).terms -> t.ex <= 6 ∧ t.ey <= 6 ∧ t.ez <= 3 := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.radializedCrossCoeff_bounds

/--
[crossCoeff_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceCertificate.lean)
-/
@[path]
private lemma crossCoeff_bounds_eq :
-- imply
  ∀ (i j k : Fin 8) (t : TriTerm), t ∈ (crossCoeffPoly i j k).terms -> 3 <= t.ex + t.ey + t.ez ∧ t.ex + t.ey + t.ez <= 6 := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.crossCoeff_bounds


-- created on 2026-10-23
