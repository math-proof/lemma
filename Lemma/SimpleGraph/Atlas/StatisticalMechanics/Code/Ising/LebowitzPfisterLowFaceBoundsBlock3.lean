import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterLowFaceBoundsBlock3
open StatMech StatMech.Ising StatMech.Ising.LowFaceCertificate


/--
[radializedCrossCoeff_bounds_at_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceBoundsBlock3.lean)
-/
@[path]
private lemma radializedCrossCoeff_bounds_at_three_eq :
-- imply
  forall (j k : Fin 8) (t : TriTerm), t ∈ (radialize (crossCoeffPoly 3 j k)).terms -> t.ex <= 6 ∧ t.ey <= 6 ∧ t.ez <= 3 := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.radializedCrossCoeff_bounds_at_three

/--
[crossCoeff_bounds_at_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceBoundsBlock3.lean)
-/
@[path]
private lemma crossCoeff_bounds_at_three_eq :
-- imply
  forall (j k : Fin 8) (t : TriTerm), t ∈ (crossCoeffPoly 3 j k).terms -> 3 <= t.ex + t.ey + t.ez ∧ t.ex + t.ey + t.ez <= 6 := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.crossCoeff_bounds_at_three


-- created on 2026-10-23
