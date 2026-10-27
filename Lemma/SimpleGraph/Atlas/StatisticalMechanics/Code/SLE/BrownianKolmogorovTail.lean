import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.SLE.BrownianKolmogorovTail
open MeasureTheory ProbabilityTheory StatMech StatMech.SLE


/--
[brownianCoordinateProcess_measure_edist_rpow_four_ge_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianKolmogorovTail.lean)
-/
@[path]
private lemma brownianCoordinateProcess_measure_edist_rpow_four_ge_le_eq
  {s t : Real}
  {epsilon : ENNReal}
-- given
  (hepsilon : Ne epsilon 0)
  (hepsilonTop : Ne epsilon (⊤ : ENNReal)) :
-- imply
  brownianProductLaw {omega | epsilon <= edist (brownianCoordinateProcess s omega) (brownianCoordinateProcess t omega) ^ (4 : Real)} <= ((3 : NNReal) * edist s t ^ (2 : Real)) / epsilon := by
-- proof
  apply StatMech.SLE.brownianCoordinateProcess_measure_edist_rpow_four_ge_le s t epsilon hepsilon hepsilonTop

/--
[brownianCoordinateProcess_measure_edist_ge_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianKolmogorovTail.lean)
-/
@[path]
private lemma brownianCoordinateProcess_measure_edist_ge_le_eq
  {s t : Real}
  {delta : ENNReal}
-- given
  (hdelta : Ne delta 0)
  (hdeltaTop : Ne delta (⊤ : ENNReal)) :
-- imply
  brownianProductLaw {omega | delta <= edist (brownianCoordinateProcess s omega) (brownianCoordinateProcess t omega)} <= ((3 : NNReal) * edist s t ^ (2 : Real)) / delta ^ (4 : Nat) := by
-- proof
  apply StatMech.SLE.brownianCoordinateProcess_measure_edist_ge_le s t delta hdelta hdeltaTop


-- created on 2026-10-23
