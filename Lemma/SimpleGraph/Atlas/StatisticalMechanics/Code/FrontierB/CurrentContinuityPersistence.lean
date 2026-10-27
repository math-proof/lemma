import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentContinuityPersistence
open MeasureTheory Set StatMech StatMech.FrontierB


/--
[inverse_smul_origin_not_mem_box_of_not_mem_originShiftBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityPersistence.lean)
-/
@[path]
private lemma inverse_smul_origin_not_mem_box_of_not_mem_originShiftBox_eq
  {d R : Nat}
  {g : Multiplicative (Site d)}
-- given
  (hg : g ∉ originShiftBox d R) :
-- imply
  g⁻¹ • origin d ∉ box d R := by
-- proof
  apply StatMech.FrontierB.inverse_smul_origin_not_mem_box_of_not_mem_originShiftBox g hg

/--
[currentContinuityPercolationPrinciple_of_genMixing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentContinuityPersistence.lean)
-/
@[path]
private lemma currentContinuityPercolationPrinciple_of_genMixing_eq
  {d : Nat}
  {rho : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))}
-- given
  (hd : 1 ≤ d)
  (hti : IsTranslationInvariant (G := Multiplicative (Site d)) (rho : Measure (ConfigSpace (Sym2 (Site d)))))
  (hmix : fmu_GenMixing (G := Multiplicative (Site d)) (rho : Measure (ConfigSpace (Sym2 (Site d)))))
  (hunique : (rho : Measure (ConfigSpace (Sym2 (Site d)))) (atLeastTwoInfinite d) = 0) :
-- imply
  CurrentContinuityPercolationPrinciple d (rho : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FrontierB.currentContinuityPercolationPrinciple_of_genMixing d hd rho hti hmix hunique


-- created on 2026-10-23
