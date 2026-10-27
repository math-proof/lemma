import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.Rot90Reindex
open Set MeasureTheory ProbabilityTheory SimpleGraph StatMech StatMech.Universality


/--
[r90_reindex_measurePreserving](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/Rot90Reindex.lean)
-/
@[path]
private lemma r90_reindex_measurePreserving_eq :
-- imply
  MeasurePreserving (Equiv.piCongrLeft (fun _ => Bool) (crossEdge : Sym2 (Site 2) ≃ Sym2 (Site 2))) rba_selfDualMeasure rba_selfDualMeasure := by
-- proof
  apply StatMech.Universality.r90_reindex_measurePreserving

/--
[r90_complement_measurePreserving](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/Rot90Reindex.lean)
-/
@[path]
private lemma r90_complement_measurePreserving_eq :
-- imply
  MeasurePreserving (fun (η : ConfigSpace (Sym2 (Site 2))) e => !(η e)) rba_selfDualMeasure rba_selfDualMeasure := by
-- proof
  apply StatMech.Universality.r90_complement_measurePreserving

/--
[r90_dual_measurePreserving](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/Rot90Reindex.lean)
-/
@[path]
private lemma r90_dual_measurePreserving_eq :
-- imply
  MeasurePreserving (dualConfig : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2))) rba_selfDualMeasure rba_selfDualMeasure := by
-- proof
  apply StatMech.Universality.r90_dual_measurePreserving

/--
[r90_dual_eq_complement_comp_reindex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/Rot90Reindex.lean)
-/
@[path]
private lemma r90_dual_eq_complement_comp_reindex_eq :
-- imply
  MeasurePreserving ((fun (η : ConfigSpace (Sym2 (Site 2))) e => !(η e)) ∘ (Equiv.piCongrLeft (fun _ => Bool) (crossEdge : Sym2 (Site 2) ≃ Sym2 (Site 2)))) rba_selfDualMeasure rba_selfDualMeasure := by
-- proof
  apply StatMech.Universality.r90_dual_eq_complement_comp_reindex

/--
[r90_negConfig_measurePreserving](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/Rot90Reindex.lean)
-/
@[path]
private lemma r90_negConfig_measurePreserving_eq :
-- imply
  MeasurePreserving (des_negConfig : ConfigSpace (Sym2 (Site 2)) → ConfigSpace (Sym2 (Site 2))) rba_selfDualMeasure rba_selfDualMeasure := by
-- proof
  apply StatMech.Universality.r90_negConfig_measurePreserving

/--
[r90_dualV_prob_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/Rot90Reindex.lean)
-/
@[path]
private lemma r90_dualV_prob_eq_eq
  {n : ℤ}
-- given
  (hmeasV : MeasurableSet (verticalCrossingEvent 0 n 0 n)) :
-- imply
  rba_selfDualMeasure.real (dualVerticalCrossingEvent 0 n 0 n) = rba_selfDualMeasure.real (verticalCrossingEvent 0 n 0 n) := by
-- proof
  apply StatMech.Universality.r90_dualV_prob_eq n hmeasV

/--
[r90_dualV_eq_primalH](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/Rot90Reindex.lean)
-/
@[path]
private lemma r90_dualV_eq_primalH_eq
  {n : ℤ}
-- given
  (hmeasV : MeasurableSet (verticalCrossingEvent 0 n 0 n))
  (hmeasH : MeasurableSet (horizontalCrossingEvent 0 n 0 n)) :
-- imply
  rba_selfDualMeasure.real (dualVerticalCrossingEvent 0 n 0 n) = rba_selfDualMeasure.real (horizontalCrossingEvent 0 n 0 n) := by
-- proof
  apply StatMech.Universality.r90_dualV_eq_primalH n hmeasV hmeasH


-- created on 2026-10-23
