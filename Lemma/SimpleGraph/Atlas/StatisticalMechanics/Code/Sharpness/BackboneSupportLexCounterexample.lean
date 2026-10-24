import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Sharpness.BackboneSupportLexCounterexample
open Finset StatMech StatMech.Sharpness


/--
[shbK4_selectsDirect03_iff_pathEnumeration](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexCounterexample.lean)
-/
@[path]
private lemma shbK4_selectsDirect03_iff_pathEnumeration_eq
  {A : Finset shbK4Edge} :
-- imply
  shbK4SelectsDirect03 A ↔ shbK4Boundary A = {0, 3} ∧ shbK4SupportsPath A shbK4Path03.p03 ∧ ∀ p, p ≠ shbK4Path03.p03 → ¬ shbK4SupportsPath A p := by
-- proof
  apply StatMech.Sharpness.shbK4_selectsDirect03_iff_pathEnumeration A

/--
[shbK4H_masses_at_two_thirds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexCounterexample.lean)
-/
@[path]
private lemma shbK4H_masses_at_two_thirds_eq :
-- imply
  shbK4DirectFiberMass shbK4H (2 / 3) = 2 / 3 ∧ shbK4VacuumMass shbK4H (2 / 3) = 145 / 81 := by
-- proof
  apply StatMech.Sharpness.shbK4H_masses_at_two_thirds

/--
[shbK4G_masses_at_two_thirds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexCounterexample.lean)
-/
@[path]
private lemma shbK4G_masses_at_two_thirds_eq :
-- imply
  shbK4DirectFiberMass shbK4G (2 / 3) = 86 / 81 ∧ shbK4VacuumMass shbK4G (2 / 3) = 25 / 9 := by
-- proof
  apply StatMech.Sharpness.shbK4G_masses_at_two_thirds

/--
[shbK4_rhos_at_two_thirds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexCounterexample.lean)
-/
@[path]
private lemma shbK4_rhos_at_two_thirds_eq :
-- imply
  shbK4DirectRho shbK4H (2 / 3) = 54 / 145 ∧ shbK4DirectRho shbK4G (2 / 3) = 86 / 225 := by
-- proof
  apply StatMech.Sharpness.shbK4_rhos_at_two_thirds

/--
[shb_supportLex_edgeDomain_P3_counterexample](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexCounterexample.lean)
-/
@[path]
private lemma shb_supportLex_edgeDomain_P3_counterexample_eq :
-- imply
  shbK4DirectRho shbK4H (2 / 3) < shbK4DirectRho shbK4G (2 / 3) := by
-- proof
  apply StatMech.Sharpness.shb_supportLex_edgeDomain_P3_counterexample

/--
[shbK4H_ssubset_shbK4G](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexCounterexample.lean)
-/
@[path]
private lemma shbK4H_ssubset_shbK4G_eq :
-- imply
  shbK4H ⊂ shbK4G := by
-- proof
  apply StatMech.Sharpness.shbK4H_ssubset_shbK4G


-- created on 2026-10-23
