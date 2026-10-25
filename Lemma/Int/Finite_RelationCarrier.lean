import Mathlib
import sympy.Basic
import Lemma.GroupCohomology.TateCohomology
import Lemma.GroupCohomology.TateSeam
import Lemma.GroupCohomology.TateShiftMaps
import Def.GroupCohomology_CochainCup
import Lemma.Definitions.Def_GroupCohomology_IsGradedCupProduct
import Lemma.Definitions.Def_GroupCohomology_IsTateCupProduct
import Lemma.GroupCohomology.RelationModule
import Lemma.Int.P2MUtil
open CategoryTheory Rep CategoryTheory.MonoidalCategory


/--
[Rep_moduleFinite_relationCarrier](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Rep_moduleFinite_relationCarrier.lean)
-/
@[path]
private lemma main
  [Group G] [Fintype G]
  {B : Rep ℤ G} [Fintype B] :
-- imply
  Module.Finite ℤ (Rep.relationCarrier B) := by
-- proof
  have h : Module.Finite ℤ (Rep.relationModule B) := inferInstance
  unfold Rep.relationCarrier
  convert h
  rfl
  rfl


-- created on 2026-10-24
