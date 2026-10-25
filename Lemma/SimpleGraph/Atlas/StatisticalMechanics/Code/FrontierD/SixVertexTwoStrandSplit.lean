import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexTwoStrandSplit
open StatMech StatMech.FrontierD


/--
[exists_list_prefix_sum_eq_of_unitSteps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexTwoStrandSplit.lean)
-/
@[path]
private lemma exists_list_prefix_sum_eq_of_unitSteps_eq
  {steps : List Int}
  {target total : Int}
-- given
  (hsteps : ∀ z ∈ steps, z = 1 \/ z = -1)
  (hsum : steps.sum = total)
  (htarget_nonneg : 0 <= target)
  (htarget_le : target <= total) :
-- imply
  ∃ pre suf : List Int, steps = pre ++ suf /\ pre.sum = target := by
-- proof
  apply StatMech.FrontierD.exists_list_prefix_sum_eq_of_unitSteps steps hsteps target total hsum htarget_nonneg htarget_le

/--
[exists_two_unit_sum_arcs_of_sum_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexTwoStrandSplit.lean)
-/
@[path]
private lemma exists_two_unit_sum_arcs_of_sum_eq_two_eq
  {steps : List Int}
-- given
  (hsteps : ∀ z ∈ steps, z = 1 \/ z = -1)
  (hsum : steps.sum = 2) :
-- imply
  ∃ first second : List Int, steps = first ++ second /\ first.sum = 1 /\ second.sum = 1 := by
-- proof
  apply StatMech.FrontierD.exists_two_unit_sum_arcs_of_sum_eq_two steps hsteps hsum

/--
[exists_two_unit_arcs_of_degreeTwoStrandSeamWord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexTwoStrandSplit.lean)
-/
@[path]
private lemma exists_two_unit_arcs_of_degreeTwoStrandSeamWord_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {seed : SixVertexOrientedDisagreementDart omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (hsum : (sixVertexDegreeTwoStrandSeamWord homega heta hdegree seed).sum = 2) :
-- imply
  ∃ first second : List Int, sixVertexDegreeTwoStrandSeamWord homega heta hdegree seed = first ++ second /\ first.sum = 1 /\ second.sum = 1 := by
-- proof
  apply StatMech.FrontierD.exists_two_unit_arcs_of_degreeTwoStrandSeamWord homega heta hdegree seed hsum

/--
[exists_two_unit_arcs_of_all_degreeTwoStrands](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexTwoStrandSplit.lean)
-/
@[path]
private lemma exists_two_unit_arcs_of_all_degreeTwoStrands_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {n : Nat}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
  (hn : 0 < n) :
-- imply
  ∃ first second : List Int, sixVertexDegreeTwoAllStrandsSeamWord homega heta hdegree = first ++ second /\ first.sum = 1 /\ second.sum = 1 := by
-- proof
  apply StatMech.FrontierD.exists_two_unit_arcs_of_all_degreeTwoStrands homega heta hdegree n homegaSector hetaSector hn


-- created on 2026-10-23
