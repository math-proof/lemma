import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc2_dpairsdowndownmono
open Finset StatMech StatMech.Walls


/--
[rc2_downComp_nonMemberSubfamily](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_dpairsdowndownmono.lean)
-/
@[path]
private lemma rc2_downComp_nonMemberSubfamily_eq
  [DecidableEq α]
  {i : α}
  {𝒜 : Finset (Finset α)} :
-- imply
  (Down.compression i 𝒜).nonMemberSubfamily i = 𝒜.memberSubfamily i ∪ 𝒜.nonMemberSubfamily i := by
-- proof
  apply StatMech.Walls.rc2_downComp_nonMemberSubfamily i 𝒜

/--
[rc2_downComp_memberSubfamily](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_dpairsdowndownmono.lean)
-/
@[path]
private lemma rc2_downComp_memberSubfamily_eq
  [DecidableEq α]
  {i : α}
  {𝒜 : Finset (Finset α)} :
-- imply
  (Down.compression i 𝒜).memberSubfamily i = 𝒜.memberSubfamily i ∩ 𝒜.nonMemberSubfamily i := by
-- proof
  apply StatMech.Walls.rc2_downComp_memberSubfamily i 𝒜

/--
[rc2_fiber_downDown_ineq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_dpairsdowndownmono.lean)
-/
@[path]
private lemma rc2_fiber_downDown_ineq_eq
  [DecidableEq α]
  {am an bm bn : Finset (Finset α)} :
-- imply
  dpairsCount an bn + dpairsCount am bn + dpairsCount an bm ≤ dpairsCount (am ∪ an) (bm ∪ bn) + dpairsCount (am ∩ an) (bm ∪ bn) + dpairsCount (am ∪ an) (bm ∩ bn) := by
-- proof
  apply StatMech.Walls.rc2_fiber_downDown_ineq am an bm bn

/--
[rc2_dpairsCount_downDown_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_dpairsdowndownmono.lean)
-/
@[path]
private lemma rc2_dpairsCount_downDown_mono_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {i : α} :
-- imply
  dpairsCount 𝒜 ℬ ≤ dpairsCount (Down.compression i 𝒜) (Down.compression i ℬ) := by
-- proof
  apply StatMech.Walls.rc2_dpairsCount_downDown_mono 𝒜 ℬ i

/--
[rc2_deficit_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_dpairsdowndownmono.lean)
-/
@[path]
private lemma rc2_deficit_identity_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {i : α} :
-- imply
  (dpairsCount (Down.compression i 𝒜) (Down.compression i ℬ) : ℤ) - dpairsCount 𝒜 ℬ = (dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i) : ℤ) - dpairsCount (𝒜.memberSubfamily i ∩ 𝒜.nonMemberSubfamily i) (ℬ.memberSubfamily i ∩ ℬ.nonMemberSubfamily i) := by
-- proof
  apply StatMech.Walls.rc2_deficit_identity 𝒜 ℬ i

/--
[rc2_deficit_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_dpairsdowndownmono.lean)
-/
@[path]
private lemma rc2_deficit_nonneg_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {i : α} :
-- imply
  (0 : ℤ) ≤ (dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i) : ℤ) - dpairsCount (𝒜.memberSubfamily i ∩ 𝒜.nonMemberSubfamily i) (ℬ.memberSubfamily i ∩ ℬ.nonMemberSubfamily i) := by
-- proof
  apply StatMech.Walls.rc2_deficit_nonneg 𝒜 ℬ i

/--
[rc2_card_boxDoubled_downDown_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc2_dpairsdowndownmono.lean)
-/
@[path]
private lemma rc2_card_boxDoubled_downDown_mono_eq
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)}
  {i : α} :
-- imply
  (boxDoubled 𝒜 ℬ).card ≤ (boxDoubled (Down.compression i 𝒜) (Down.compression i ℬ)).card := by
-- proof
  apply StatMech.Walls.rc2_card_boxDoubled_downDown_mono 𝒜 ℬ i


-- created on 2026-10-23
