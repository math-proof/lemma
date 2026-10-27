import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc11compressionengine
open Finset StatMech StatMech.Walls


/--
[rc11_engine_count_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11compressionengine.lean)
-/
@[path]
private lemma rc11_engine_count_identity_eq
  [DecidableEq β]
  {𝒜 ℬ : Finset (Finset β)} :
-- imply
  (boxDoubled 𝒜 ℬ).card = dpairsCount 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc11_engine_count_identity 𝒜 ℬ

/--
[rc11_engine_downDown_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11compressionengine.lean)
-/
@[path]
private lemma rc11_engine_downDown_mono_eq
  [DecidableEq β]
  {𝒜 ℬ : Finset (Finset β)}
  {i : β} :
-- imply
  dpairsCount 𝒜 ℬ ≤ dpairsCount (Down.compression i 𝒜) (Down.compression i ℬ) := by
-- proof
  apply StatMech.Walls.rc11_engine_downDown_mono 𝒜 ℬ i

/--
[rc11_engine_deficit_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11compressionengine.lean)
-/
@[path]
private lemma rc11_engine_deficit_identity_eq
  [DecidableEq β]
  {𝒜 ℬ : Finset (Finset β)}
  {i : β} :
-- imply
  (dpairsCount (Down.compression i 𝒜) (Down.compression i ℬ) : ℤ) - dpairsCount 𝒜 ℬ = (dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i) : ℤ) - dpairsCount (𝒜.memberSubfamily i ∩ 𝒜.nonMemberSubfamily i) (ℬ.memberSubfamily i ∩ ℬ.nonMemberSubfamily i) := by
-- proof
  apply StatMech.Walls.rc11_engine_deficit_identity 𝒜 ℬ i

/--
[rc11_engine_sweep_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11compressionengine.lean)
-/
@[path]
private lemma rc11_engine_sweep_card_eq
  [DecidableEq β]
  {cs : List β}
  {𝒜 : Finset (Finset β)} :
-- imply
  (iterDownComp cs 𝒜).card = 𝒜.card := by
-- proof
  apply StatMech.Walls.rc11_engine_sweep_card cs 𝒜

/--
[rc11_engine_converges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11compressionengine.lean)
-/
@[path]
private lemma rc11_engine_converges_eq
  [DecidableEq β]
  {𝒜 ℬ : Finset (Finset β)} :
-- imply
  ∃ cs : List β, IsLowerSet ((iterDownComp cs 𝒜) : Set (Finset β)) ∧ dpairsCount 𝒜 ℬ ≤ dpairsCount (iterDownComp cs 𝒜) (iterDownComp cs ℬ) := by
-- proof
  apply StatMech.Walls.rc11_engine_converges 𝒜 ℬ

/--
[rc11_engine_harrisKleitman](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11compressionengine.lean)
-/
@[path]
private lemma rc11_engine_harrisKleitman_eq
  [DecidableEq β]
  {𝒜 ℬ : Finset (Finset β)}
  {i : β}
-- given
  (h𝒜 : IsLowerSet (𝒜 : Set (Finset β)))
  (hℬ : IsLowerSet (ℬ : Set (Finset β))) :
-- imply
  dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i) ≤ dpairsCount (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i) := by
-- proof
  apply StatMech.Walls.rc11_engine_harrisKleitman 𝒜 ℬ h𝒜 hℬ i

/--
[rc11_compressionEngine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11compressionengine.lean)
-/
@[path]
private lemma rc11_compressionEngine_eq
  [DecidableEq β]
  {𝒜 ℬ : Finset (Finset β)} :
-- imply
  ((boxDoubled 𝒜 ℬ).card = dpairsCount 𝒜 ℬ) ∧ (∀ i : β, dpairsCount 𝒜 ℬ ≤ dpairsCount (Down.compression i 𝒜) (Down.compression i ℬ)) ∧ (∀ i : β, (dpairsCount (Down.compression i 𝒜) (Down.compression i ℬ) : ℤ) - dpairsCount 𝒜 ℬ = (dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i) : ℤ) - dpairsCount (𝒜.memberSubfamily i ∩ 𝒜.nonMemberSubfamily i) (ℬ.memberSubfamily i ∩ ℬ.nonMemberSubfamily i)) ∧ (∀ cs : List β, (iterDownComp cs 𝒜).card = 𝒜.card) ∧ (∃ cs : List β, IsLowerSet ((iterDownComp cs 𝒜) : Set (Finset β)) ∧ dpairsCount 𝒜 ℬ ≤ dpairsCount (iterDownComp cs 𝒜) (iterDownComp cs ℬ)) ∧ (IsLowerSet (𝒜 : Set (Finset β)) → IsLowerSet (ℬ : Set (Finset β)) → ∀ i : β, dpairsCount (𝒜.memberSubfamily i) (ℬ.memberSubfamily i) ≤ dpairsCount (𝒜.nonMemberSubfamily i) (ℬ.nonMemberSubfamily i)) := by
-- proof
  apply StatMech.Walls.rc11_compressionEngine 𝒜 ℬ

/--
[rc11_compressionEngine_eq_core](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11compressionengine.lean)
-/
@[path]
private lemma rc11_compressionEngine_eq_core_eq
  [DecidableEq β]
  {𝒜 ℬ : Finset (Finset β)} :
-- imply
  rc11_compressionEngine 𝒜 ℬ = rc5_core_compressionEngine 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc11_compressionEngine_eq_core 𝒜 ℬ

/--
[rc11_engine_gain_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11compressionengine.lean)
-/
@[path]
private lemma rc11_engine_gain_nonneg_eq
  [DecidableEq β]
  {𝒜 ℬ : Finset (Finset β)}
  {i : β} :
-- imply
  (0 : ℤ) ≤ (dpairsCount (Down.compression i 𝒜) (Down.compression i ℬ) : ℤ) - dpairsCount 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc11_engine_gain_nonneg 𝒜 ℬ i

/--
[rc11_engine_count_identity_collapse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11compressionengine.lean)
-/
@[path]
private lemma rc11_engine_count_identity_collapse_eq :
-- imply
  (boxDoubled rc5_collapseFamily rc5_collapseFamily).card = 3 := by
-- proof
  apply StatMech.Walls.rc11_engine_count_identity_collapse

/--
[rc11_engine_count_identity_empty_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc11compressionengine.lean)
-/
@[path]
private lemma rc11_engine_count_identity_empty_left_eq
  [DecidableEq β]
  {ℬ : Finset (Finset β)} :
-- imply
  (boxDoubled (∅ : Finset (Finset β)) ℬ).card = 0 := by
-- proof
  apply StatMech.Walls.rc11_engine_count_identity_empty_left ℬ


-- created on 2026-10-23
