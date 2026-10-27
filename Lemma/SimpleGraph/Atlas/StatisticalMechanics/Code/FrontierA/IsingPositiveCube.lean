import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingPositiveCube.Part2
open Finset Set StatMech StatMech.FrontierA


/--
[isingPositiveCube_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingPositiveCube.lean)
-/
@[path]
private lemma isingPositiveCube_card_eq
  {d m k : Nat}
  {d m : Nat} :
-- imply
  (isingPositiveCube d m).card = m ^ d := by
-- proof
  apply StatMech.FrontierA.isingPositiveCube_card d m

/--
[isingPositiveCube_subset_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingPositiveCube.lean)
-/
@[path]
private lemma isingPositiveCube_subset_box_eq
  {d m k : Nat}
  {d m : Nat} :
-- imply
  (isingPositiveCube d m : Set (Site d)) ⊆ box d m := by
-- proof
  apply StatMech.FrontierA.isingPositiveCube_subset_box d m

/--
[isingPositiveCube_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingPositiveCube.lean)
-/
@[path]
private lemma isingPositiveCube_nonempty_eq
  {d m k : Nat}
  {d m : Nat}
-- given
  (hm : 1 <= m) :
-- imply
  (isingPositiveCube d m).Nonempty := by
-- proof
  apply StatMech.FrontierA.isingPositiveCube_nonempty d m hm

/--
[isingPositiveCube_difference_l1_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingPositiveCube.lean)
-/
@[path]
private lemma isingPositiveCube_difference_l1_le_eq
  {d m k : Nat}
  {a b : Site d}
-- given
  (ha : a ∈ isingPositiveCube d m)
  (hb : b ∈ isingPositiveCube d m) :
-- imply
  (∑ i, (b i - a i).natAbs) <= d * m := by
-- proof
  apply StatMech.FrontierA.isingPositiveCube_difference_l1_le ha hb

/--
[isingPositiveCube_difference_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingPositiveCube.lean)
-/
@[path]
private lemma isingPositiveCube_difference_mem_box_eq
  {d m k : Nat}
  {a b : Site d}
-- given
  (ha : a ∈ isingPositiveCube d m)
  (hb : b ∈ isingPositiveCube d m) :
-- imply
  b - a ∈ box d m := by
-- proof
  apply StatMech.FrontierA.isingPositiveCube_difference_mem_box ha hb

/--
[isingTorusPositiveCube_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingPositiveCube.lean)
-/
@[path]
private lemma isingTorusPositiveCube_card_eq
  {d m k : Nat}
-- given
  (hside : 2 * m < isingDyadicSide k) :
-- imply
  (isingTorusPositiveCube d m k).card = m ^ d := by
-- proof
  apply StatMech.FrontierA.isingTorusPositiveCube_card hside

/--
[isingTorusPositiveCube_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingPositiveCube.lean)
-/
@[path]
private lemma isingTorusPositiveCube_nonempty_eq
  {d m k : Nat}
-- given
  (hm : 1 <= m) :
-- imply
  (isingTorusPositiveCube d m k).Nonempty := by
-- proof
  apply StatMech.FrontierA.isingTorusPositiveCube_nonempty hm

/--
[finiteTorusBlockDifferenceAverage_image](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingPositiveCube.lean)
-/
@[path]
private lemma finiteTorusBlockDifferenceAverage_image_eq
  {d m k : Nat}
  [Fintype Gamma]
  [DecidableEq Gamma]
  [AddCommGroup Gamma]
  {S : Finset (Site d)}
-- given
  (G : Gamma -> Real)
  (f : Site d -> Gamma)
  (hf : Set.InjOn f (S : Set (Site d))) :
-- imply
  finiteTorusBlockDifferenceAverage G (S.image f) = (1 / (S.card : Real) ^ 2) * ∑ a ∈ S, ∑ b ∈ S, G (f b - f a) := by
-- proof
  apply StatMech.FrontierA.finiteTorusBlockDifferenceAverage_image G S f hf

/--
[exists_isingTorusPositiveCube_green_le_power](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingPositiveCube.lean)
-/
@[path]
private lemma exists_isingTorusPositiveCube_green_le_power_eq
  {d m k : Nat}
  {d : Nat}
-- given
  (hd : 2 < d) :
-- imply
  ∃ C : Real, 0 < C ∧ ∀ m : Nat, 2 <= m -> ∀ᶠ k : Nat in Filter.atTop, finiteTorusBlockDifferenceAverage (finiteTorusZeroModeGreen (isingTorusCharacterDispersion (d := d) (k := k))) (isingTorusPositiveCube d m k) <= C / (m : Real) ^ (d - 2) := by
-- proof
  apply StatMech.FrontierA.exists_isingTorusPositiveCube_green_le_power hd


-- created on 2026-10-23
