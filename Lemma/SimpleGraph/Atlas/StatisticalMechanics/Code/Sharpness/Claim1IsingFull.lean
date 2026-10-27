import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.Claim1IsingFull.Part3
open SimpleGraph Finset Classical StatMech StatMech.Sharpness StatMech.Sharpness.RandomCurrent


/--
[mem_notConnCompK](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Claim1IsingFull.lean)
-/
@[path]
private lemma mem_notConnCompK_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {o w : V} :
-- imply
  w ∈ notConnCompK ends m o ↔ ¬ connK ends m o w := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.mem_notConnCompK

/--
[noCrossingK_of_event](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Claim1IsingFull.lean)
-/
@[path]
private lemma noCrossingK_of_event_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {m : Finset ι}
  {S : Finset V}
  {o : V}
-- given
  (_ho : o ∉ S)
  (hev : notConnCompK ends m o = S) :
-- imply
  NoCrossingK ends m S := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.noCrossingK_of_event ends m S o _ho hev

/--
[sc1_pair_switching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Claim1IsingFull.lean)
-/
@[path]
private lemma sc1_pair_switching_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {A : Finset V}
  {u v : V}
  {F : Finset ι → ℝ}
-- given
  (hnd : ∀ i, ¬ (ends i).IsDiag)
  (huv : u ≠ v) :
-- imply
  srcPairFamily ends (A ∆ {u, v}) {u, v} F = ∑ m ∈ (Finset.univ.powerset.filter (fun m => sources ends m = A)), (∑ _K ∈ m.powerset.filter (fun K => sources ends K = A), F m * (if connK ends m u v then 1 else 0)) := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.sc1_pair_switching ends hnd A huv F

/--
[sc1_source_set_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Claim1IsingFull.lean)
-/
@[path]
private lemma sc1_source_set_eq_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {o x y g : V}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g) :
-- imply
  ({o, x} : Finset V) ∆ {y, g} = {o, g} ∆ {x, y} := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.sc1_source_set_eq hox hoy hog hxy hxg hyg

/--
[sc1_claim1_switching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Claim1IsingFull.lean)
-/
@[path]
private lemma sc1_claim1_switching_eq
  [DecidableEq ι]
  [DecidableEq V]
  [Fintype V]
  [Fintype ι]
  {ends : ι → Sym2 V}
  {o x y g : V}
  {S : Finset V}
-- given
  (hnd : ∀ i, ¬ (ends i).IsDiag)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g) :
-- imply
  srcPairFamily ends ({o, g} ∆ {x, y}) {y, g} (fun m => if notConnCompK ends m o = S then 1 else 0) = ∑ m ∈ (Finset.univ.powerset.filter (fun m => sources ends m = {o, x})), (∑ _K ∈ m.powerset.filter (fun K => sources ends K = {o, x}), (if notConnCompK ends m o = S then 1 else 0) * (if connK ends m y g then 1 else 0)) := by
-- proof
  apply StatMech.Sharpness.RandomCurrent.sc1_claim1_switching ends hnd o x y g S hox hoy hog hxy hxg hyg


-- created on 2026-10-23
