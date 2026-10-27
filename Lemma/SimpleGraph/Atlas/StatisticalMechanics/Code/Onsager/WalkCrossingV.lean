import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.WalkCrossingV.Part2
open StatMech StatMech.Onsager StatMech.Onsager.WalkCrossingV


/--
[fst_step_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCrossingV.lean)
-/
@[path]
private lemma fst_step_bound_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {k : Fin n}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0) :
-- imply
  (pos d (k + 1)).1 = (pos d k).1 ∨ (pos d (k + 1)).1 = (pos d k).1 + 1 ∨ (pos d (k + 1)).1 = (pos d k).1 - 1 := by
-- proof
  apply StatMech.Onsager.WalkCrossingV.fst_step_bound d hclosed k

/--
[leftRight_card_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCrossingV.lean)
-/
@[path]
private lemma leftRight_card_eq_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {m : ℤ} :
-- imply
  (Finset.univ.filter (fun k : Fin n => (pos d k).1 ≤ m ∧ m + 1 ≤ (pos d (k + 1)).1)).card = (Finset.univ.filter (fun k : Fin n => m + 1 ≤ (pos d k).1 ∧ (pos d (k + 1)).1 ≤ m)).card := by
-- proof
  apply StatMech.Onsager.WalkCrossingV.leftRight_card_eq d m

/--
[vertColCross_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WalkCrossingV.lean)
-/
@[path]
private lemma vertColCross_even_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {m : ℤ}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0) :
-- imply
  Even (vertColCross d m) := by
-- proof
  apply StatMech.Onsager.WalkCrossingV.vertColCross_even d hclosed m


-- created on 2026-10-23
