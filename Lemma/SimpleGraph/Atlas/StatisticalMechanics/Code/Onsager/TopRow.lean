import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.TopRow.Part2
open StatMech StatMech.Onsager StatMech.Onsager.TopRow


/--
[top_out_ne_N](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TopRow.lean)
-/
@[path]
private lemma top_out_ne_N_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {M v : Fin n}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hmax : ∀ j : Fin n, (pos d j).2 ≤ (pos d M).2)
  (hv : (pos d v).2 = (pos d M).2) :
-- imply
  d v ≠ 1 := by
-- proof
  apply StatMech.Onsager.TopRow.top_out_ne_N d hclosed hmax hv

/--
[top_in_ne_S](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TopRow.lean)
-/
@[path]
private lemma top_in_ne_S_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {M v : Fin n}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hmax : ∀ j : Fin n, (pos d j).2 ≤ (pos d M).2)
  (hv : (pos d v).2 = (pos d M).2) :
-- imply
  d (v - 1) ≠ 3 := by
-- proof
  apply StatMech.Onsager.TopRow.top_in_ne_S d hclosed hmax hv

/--
[forward_west_run](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TopRow.lean)
-/
@[path]
private lemma forward_west_run_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {M : Fin n}
  {j : ℕ}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hj : ∀ i : ℕ, i < j → d (M + (Nat.cast i : Fin n)) = 2) :
-- imply
  pos d (M + (Nat.cast j : Fin n)) = ((pos d M).1 - (j : ℤ), (pos d M).2) := by
-- proof
  apply StatMech.Onsager.TopRow.forward_west_run d hclosed M j hj

/--
[topRowContiguous_of_singleTopRun](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TopRow.lean)
-/
@[path]
private lemma topRowContiguous_of_singleTopRun_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {M : Fin n}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hmax : ∀ j : Fin n, (pos d j).2 ≤ (pos d M).2)
  (hrun : SingleTopRun d M) :
-- imply
  StatMech.Onsager.UmlaufsatzStrip.TopRowContiguous d := by
-- proof
  apply StatMech.Onsager.TopRow.topRowContiguous_of_singleTopRun d hclosed hmax hrun

/--
[topRowContiguous_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TopRow.lean)
-/
@[path]
private lemma topRowContiguous_of_residue_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1)
  (hres : ∀ M : Fin n, d (M - 1) = 1 → d M = 2 → (∀ j : Fin n, (pos d j).2 ≤ (pos d M).2) → SingleTopRun d M) :
-- imply
  StatMech.Onsager.UmlaufsatzStrip.TopRowContiguous d := by
-- proof
  apply StatMech.Onsager.TopRow.topRowContiguous_of_residue d hclosed hreflexfree hres


-- created on 2026-10-23
