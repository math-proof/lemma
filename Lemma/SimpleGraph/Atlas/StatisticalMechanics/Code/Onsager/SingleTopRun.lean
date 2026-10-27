import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.SingleTopRun
open StatMech StatMech.Onsager StatMech.Onsager.SingleTopRunProof


/--
[top_arrival_west](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SingleTopRun.lean)
-/
@[path]
private lemma top_arrival_west_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {M v : Fin n}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1)
  (hmax : ∀ j : Fin n, (pos d j).2 ≤ (pos d M).2)
  (hv : (pos d v).2 = (pos d M).2)
  (harr : d (v - 1) = 1) :
-- imply
  d v = 2 := by
-- proof
  apply StatMech.Onsager.SingleTopRunProof.top_arrival_west d hclosed hreflexfree hmax hv harr

/--
[top_west_next](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SingleTopRun.lean)
-/
@[path]
private lemma top_west_next_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {M v : Fin n}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1)
  (hmax : ∀ j : Fin n, (pos d j).2 ≤ (pos d M).2)
  (hv : (pos d v).2 = (pos d M).2)
  (hw : d v = 2) :
-- imply
  (pos d (v + 1)).2 = (pos d M).2 ∧ (d (v + 1) = 2 ∨ d (v + 1) = 3) := by
-- proof
  apply StatMech.Onsager.SingleTopRunProof.top_west_next d hclosed hreflexfree hmax hv hw

/--
[exists_step_ne_west](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SingleTopRun.lean)
-/
@[path]
private lemma exists_step_ne_west_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {M : Fin n}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0) :
-- imply
  ∃ i : ℕ, d (M + (Nat.cast i : Fin n)) ≠ 2 := by
-- proof
  apply StatMech.Onsager.SingleTopRunProof.exists_step_ne_west d hclosed M

/--
[exists_west_run_end](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SingleTopRun.lean)
-/
@[path]
private lemma exists_west_run_end_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {M : Fin n}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1)
  (hmax : ∀ j : Fin n, (pos d j).2 ≤ (pos d M).2)
  (hout : d M = 2) :
-- imply
  ∃ J : ℕ, 1 ≤ J ∧ (∀ i : ℕ, i < J → d (M + (Nat.cast i : Fin n)) = 2) ∧ d (M + (Nat.cast J : Fin n)) = 3 := by
-- proof
  apply StatMech.Onsager.SingleTopRunProof.exists_west_run_end d hclosed hreflexfree M hmax hout

/--
[singleTopRun_of_runCoversTop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SingleTopRun.lean)
-/
@[path]
private lemma singleTopRun_of_runCoversTop_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {M : Fin n}
  {J : ℕ}
-- given
  (hrun : ∀ i : ℕ, i < J → d (M + (Nat.cast i : Fin n)) = 2)
  (hcover : ∀ v : Fin n, (pos d v).2 = (pos d M).2 → ∃ i : ℕ, i ≤ J ∧ (pos d v).1 = (pos d M).1 - (i : ℤ)) :
-- imply
  StatMech.Onsager.TopRow.SingleTopRun d M := by
-- proof
  apply StatMech.Onsager.SingleTopRunProof.singleTopRun_of_runCoversTop d M J hrun hcover


-- created on 2026-10-23
