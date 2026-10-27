import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.NoDoubleWind2.Part2
open StatMech StatMech.Onsager StatMech.Onsager.NoDoubleWind2


/--
[xco_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/NoDoubleWind2.lean)
-/
@[path]
private lemma xco_succ_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {k : Fin n}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0) :
-- imply
  (pos d (k + 1)).1 = (pos d k).1 + (stepOf (d k)).1 := by
-- proof
  apply StatMech.Onsager.NoDoubleWind2.xco_succ d hclosed k

/--
[yco_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/NoDoubleWind2.lean)
-/
@[path]
private lemma yco_succ_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {k : Fin n}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0) :
-- imply
  (pos d (k + 1)).2 = (pos d k).2 + (stepOf (d k)).2 := by
-- proof
  apply StatMech.Onsager.NoDoubleWind2.yco_succ d hclosed k

/--
[xstep_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/NoDoubleWind2.lean)
-/
@[path]
private lemma xstep_cases_eq
  {n : ℕ}
  [NeZero n]
  {w : Fin 4} :
-- imply
  (w = 0 ∧ (stepOf w).1 = 1) ∨ (w = 2 ∧ (stepOf w).1 = -1) ∨ ((w = 1 ∨ w = 3) ∧ (stepOf w).1 = 0) := by
-- proof
  apply StatMech.Onsager.NoDoubleWind2.xstep_cases w

/--
[ystep_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/NoDoubleWind2.lean)
-/
@[path]
private lemma ystep_cases_eq
  {n : ℕ}
  [NeZero n]
  {w : Fin 4} :
-- imply
  (w = 1 ∧ (stepOf w).2 = 1) ∨ (w = 3 ∧ (stepOf w).2 = -1) ∨ ((w = 0 ∨ w = 2) ∧ (stepOf w).2 = 0) := by
-- proof
  apply StatMech.Onsager.NoDoubleWind2.ystep_cases w

/--
[maxx_no_E_out](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/NoDoubleWind2.lean)
-/
@[path]
private lemma maxx_no_E_out_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {k : Fin n}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hmax : ∀ j : Fin n, (pos d j).1 ≤ (pos d k).1) :
-- imply
  d k ≠ 0 := by
-- proof
  apply StatMech.Onsager.NoDoubleWind2.maxx_no_E_out d hclosed k hmax

/--
[maxx_no_W_in](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/NoDoubleWind2.lean)
-/
@[path]
private lemma maxx_no_W_in_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {k : Fin n}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hmax : ∀ j : Fin n, (pos d j).1 ≤ (pos d k).1) :
-- imply
  d (k - 1) ≠ 2 := by
-- proof
  apply StatMech.Onsager.NoDoubleWind2.maxx_no_W_in d hclosed k hmax

/--
[miny_no_S_out](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/NoDoubleWind2.lean)
-/
@[path]
private lemma miny_no_S_out_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {k : Fin n}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hmin : ∀ j : Fin n, (pos d k).2 ≤ (pos d j).2) :
-- imply
  d k ≠ 3 := by
-- proof
  apply StatMech.Onsager.NoDoubleWind2.miny_no_S_out d hclosed k hmin

/--
[miny_no_N_in](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/NoDoubleWind2.lean)
-/
@[path]
private lemma miny_no_N_in_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {k : Fin n}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hmin : ∀ j : Fin n, (pos d k).2 ≤ (pos d j).2) :
-- imply
  d (k - 1) ≠ 1 := by
-- proof
  apply StatMech.Onsager.NoDoubleWind2.miny_no_N_in d hclosed k hmin

/--
[succ_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/NoDoubleWind2.lean)
-/
@[path]
private lemma succ_ne_eq
  {n : ℕ}
  [NeZero n]
  {c : Fin 4} :
-- imply
  c + 1 ≠ c := by
-- proof
  apply StatMech.Onsager.NoDoubleWind2.succ_ne c

/--
[card_filter_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/NoDoubleWind2.lean)
-/
@[path]
private lemma card_filter_shift_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  [DecidablePred P]
-- given
  (P : Fin 4 → Prop) :
-- imply
  (Finset.univ.filter (fun i : Fin n => P (d (i + 1)))).card = (Finset.univ.filter (fun i : Fin n => P (d i))).card := by
-- proof
  apply StatMech.Onsager.NoDoubleWind2.card_filter_shift d P

/--
[dcount_out](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/NoDoubleWind2.lean)
-/
@[path]
private lemma dcount_out_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {c : Fin 4}
-- given
  (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
-- imply
  (Finset.univ.filter (fun i : Fin n => d i = c)).card = tcount d c + scount d c := by
-- proof
  apply StatMech.Onsager.NoDoubleWind2.dcount_out d hreflexfree c

/--
[dcount_in](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/NoDoubleWind2.lean)
-/
@[path]
private lemma dcount_in_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {c : Fin 4}
-- given
  (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
-- imply
  (Finset.univ.filter (fun i : Fin n => d (i + 1) = c + 1)).card = tcount d c + scount d (c + 1) := by
-- proof
  apply StatMech.Onsager.NoDoubleWind2.dcount_in d hreflexfree c

/--
[tcount_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/NoDoubleWind2.lean)
-/
@[path]
private lemma tcount_shift_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
  {c : Fin 4}
-- given
  (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
-- imply
  tcount d c = tcount d (c + 1) := by
-- proof
  apply StatMech.Onsager.NoDoubleWind2.tcount_shift d hreflexfree c

/--
[cc_eq_sum_tcount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/NoDoubleWind2.lean)
-/
@[path]
private lemma cc_eq_sum_tcount_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4} :
-- imply
  cc d = ∑ c : Fin 4, tcount d c := by
-- proof
  apply StatMech.Onsager.NoDoubleWind2.cc_eq_sum_tcount d

/--
[cc_eq_four_mul_tcount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/NoDoubleWind2.lean)
-/
@[path]
private lemma cc_eq_four_mul_tcount_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
-- given
  (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1) :
-- imply
  cc d = 4 * tcount d 1 := by
-- proof
  apply StatMech.Onsager.NoDoubleWind2.cc_eq_four_mul_tcount d hreflexfree

/--
[two_le_tcount_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/NoDoubleWind2.lean)
-/
@[path]
private lemma two_le_tcount_one_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
-- given
  (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1)
  (h8 : 8 ≤ cc d) :
-- imply
  2 ≤ tcount d 1 := by
-- proof
  apply StatMech.Onsager.NoDoubleWind2.two_le_tcount_one d hreflexfree h8

/--
[exists_two_top_corners](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/NoDoubleWind2.lean)
-/
@[path]
private lemma exists_two_top_corners_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
-- given
  (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1)
  (h8 : 8 ≤ cc d) :
-- imply
  ∃ i j : Fin n, i ≠ j ∧ d i = 1 ∧ d (i + 1) = 2 ∧ d j = 1 ∧ d (j + 1) = 2 := by
-- proof
  apply StatMech.Onsager.NoDoubleWind2.exists_two_top_corners d hreflexfree h8

/--
[cc_lt_eight_of_uniqueTopCorner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/NoDoubleWind2.lean)
-/
@[path]
private lemma cc_lt_eight_of_uniqueTopCorner_eq
  {n : ℕ}
  [NeZero n]
  {d : Fin n → Fin 4}
-- given
  (hreflexfree : ∀ i : Fin n, d (i + 1) - d i = 0 ∨ d (i + 1) - d i = 1)
  (huniq : ∀ i j : Fin n, d i = 1 → d (i + 1) = 2 → d j = 1 → d (j + 1) = 2 → i = j) :
-- imply
  cc d < 8 := by
-- proof
  apply StatMech.Onsager.NoDoubleWind2.cc_lt_eight_of_uniqueTopCorner d hreflexfree huniq


-- created on 2026-10-23
