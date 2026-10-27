import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.btrtrifnotion.Part3
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[btr_removed_isolated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/btrtrifnotion.lean)
-/
@[path]
private lemma btr_removed_isolated_eq
  {d : ℕ}
  {T : Finset (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a b : Site d}
-- given
  (ha : a ∈ T)
  (hconn : Connected d (removeSites T ω) a b) :
-- imply
  b = a := by
-- proof
  apply StatMech.Walls.btr_removed_isolated ha hconn

/--
[btr_arm_outside_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/btrtrifnotion.lean)
-/
@[path]
private lemma btr_arm_outside_box_eq
  {d : ℕ}
  {T : Finset (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a : Site d}
-- given
  (hinf : (cluster d (removeSites T ω) a).Infinite) :
-- imply
  a ∉ T := by
-- proof
  apply StatMech.Walls.btr_arm_outside_box hinf

/--
[btr_genuine_imp_bc61](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/btrtrifnotion.lean)
-/
@[path]
private lemma btr_genuine_imp_bc61_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y : Site d}
-- given
  (h : btr_IsGenuineCoarseTrif ω L y) :
-- imply
  bc61_IsCoarseTrifurcation ω L y := by
-- proof
  apply StatMech.Walls.btr_genuine_imp_bc61 h

/--
[btr_pt_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/btrtrifnotion.lean)
-/
@[path]
private lemma btr_pt_outside_eq
  {d : ℕ}
  {L : ℕ}
  {m h₀ c H : ℤ}
-- given
  (hc : L < (c - m).natAbs) :
-- imply
  bc57_pt c H ∉ bc61_boxAround 2 L (bc57_pt m h₀) := by
-- proof
  apply StatMech.Walls.btr_pt_outside hc

/--
[btr_right_reach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/btrtrifnotion.lean)
-/
@[path]
private lemma btr_right_reach_eq
  {d : ℕ}
  {L : ℕ}
  {m h₀ h c : ℤ}
  {j : ℕ}
-- given
  (hh : 1 ≤ h)
  (hc : (L : ℤ) < c - m) :
-- imply
  Connected 2 (removeSites (bc61_boxAround 2 L (bc57_pt m h₀)) bc60_upperLines) (bc57_pt c h) (bc57_pt (c + (j : ℤ)) h) := by
-- proof
  apply StatMech.Walls.btr_right_reach hh hc j

/--
[btr_left_reach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/btrtrifnotion.lean)
-/
@[path]
private lemma btr_left_reach_eq
  {d : ℕ}
  {L : ℕ}
  {m h₀ h c : ℤ}
  {j : ℕ}
-- given
  (hh : 1 ≤ h)
  (hc : c - m < -(L : ℤ)) :
-- imply
  Connected 2 (removeSites (bc61_boxAround 2 L (bc57_pt m h₀)) bc60_upperLines) (bc57_pt c h) (bc57_pt (c - (j : ℤ)) h) := by
-- proof
  apply StatMech.Walls.btr_left_reach hh hc j

/--
[btr_sameSide_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/btrtrifnotion.lean)
-/
@[path]
private lemma btr_sameSide_right_eq
  {d : ℕ}
  {L : ℕ}
  {m h₀ h c c' : ℤ}
-- given
  (hh : 1 ≤ h)
  (hc : (L : ℤ) < c - m)
  (hc' : (L : ℤ) < c' - m) :
-- imply
  Connected 2 (removeSites (bc61_boxAround 2 L (bc57_pt m h₀)) bc60_upperLines) (bc57_pt c h) (bc57_pt c' h) := by
-- proof
  apply StatMech.Walls.btr_sameSide_right hh hc hc'

/--
[btr_sameSide_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/btrtrifnotion.lean)
-/
@[path]
private lemma btr_sameSide_left_eq
  {d : ℕ}
  {L : ℕ}
  {m h₀ h c c' : ℤ}
-- given
  (hh : 1 ≤ h)
  (hc : c - m < -(L : ℤ))
  (hc' : c' - m < -(L : ℤ)) :
-- imply
  Connected 2 (removeSites (bc61_boxAround 2 L (bc57_pt m h₀)) bc60_upperLines) (bc57_pt c h) (bc57_pt c' h) := by
-- proof
  apply StatMech.Walls.btr_sameSide_left hh hc hc'

/--
[btr_site_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/btrtrifnotion.lean)
-/
@[path]
private lemma btr_site_eq_eq
  {d : ℕ}
  {x : Site 2} :
-- imply
  x = bc57_pt (x 0) (x 1) := by
-- proof
  apply StatMech.Walls.btr_site_eq x

/--
[btr_center_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/btrtrifnotion.lean)
-/
@[path]
private lemma btr_center_mem_box_eq
  {d : ℕ}
  {L : ℕ}
  {y : Site 2} :
-- imply
  y ∈ bc61_boxAround 2 L y := by
-- proof
  apply StatMech.Walls.btr_center_mem_box y

/--
[btr_height_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/btrtrifnotion.lean)
-/
@[path]
private lemma btr_height_pos_eq
  {d : ℕ}
  {u v : Site 2}
-- given
  (hne : v ≠ u)
  (hconn : Connected 2 bc60_upperLines u v) :
-- imply
  1 ≤ u 1 := by
-- proof
  apply StatMech.Walls.btr_height_pos hne hconn

/--
[btr_outside_col](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/btrtrifnotion.lean)
-/
@[path]
private lemma btr_outside_col_eq
  {d : ℕ}
  {L : ℕ}
  {m h₀ c : ℤ}
-- given
  (hout : bc57_pt c h₀ ∉ bc61_boxAround 2 L (bc57_pt m h₀)) :
-- imply
  L < (c - m).natAbs := by
-- proof
  apply StatMech.Walls.btr_outside_col hout

/--
[btr_bc60_not_genuineTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/btrtrifnotion.lean)
-/
@[path]
private lemma btr_bc60_not_genuineTrif_eq
  {d : ℕ}
  {L : ℕ}
  {y : Site 2} :
-- imply
  ¬ btr_IsGenuineCoarseTrif bc60_upperLines L y := by
-- proof
  apply StatMech.Walls.btr_bc60_not_genuineTrif L y

/--
[btr_bc60_genuineTrifFinset_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/btrtrifnotion.lean)
-/
@[path]
private lemma btr_bc60_genuineTrifFinset_empty_eq
  {d : ℕ}
  {L R : ℕ} :
-- imply
  btr_genuineTrifFinset bc60_upperLines L R = ∅ := by
-- proof
  apply StatMech.Walls.btr_bc60_genuineTrifFinset_empty L R

/--
[btr_bc60_genuineTcount_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/btrtrifnotion.lean)
-/
@[path]
private lemma btr_bc60_genuineTcount_zero_eq
  {d : ℕ}
  {L R : ℕ} :
-- imply
  (btr_genuineTrifFinset bc60_upperLines L R).card = 0 := by
-- proof
  apply StatMech.Walls.btr_bc60_genuineTcount_zero L R

/--
[btr_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/btrtrifnotion.lean)
-/
@[path]
private lemma btr_status_eq
  {d : ℕ} :
-- imply
  (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (y : Site 2), btr_IsGenuineCoarseTrif ω L y → bc61_IsCoarseTrifurcation ω L y) ∧ (∀ (L : ℕ) (y : Site 2), ¬ btr_IsGenuineCoarseTrif bc60_upperLines L y) ∧ (∀ (L R : ℕ), (btr_genuineTrifFinset bc60_upperLines L R).card = 0) := by
-- proof
  apply StatMech.Walls.btr_status


-- created on 2026-10-23
