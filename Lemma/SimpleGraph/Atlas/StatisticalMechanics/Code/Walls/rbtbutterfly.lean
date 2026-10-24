import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.rbtbutterfly
open Finset StatMech StatMech.Walls StatMech.Walls.Reimer


/--
[rbt_inner2_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rbtbutterfly.lean)
-/
@[path]
private lemma rbt_inner2_eq_eq
  {u v : Bool → ℝ} :
-- imply
  rbt_inner2 u v = u false * v false + u true * v true := by
-- proof
  apply StatMech.Walls.Reimer.rbt_inner2_eq u v

/--
[rbt_inner2_e_f](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rbtbutterfly.lean)
-/
@[path]
private lemma rbt_inner2_e_f_eq
  {c : Bool} :
-- imply
  rbt_inner2 (rbt_e2 c) (rbt_f2 (!c)) = 0 := by
-- proof
  apply StatMech.Walls.Reimer.rbt_inner2_e_f c

/--
[rbt_inner2_e_g](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rbtbutterfly.lean)
-/
@[path]
private lemma rbt_inner2_e_g_eq
  {c : Bool} :
-- imply
  rbt_inner2 (rbt_e2 c) (rbt_g2 (!c) (!c)) = 0 := by
-- proof
  apply StatMech.Walls.Reimer.rbt_inner2_e_g c

/--
[rbt_inner2_f_g](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rbtbutterfly.lean)
-/
@[path]
private lemma rbt_inner2_f_g_eq
  {c : Bool} :
-- imply
  rbt_inner2 (rbt_f2 c) (rbt_g2 (!c) c) = 0 := by
-- proof
  apply StatMech.Walls.Reimer.rbt_inner2_f_g c

/--
[rbt_tens_inner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rbtbutterfly.lean)
-/
@[path]
private lemma rbt_tens_inner_eq
  {m : ℕ}
  {u v : Fin m → Bool → ℝ} :
-- imply
  rbt_inner (rbt_tens u) (rbt_tens v) = ∏ i, rbt_inner2 (u i) (v i) := by
-- proof
  apply StatMech.Walls.Reimer.rbt_tens_inner u v

/--
[rbt_e_perp_f](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rbtbutterfly.lean)
-/
@[path]
private lemma rbt_e_perp_f_eq
  {m : ℕ}
  {x y : rbt_Q m}
-- given
  (hxy : x ≠ y) :
-- imply
  rbt_inner (rbt_e x) (rbt_f y) = 0 := by
-- proof
  apply StatMech.Walls.Reimer.rbt_e_perp_f x y hxy

/--
[rbt_e_perp_g](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rbtbutterfly.lean)
-/
@[path]
private lemma rbt_e_perp_g_eq
  {m : ℕ}
  {x y z : rbt_Q m}
-- given
  (hx : ¬ rbt_inRed y z x) :
-- imply
  rbt_inner (rbt_e x) (rbt_g y z) = 0 := by
-- proof
  apply StatMech.Walls.Reimer.rbt_e_perp_g x y z hx

/--
[rbt_f_perp_g](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rbtbutterfly.lean)
-/
@[path]
private lemma rbt_f_perp_g_eq
  {m : ℕ}
  {x y z : rbt_Q m}
-- given
  (hx : ¬ rbt_inYellow y z x) :
-- imply
  rbt_inner (rbt_f x) (rbt_g y z) = 0 := by
-- proof
  apply StatMech.Walls.Reimer.rbt_f_perp_g x y z hx

/--
[rbt_triangular_indep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rbtbutterfly.lean)
-/
@[path]
private lemma rbt_triangular_indep_eq
  [Fintype ι]
  [PartialOrder ι]
  [DecidableEq ι]
  {M : ι → ι → ℝ}
-- given
  (hoff : ∀ x z, ¬ x ≤ z → M x z = 0)
  (hdiag : ∀ x, M x x ≠ 0) :
-- imply
  LinearIndependent ℝ (fun x : ι => (fun z => M x z : ι → ℝ)) := by
-- proof
  apply StatMech.Walls.Reimer.rbt_triangular_indep M hoff hdiag

/--
[rbt_e2_eq_zeta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rbtbutterfly.lean)
-/
@[path]
private lemma rbt_e2_eq_zeta_eq
  {c c' : Bool} :
-- imply
  rbt_e2 c c' = if c ≤ c' then 1 else 0 := by
-- proof
  apply StatMech.Walls.Reimer.rbt_e2_eq_zeta c c'

/--
[rbt_e_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rbtbutterfly.lean)
-/
@[path]
private lemma rbt_e_apply_eq
  {m : ℕ}
  {x z : rbt_Q m} :
-- imply
  rbt_e x z = if x ≤ z then 1 else 0 := by
-- proof
  apply StatMech.Walls.Reimer.rbt_e_apply x z

/--
[rbt_e_off](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rbtbutterfly.lean)
-/
@[path]
private lemma rbt_e_off_eq
  {m : ℕ}
  {x z : rbt_Q m}
-- given
  (h : ¬ x ≤ z) :
-- imply
  rbt_e x z = 0 := by
-- proof
  apply StatMech.Walls.Reimer.rbt_e_off x z h

/--
[rbt_e_diag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rbtbutterfly.lean)
-/
@[path]
private lemma rbt_e_diag_eq
  {m : ℕ}
  {x : rbt_Q m} :
-- imply
  rbt_e x x ≠ 0 := by
-- proof
  apply StatMech.Walls.Reimer.rbt_e_diag x

/--
[rbt_e_indep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rbtbutterfly.lean)
-/
@[path]
private lemma rbt_e_indep_eq
  {m : ℕ} :
-- imply
  LinearIndependent ℝ (fun x : rbt_Q m => rbt_e x) := by
-- proof
  apply StatMech.Walls.Reimer.rbt_e_indep m

/--
[rbt_f2_off](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rbtbutterfly.lean)
-/
@[path]
private lemma rbt_f2_off_eq
  {c c' : Bool}
-- given
  (h : ¬ c' ≤ c) :
-- imply
  rbt_f2 c c' = 0 := by
-- proof
  apply StatMech.Walls.Reimer.rbt_f2_off c c' h

/--
[rbt_f2_diag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rbtbutterfly.lean)
-/
@[path]
private lemma rbt_f2_diag_eq
  {c : Bool} :
-- imply
  rbt_f2 c c ≠ 0 := by
-- proof
  apply StatMech.Walls.Reimer.rbt_f2_diag c

/--
[rbt_f_off](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rbtbutterfly.lean)
-/
@[path]
private lemma rbt_f_off_eq
  {m : ℕ}
  {x z : rbt_Q m}
-- given
  (h : ¬ z ≤ x) :
-- imply
  rbt_f x z = 0 := by
-- proof
  apply StatMech.Walls.Reimer.rbt_f_off x z h

/--
[rbt_f_diag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rbtbutterfly.lean)
-/
@[path]
private lemma rbt_f_diag_eq
  {m : ℕ}
  {x : rbt_Q m} :
-- imply
  rbt_f x x ≠ 0 := by
-- proof
  apply StatMech.Walls.Reimer.rbt_f_diag x

/--
[rbt_f_indep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rbtbutterfly.lean)
-/
@[path]
private lemma rbt_f_indep_eq
  {m : ℕ} :
-- imply
  LinearIndependent ℝ (fun x : rbt_Q m => rbt_f x) := by
-- proof
  apply StatMech.Walls.Reimer.rbt_f_indep m

/--
[rbt_partition_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rbtbutterfly.lean)
-/
@[path]
private lemma rbt_partition_card_eq
  {m : ℕ}
  {body : rbt_Q m → rbt_Q m}
  {T : Finset (rbt_Q m)} :
-- imply
  2 ^ m = (rbt_Red body T ∩ rbt_Yellow body T).card + (rbt_Ybar body T).card + (rbt_Rbar body T).card := by
-- proof
  apply StatMech.Walls.Reimer.rbt_partition_card body T


-- created on 2026-10-23
