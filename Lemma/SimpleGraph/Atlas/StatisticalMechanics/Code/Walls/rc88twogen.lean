import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc88twogen.Part2
open Finset StatMech StatMech.Walls


/--
[rc88_occ_pair_self_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc88twogen.lean)
-/
@[path]
private lemma rc88_occ_pair_self_mem_eq
  [Fintype ι]
  [DecidableEq ι]
  {a b : ConfigSpace ι}
  {K : Finset ι}
  {w : ConfigSpace ι}
-- given
  (h : rc80_occ ({a, b} : Finset (ConfigSpace ι)) K w = true) :
-- imply
  w = a ∨ w = b := by
-- proof
  apply StatMech.Walls.rc88_occ_pair_self_mem a b K w h

/--
[rc88_occ_mem_of_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc88twogen.lean)
-/
@[path]
private lemma rc88_occ_mem_of_agree_eq
  [Fintype ι]
  [DecidableEq ι]
  {B : Finset (ConfigSpace ι)}
  {L : Finset ι}
  {w x : ConfigSpace ι}
-- given
  (h : rc80_occ B L w = true)
  (hx : ∀ e ∈ L, x e = w e) :
-- imply
  x ∈ B := by
-- proof
  apply StatMech.Walls.rc88_occ_mem_of_agree B L w x h hx

/--
[rc88_disjOccG_pair_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc88twogen.lean)
-/
@[path]
private lemma rc88_disjOccG_pair_subset_eq
  [Fintype ι]
  [DecidableEq ι]
  {a b : ConfigSpace ι}
  {B : Finset (ConfigSpace ι)} :
-- imply
  rc80_disjOccG ({a, b} : Finset (ConfigSpace ι)) B ⊆ ({a, b} : Finset (ConfigSpace ι)) := by
-- proof
  apply StatMech.Walls.rc88_disjOccG_pair_subset a b B

/--
[rc88_other_differs_on_L](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc88twogen.lean)
-/
@[path]
private lemma rc88_other_differs_on_L_eq
  [Fintype ι]
  [DecidableEq ι]
  {a b : ConfigSpace ι}
  {K L : Finset ι}
  {w : ConfigSpace ι}
-- given
  (hdisj : Disjoint K L)
  (hK : rc80_occ ({a, b} : Finset (ConfigSpace ι)) K w = true)
  (hwa : w = a) :
-- imply
  ∀ e ∈ L, b e ≠ w e := by
-- proof
  apply StatMech.Walls.rc88_other_differs_on_L a b K L w hdisj hK hwa

/--
[rc88_disjOccG_pair_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc88twogen.lean)
-/
@[path]
private lemma rc88_disjOccG_pair_comm_eq
  [Fintype ι]
  [DecidableEq ι]
  {a b : ConfigSpace ι}
  {B : Finset (ConfigSpace ι)} :
-- imply
  rc80_disjOccG ({a, b} : Finset (ConfigSpace ι)) B = rc80_disjOccG ({b, a} : Finset (ConfigSpace ι)) B := by
-- proof
  apply StatMech.Walls.rc88_disjOccG_pair_comm a b B

/--
[rc88_core_other](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc88twogen.lean)
-/
@[path]
private lemma rc88_core_other_eq
  [Fintype ι]
  [DecidableEq ι]
  {a b : ConfigSpace ι}
  {B : Finset (ConfigSpace ι)}
-- given
  (ha : a ∈ rc80_disjOccG ({a, b} : Finset (ConfigSpace ι)) B) :
-- imply
  rc80_compl b ∈ B := by
-- proof
  apply StatMech.Walls.rc88_core_other a b B ha

/--
[rc88_core](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc88twogen.lean)
-/
@[path]
private lemma rc88_core_eq
  [Fintype ι]
  [DecidableEq ι]
  {a b : ConfigSpace ι}
  {B : Finset (ConfigSpace ι)}
  {w : ConfigSpace ι}
-- given
  (hw : w ∈ rc80_disjOccG ({a, b} : Finset (ConfigSpace ι)) B) :
-- imply
  rc80_compl a ∈ B ∨ rc80_compl b ∈ B := by
-- proof
  apply StatMech.Walls.rc88_core a b B w hw

/--
[rc88_mem_reflInterG_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc88twogen.lean)
-/
@[path]
private lemma rc88_mem_reflInterG_pair_eq
  [Fintype ι]
  [DecidableEq ι]
  {a b : ConfigSpace ι}
  {B : Finset (ConfigSpace ι)}
  {x : ConfigSpace ι} :
-- imply
  x ∈ rc80_reflInterG ({a, b} : Finset (ConfigSpace ι)) B ↔ (x = a ∨ x = b) ∧ rc80_compl x ∈ B := by
-- proof
  apply StatMech.Walls.rc88_mem_reflInterG_pair a b B x

/--
[rc88_reflInterG_pair_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc88twogen.lean)
-/
@[path]
private lemma rc88_reflInterG_pair_nonempty_eq
  [Fintype ι]
  [DecidableEq ι]
  {a b : ConfigSpace ι}
  {B : Finset (ConfigSpace ι)}
  {w : ConfigSpace ι}
-- given
  (hw : w ∈ rc80_disjOccG ({a, b} : Finset (ConfigSpace ι)) B) :
-- imply
  (rc80_reflInterG ({a, b} : Finset (ConfigSpace ι)) B).Nonempty := by
-- proof
  apply StatMech.Walls.rc88_reflInterG_pair_nonempty a b B w hw

/--
[rc88_reflInterG_pair_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc88twogen.lean)
-/
@[path]
private lemma rc88_reflInterG_pair_full_eq
  [Fintype ι]
  [DecidableEq ι]
  {a b : ConfigSpace ι}
  {B : Finset (ConfigSpace ι)}
-- given
  (ha : a ∈ rc80_disjOccG ({a, b} : Finset (ConfigSpace ι)) B)
  (hb : b ∈ rc80_disjOccG ({a, b} : Finset (ConfigSpace ι)) B) :
-- imply
  rc80_reflInterG ({a, b} : Finset (ConfigSpace ι)) B = ({a, b} : Finset (ConfigSpace ι)) := by
-- proof
  apply StatMech.Walls.rc88_reflInterG_pair_full a b B ha hb

/--
[rc88_wall_twogen_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc88twogen.lean)
-/
@[path]
private lemma rc88_wall_twogen_left_eq
  [Fintype ι]
  [DecidableEq ι]
  {a b : ConfigSpace ι}
  {B : Finset (ConfigSpace ι)} :
-- imply
  (rc80_disjOccG ({a, b} : Finset (ConfigSpace ι)) B).card ≤ (rc80_reflInterG ({a, b} : Finset (ConfigSpace ι)) B).card := by
-- proof
  apply StatMech.Walls.rc88_wall_twogen_left a b B

/--
[rc88_disjOccG_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc88twogen.lean)
-/
@[path]
private lemma rc88_disjOccG_comm_eq
  [Fintype ι]
  [DecidableEq ι]
  {A B : Finset (ConfigSpace ι)} :
-- imply
  rc80_disjOccG A B = rc80_disjOccG B A := by
-- proof
  apply StatMech.Walls.rc88_disjOccG_comm A B

/--
[rc88_reflInterG_comm_image](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc88twogen.lean)
-/
@[path]
private lemma rc88_reflInterG_comm_image_eq
  [Fintype ι]
  [DecidableEq ι]
  {A B : Finset (ConfigSpace ι)} :
-- imply
  rc80_reflInterG A B = (rc80_reflInterG B A).image rc80_compl := by
-- proof
  apply StatMech.Walls.rc88_reflInterG_comm_image A B

/--
[rc88_reflInterG_card_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc88twogen.lean)
-/
@[path]
private lemma rc88_reflInterG_card_comm_eq
  [Fintype ι]
  [DecidableEq ι]
  {A B : Finset (ConfigSpace ι)} :
-- imply
  (rc80_reflInterG A B).card = (rc80_reflInterG B A).card := by
-- proof
  apply StatMech.Walls.rc88_reflInterG_card_comm A B

/--
[rc88_wall_twogen_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc88twogen.lean)
-/
@[path]
private lemma rc88_wall_twogen_right_eq
  [Fintype ι]
  [DecidableEq ι]
  {A : Finset (ConfigSpace ι)}
  {a b : ConfigSpace ι} :
-- imply
  (rc80_disjOccG A ({a, b} : Finset (ConfigSpace ι))).card ≤ (rc80_reflInterG A ({a, b} : Finset (ConfigSpace ι))).card := by
-- proof
  apply StatMech.Walls.rc88_wall_twogen_right A a b

/--
[rc88_a3_ne_b3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc88twogen.lean)
-/
@[path]
private lemma rc88_a3_ne_b3_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  rc88_a3 ≠ rc88_b3 := by
-- proof
  apply StatMech.Walls.rc88_a3_ne_b3

/--
[rc88_A3_not_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc88twogen.lean)
-/
@[path]
private lemma rc88_A3_not_upper_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  ¬ rc80_IsUpper rc88_A3 := by
-- proof
  apply StatMech.Walls.rc88_A3_not_upper

/--
[rc88_A3_not_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc88twogen.lean)
-/
@[path]
private lemma rc88_A3_not_lower_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  ¬ rc80_IsLower rc88_A3 := by
-- proof
  apply StatMech.Walls.rc88_A3_not_lower

/--
[rc88_nonmono_witness_fin3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc88twogen.lean)
-/
@[path]
private lemma rc88_nonmono_witness_fin3_eq
  [Fintype ι]
  [DecidableEq ι]
  {B : Finset (ConfigSpace (Fin 3))} :
-- imply
  (rc80_disjOccG rc88_A3 B).card ≤ (rc80_reflInterG rc88_A3 B).card := by
-- proof
  apply StatMech.Walls.rc88_nonmono_witness_fin3 B

/--
[rc88_A3_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc88twogen.lean)
-/
@[path]
private lemma rc88_A3_card_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  rc88_A3.card = 2 := by
-- proof
  apply StatMech.Walls.rc88_A3_card

/--
[rc88_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc88twogen.lean)
-/
@[path]
private lemma rc88_status_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (a b : ConfigSpace ι) (B : Finset (ConfigSpace ι)), rc80_disjOccG ({a, b} : Finset (ConfigSpace ι)) B ⊆ ({a, b} : Finset (ConfigSpace ι))) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (a b : ConfigSpace ι) (B : Finset (ConfigSpace ι)), a ∈ rc80_disjOccG ({a, b} : Finset (ConfigSpace ι)) B → rc80_compl b ∈ B) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (a b : ConfigSpace ι) (B : Finset (ConfigSpace ι)), (rc80_disjOccG ({a, b} : Finset (ConfigSpace ι)) B).card ≤ (rc80_reflInterG ({a, b} : Finset (ConfigSpace ι)) B).card) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset (ConfigSpace ι)) (a b : ConfigSpace ι), (rc80_disjOccG A ({a, b} : Finset (ConfigSpace ι))).card ≤ (rc80_reflInterG A ({a, b} : Finset (ConfigSpace ι))).card) ∧ (¬ rc80_IsUpper rc88_A3 ∧ ¬ rc80_IsLower rc88_A3 ∧ rc88_A3.card = 2 ∧ (rc80_disjOccG rc88_A3 Finset.univ).card ≤ (rc80_reflInterG rc88_A3 Finset.univ).card) ∧ (rc60_BoxUnionBound → ReimerWprobCore) := by
-- proof
  apply StatMech.Walls.rc88_status


-- created on 2026-10-23
