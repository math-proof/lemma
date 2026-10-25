import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bcorcorridors.Part5
open Set SimpleGraph StatMech StatMech.Lattice StatMech.Walls


/--
[bcor_origin_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcorcorridors.lean)
-/
@[path]
private lemma bcor_origin_eq_eq :
-- imply
  (![0, 0] : Site 2) = 0 := by
-- proof
  apply StatMech.Walls.bcor_origin_eq

/--
[bcor_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcorcorridors.lean)
-/
@[path]
private lemma bcor_mem_box_eq
  {a b : ℤ}
  {n : ℕ}
-- given
  (ha : a.natAbs ≤ n)
  (hb : b.natAbs ≤ n) :
-- imply
  (![a, b] : Site 2) ∈ box 2 n := by
-- proof
  apply StatMech.Walls.bcor_mem_box ha hb

/--
[bcor_uIcc_natAbs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcorcorridors.lean)
-/
@[path]
private lemma bcor_uIcc_natAbs_eq
  {s t : ℤ}
  {n : ℕ}
-- given
  (hs : s.natAbs ≤ n)
  (ht : t ∈ Set.uIcc 0 s) :
-- imply
  t.natAbs ≤ n := by
-- proof
  apply StatMech.Walls.bcor_uIcc_natAbs hs ht

/--
[bcor_rot90_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcorcorridors.lean)
-/
@[path]
private lemma bcor_rot90_mem_box_eq
  {n : ℕ}
  {x : Site 2}
-- given
  (hx : x ∈ box 2 n) :
-- imply
  rot90Fun x ∈ box 2 n := by
-- proof
  apply StatMech.Walls.bcor_rot90_mem_box hx

/--
[bcor_corridors_rot90](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcorcorridors.lean)
-/
@[path]
private lemma bcor_corridors_rot90_eq
  {n : ℕ}
  {u₁ u₂ u₃ : Site 2}
-- given
  (hC : bcor_Corridors n u₁ u₂ u₃) :
-- imply
  bcor_Corridors n (rot90Fun u₁) (rot90Fun u₂) (rot90Fun u₃) := by
-- proof
  apply StatMech.Walls.bcor_corridors_rot90 hC

/--
[bcor_corridors_rot90_iterate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcorcorridors.lean)
-/
@[path]
private lemma bcor_corridors_rot90_iterate_eq
  {k : ℕ}
  {n : ℕ}
  {u₁ u₂ u₃ : Site 2}
-- given
  (hC : bcor_Corridors n u₁ u₂ u₃) :
-- imply
  bcor_Corridors n ((rot90Fun^[k]) u₁) ((rot90Fun^[k]) u₂) ((rot90Fun^[k]) u₃) := by
-- proof
  apply StatMech.Walls.bcor_corridors_rot90_iterate k hC

/--
[bcor_corridors_swap12](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcorcorridors.lean)
-/
@[path]
private lemma bcor_corridors_swap12_eq
  {n : ℕ}
  {u₁ u₂ u₃ : Site 2}
-- given
  (hC : bcor_Corridors n u₁ u₂ u₃) :
-- imply
  bcor_Corridors n u₂ u₁ u₃ := by
-- proof
  apply StatMech.Walls.bcor_corridors_swap12 hC

/--
[bcor_corridors_swap23](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcorcorridors.lean)
-/
@[path]
private lemma bcor_corridors_swap23_eq
  {n : ℕ}
  {u₁ u₂ u₃ : Site 2}
-- given
  (hC : bcor_Corridors n u₁ u₂ u₃) :
-- imply
  bcor_Corridors n u₁ u₃ u₂ := by
-- proof
  apply StatMech.Walls.bcor_corridors_swap23 hC

/--
[bcor_reflFun_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcorcorridors.lean)
-/
@[path]
private lemma bcor_reflFun_apply_eq
  {a b : ℤ} :
-- imply
  bcor_reflFun ![a, b] = ![a, -b] := by
-- proof
  apply StatMech.Walls.bcor_reflFun_apply a b

/--
[bcor_refl_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcorcorridors.lean)
-/
@[path]
private lemma bcor_refl_adj_eq
  {x y : Site 2} :
-- imply
  (hypercubicLattice 2).Adj (bcor_reflFun x) (bcor_reflFun y) ↔ (hypercubicLattice 2).Adj x y := by
-- proof
  apply StatMech.Walls.bcor_refl_adj x y

/--
[bcor_refl_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcorcorridors.lean)
-/
@[path]
private lemma bcor_refl_mem_box_eq
  {n : ℕ}
  {x : Site 2}
-- given
  (hx : x ∈ box 2 n) :
-- imply
  bcor_reflFun x ∈ box 2 n := by
-- proof
  apply StatMech.Walls.bcor_refl_mem_box hx

/--
[bcor_corridors_refl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcorcorridors.lean)
-/
@[path]
private lemma bcor_corridors_refl_eq
  {n : ℕ}
  {u₁ u₂ u₃ : Site 2}
-- given
  (hC : bcor_Corridors n u₁ u₂ u₃) :
-- imply
  bcor_Corridors n (bcor_reflFun u₁) (bcor_reflFun u₂) (bcor_reflFun u₃) := by
-- proof
  apply StatMech.Walls.bcor_corridors_refl hC

/--
[bcor_corridors_RTL](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcorcorridors.lean)
-/
@[path]
private lemma bcor_corridors_RTL_eq
  {n : ℕ}
  {s t r : ℤ}
-- given
  (hn : 1 ≤ n)
  (hs : s.natAbs ≤ n)
  (ht : t.natAbs ≤ n)
  (hr : r.natAbs ≤ n)
  (h12 : (![(n : ℤ), s] : Site 2) ≠ ![t, (n : ℤ)])
  (h23 : (![t, (n : ℤ)] : Site 2) ≠ ![(-(n : ℤ)), r]) :
-- imply
  bcor_Corridors n ![(n : ℤ), s] ![t, (n : ℤ)] ![(-(n : ℤ)), r] := by
-- proof
  apply StatMech.Walls.bcor_corridors_RTL n hn s t r hs ht hr h12 h23

/--
[bcor_corridors_two_right_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcorcorridors.lean)
-/
@[path]
private lemma bcor_corridors_two_right_upper_eq
  {n : ℕ}
  {y₁ y₂ x y : ℤ}
-- given
  (hn : 1 ≤ n)
  (hy₁ : y₁.natAbs ≤ n)
  (hy₂ : y₂.natAbs ≤ n)
  (hx : x.natAbs ≤ n)
  (hy : y.natAbs ≤ n)
  (h12 : y₁ < y₂)
  (h2top : y₂ < n)
  (houter : y = n ∨ x = -(n : ℤ)) :
-- imply
  bcor_Corridors n ![(n : ℤ), y₁] ![(n : ℤ), y₂] ![x, y] := by
-- proof
  apply StatMech.Walls.bcor_corridors_two_right_upper n hn y₁ y₂ x y hy₁ hy₂ hx hy h12 h2top houter

/--
[bcor_corridors_two_right_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcorcorridors.lean)
-/
@[path]
private lemma bcor_corridors_two_right_lower_eq
  {n : ℕ}
  {y₁ y₂ x y : ℤ}
-- given
  (hn : 1 ≤ n)
  (hy₁ : y₁.natAbs ≤ n)
  (hy₂ : y₂.natAbs ≤ n)
  (hx : x.natAbs ≤ n)
  (hy : y.natAbs ≤ n)
  (h12 : y₁ < y₂)
  (hbot1 : -(n : ℤ) < y₁)
  (houter : y = -(n : ℤ) ∨ x = -(n : ℤ)) :
-- imply
  bcor_Corridors n ![(n : ℤ), y₁] ![(n : ℤ), y₂] ![x, y] := by
-- proof
  apply StatMech.Walls.bcor_corridors_two_right_lower n hn y₁ y₂ x y hy₁ hy₂ hx hy h12 hbot1 houter

/--
[bcor_corridors_same_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcorcorridors.lean)
-/
@[path]
private lemma bcor_corridors_same_right_eq
  {n : ℕ}
  {y₁ y₂ y₃ : ℤ}
-- given
  (hn : 1 ≤ n)
  (hy₁ : y₁.natAbs ≤ n)
  (hy₂ : y₂.natAbs ≤ n)
  (hy₃ : y₃.natAbs ≤ n)
  (h12 : y₁ < y₂)
  (h23 : y₂ < y₃) :
-- imply
  bcor_Corridors n ![(n : ℤ), y₁] ![(n : ℤ), y₂] ![(n : ℤ), y₃] := by
-- proof
  apply StatMech.Walls.bcor_corridors_same_right n hn y₁ y₂ y₃ hy₁ hy₂ hy₃ h12 h23

/--
[bcor_corridors_same_right_of_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcorcorridors.lean)
-/
@[path]
private lemma bcor_corridors_same_right_of_distinct_eq
  {n : ℕ}
  {y₁ y₂ y₃ : ℤ}
-- given
  (hn : 1 ≤ n)
  (hy₁ : y₁.natAbs ≤ n)
  (hy₂ : y₂.natAbs ≤ n)
  (hy₃ : y₃.natAbs ≤ n)
  (hne12 : y₁ ≠ y₂)
  (hne13 : y₁ ≠ y₃)
  (hne23 : y₂ ≠ y₃) :
-- imply
  bcor_Corridors n ![(n : ℤ), y₁] ![(n : ℤ), y₂] ![(n : ℤ), y₃] := by
-- proof
  apply StatMech.Walls.bcor_corridors_same_right_of_distinct n hn y₁ y₂ y₃ hy₁ hy₂ hy₃ hne12 hne13 hne23

/--
[bcor_firstSteps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcorcorridors.lean)
-/
@[path]
private lemma bcor_firstSteps_eq
  {n : ℕ}
  {u₁ u₂ u₃ : Site 2}
-- given
  (hu₁ : u₁ ≠ ![0, 0])
  (hu₂ : u₂ ≠ ![0, 0])
  (hu₃ : u₃ ≠ ![0, 0])
  (hC : bcor_Corridors n u₁ u₂ u₃) :
-- imply
  ∃ a₁ a₂ a₃ : Site 2, ((hypercubicLattice 2).Adj 0 a₁ ∧ (hypercubicLattice 2).Adj 0 a₂ ∧ (hypercubicLattice 2).Adj 0 a₃) ∧ (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) := by
-- proof
  apply StatMech.Walls.bcor_firstSteps n hu₁ hu₂ hu₃ hC

/--
[bcor_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcorcorridors.lean)
-/
@[path]
private lemma bcor_witness_eq :
-- imply
  bcor_Corridors 3 ![(3 : ℤ), 1] ![(-2 : ℤ), (3 : ℤ)] ![(-3 : ℤ), -2] := by
-- proof
  apply StatMech.Walls.bcor_witness

/--
[bcor_incident_corner_impossible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcorcorridors.lean)
-/
@[path]
private lemma bcor_incident_corner_impossible_eq
  {n : ℕ}
-- given
  (hn : 1 ≤ n) :
-- imply
  ¬ bcor_Corridors n ![(n : ℤ), (n : ℤ) - 1] ![(n : ℤ), (n : ℤ)] ![(n : ℤ) - 1, (n : ℤ)] := by
-- proof
  apply StatMech.Walls.bcor_incident_corner_impossible n hn

/--
[bcor_witness_firstSteps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcorcorridors.lean)
-/
@[path]
private lemma bcor_witness_firstSteps_eq :
-- imply
  ∃ a₁ a₂ a₃ : Site 2, ((hypercubicLattice 2).Adj 0 a₁ ∧ (hypercubicLattice 2).Adj 0 a₂ ∧ (hypercubicLattice 2).Adj 0 a₃) ∧ (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) := by
-- proof
  apply StatMech.Walls.bcor_witness_firstSteps


-- created on 2026-10-23
