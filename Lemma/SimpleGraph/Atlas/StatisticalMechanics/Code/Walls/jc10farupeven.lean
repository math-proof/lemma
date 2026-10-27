import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.jc10farupeven
open Set SimpleGraph Function StatMech StatMech.Walls


/--
[jc10_rayCount_eq_zero_of_above](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc10farupeven.lean)
-/
@[path]
private lemma jc10_rayCount_eq_zero_of_above_eq
  {z : Site 2}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (h : ∀ p ∈ w.support, p 1 ≤ z 1 - 1) :
-- imply
  jec_rayCount z w = 0 := by
-- proof
  apply StatMech.Walls.jc10_rayCount_eq_zero_of_above z w h

/--
[jc10_even_of_above](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc10farupeven.lean)
-/
@[path]
private lemma jc10_even_of_above_eq
  {z : Site 2}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (h : ∀ p ∈ w.support, p 1 ≤ z 1 - 1) :
-- imply
  Even (jec_rayCount z w) := by
-- proof
  apply StatMech.Walls.jc10_even_of_above z w h

/--
[jc10_support_row_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc10farupeven.lean)
-/
@[path]
private lemma jc10_support_row_bound_eq
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
  {R : ℕ}
  {p : Site 2}
-- given
  (hsupp : ∀ p ∈ w.support, p ∈ box 2 R)
  (hp : p ∈ w.support) :
-- imply
  -(R : ℤ) ≤ p 1 ∧ p 1 ≤ (R : ℤ) := by
-- proof
  apply StatMech.Walls.jc10_support_row_bound w R hsupp hp

/--
[jc10_rayCount_eq_zero_of_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc10farupeven.lean)
-/
@[path]
private lemma jc10_rayCount_eq_zero_of_box_eq
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
  {R : ℕ}
  {z : Site 2}
-- given
  (hsupp : ∀ p ∈ w.support, p ∈ box 2 R)
  (hz : (R : ℤ) < z 1) :
-- imply
  jec_rayCount z w = 0 := by
-- proof
  apply StatMech.Walls.jc10_rayCount_eq_zero_of_box w R hsupp z hz

/--
[jc10_farUp_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc10farupeven.lean)
-/
@[path]
private lemma jc10_farUp_even_eq
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
  {R : ℕ}
  {z : Site 2}
-- given
  (hsupp : ∀ p ∈ w.support, p ∈ box 2 R)
  (hz : (R : ℤ) < z 1) :
-- imply
  Even (jec_rayCount z w) := by
-- proof
  apply StatMech.Walls.jc10_farUp_even w R hsupp z hz

/--
[jc10_orbitLoop_box_confined](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc10farupeven.lean)
-/
@[path]
private lemma jc10_orbitLoop_box_confined_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  ∃ R : ℕ, ∀ p ∈ (mpl_orbitLoop K a).support, p ∈ box 2 R := by
-- proof
  apply StatMech.Walls.jc10_orbitLoop_box_confined K a

/--
[jc10_orbitLoop_rayCount_eq_zero_of_above](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc10farupeven.lean)
-/
@[path]
private lemma jc10_orbitLoop_rayCount_eq_zero_of_above_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {z : Site 2}
-- given
  (hfar : ∀ p ∈ (mpl_orbitLoop K a).support, p 1 ≤ z 1 - 1) :
-- imply
  jec_rayCount z (mpl_orbitLoop K a) = 0 := by
-- proof
  apply StatMech.Walls.jc10_orbitLoop_rayCount_eq_zero_of_above K a z hfar

/--
[jc10_orbitLoop_farUp_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc10farupeven.lean)
-/
@[path]
private lemma jc10_orbitLoop_farUp_even_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {z : Site 2}
-- given
  (hfar : ∀ p ∈ (mpl_orbitLoop K a).support, p 1 ≤ z 1 - 1) :
-- imply
  Even (jec_rayCount z (mpl_orbitLoop K a)) := by
-- proof
  apply StatMech.Walls.jc10_orbitLoop_farUp_even K a z hfar

/--
[jc10_orbitLoop_farUp_even_of_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc10farupeven.lean)
-/
@[path]
private lemma jc10_orbitLoop_farUp_even_of_box_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {R : ℕ}
  {z : Site 2}
-- given
  (hsupp : ∀ p ∈ (mpl_orbitLoop K a).support, p ∈ box 2 R)
  (hz : (R : ℤ) < z 1) :
-- imply
  Even (jec_rayCount z (mpl_orbitLoop K a)) := by
-- proof
  apply StatMech.Walls.jc10_orbitLoop_farUp_even_of_box K a R hsupp z hz

/--
[jc10_unitCell_farUp_rayCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc10farupeven.lean)
-/
@[path]
private lemma jc10_unitCell_farUp_rayCount_eq :
-- imply
  jec_rayCount (![0, 5] : Site 2) (mpl_orbitLoop unitCell ucBase) = 0 := by
-- proof
  apply StatMech.Walls.jc10_unitCell_farUp_rayCount

/--
[jc10_unitCell_farUp_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc10farupeven.lean)
-/
@[path]
private lemma jc10_unitCell_farUp_even_eq :
-- imply
  Even (jec_rayCount (![0, 5] : Site 2) (mpl_orbitLoop unitCell ucBase)) := by
-- proof
  apply StatMech.Walls.jc10_unitCell_farUp_even


-- created on 2026-10-23
