import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.kc2_crosscountparity
open Set SimpleGraph Function StatMech.Lattice StatMech StatMech.Walls


/--
[kc2_crossCount_parity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_crosscountparity.lean)
-/
@[path]
private lemma kc2_crossCount_parity_eq
  {S : Set (Site 2)}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y} :
-- imply
  Even (crossCount S w) ↔ (x ∈ S ↔ y ∈ S) := by
-- proof
  apply StatMech.Walls.kc2_crossCount_parity S w

/--
[kc2_crossCount_even_of_loop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_crosscountparity.lean)
-/
@[path]
private lemma kc2_crossCount_even_of_loop_eq
  {S : Set (Site 2)}
  {x : Site 2}
  {w : (hypercubicLattice 2).Walk x x} :
-- imply
  Even (crossCount S w) := by
-- proof
  apply StatMech.Walls.kc2_crossCount_even_of_loop S w

/--
[kc2_crossCount_odd_of_separated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_crosscountparity.lean)
-/
@[path]
private lemma kc2_crossCount_odd_of_separated_eq
  {S : Set (Site 2)}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (hx : x ∈ S)
  (hy : y ∉ S) :
-- imply
  ¬ Even (crossCount S w) := by
-- proof
  apply StatMech.Walls.kc2_crossCount_odd_of_separated S hx hy w

/--
[kc2_crossCount_parity_eq_of_sameEndpoints](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_crosscountparity.lean)
-/
@[path]
private lemma kc2_crossCount_parity_eq_of_sameEndpoints_eq
  {S : Set (Site 2)}
  {x y : Site 2}
  {w₁ w₂ : (hypercubicLattice 2).Walk x y} :
-- imply
  crossCount S w₁ % 2 = crossCount S w₂ % 2 := by
-- proof
  apply StatMech.Walls.kc2_crossCount_parity_eq_of_sameEndpoints S w₁ w₂

/--
[kc2_rayCount_eq_zero_farLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_crosscountparity.lean)
-/
@[path]
private lemma kc2_rayCount_eq_zero_farLeft_eq
  {z : Site 2}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (hfar : ∀ p ∈ w.support, z 0 ≤ p 0) :
-- imply
  jec_rayCount z w = 0 := by
-- proof
  apply StatMech.Walls.kc2_rayCount_eq_zero_farLeft z w hfar

/--
[kc2_ray_even_farLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_crosscountparity.lean)
-/
@[path]
private lemma kc2_ray_even_farLeft_eq
  {z : Site 2}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (hfar : ∀ p ∈ w.support, z 0 ≤ p 0) :
-- imply
  Even (jec_rayCount z w) := by
-- proof
  apply StatMech.Walls.kc2_ray_even_farLeft z w hfar

/--
[kc2_not_mem_leftRegion_farLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_crosscountparity.lean)
-/
@[path]
private lemma kc2_not_mem_leftRegion_farLeft_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2}
-- given
  (hfar : ∀ p ∈ Vc.support, z 0 ≤ p 0) :
-- imply
  z ∉ jec_leftRegion Vc := by
-- proof
  apply StatMech.Walls.kc2_not_mem_leftRegion_farLeft Vc z hfar

/--
[kc2_ray_even_farRight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_crosscountparity.lean)
-/
@[path]
private lemma kc2_ray_even_farRight_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2}
-- given
  (hfar : ∀ p ∈ Vc.support, p 0 ≤ z 0 - 1) :
-- imply
  Even (jec_rayCount z Vc) := by
-- proof
  apply StatMech.Walls.kc2_ray_even_farRight Vc z hfar

/--
[kc2_crossCountParity_node](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_crosscountparity.lean)
-/
@[path]
private lemma kc2_crossCountParity_node_eq :
-- imply
  (∀ (S : Set (Site 2)) (x y : Site 2) (w : (hypercubicLattice 2).Walk x y), Even (crossCount S w) ↔ (x ∈ S ↔ y ∈ S)) ∧ (∀ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a) (z : Site 2), (∀ p ∈ Vc.support, z 0 ≤ p 0) → z ∉ jec_leftRegion Vc) := by
-- proof
  apply StatMech.Walls.kc2_crossCountParity_node


-- created on 2026-10-23
