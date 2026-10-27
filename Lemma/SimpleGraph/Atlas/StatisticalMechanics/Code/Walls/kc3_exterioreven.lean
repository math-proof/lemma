import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.kc3_exterioreven
open Set SimpleGraph Function StatMech.Lattice StatMech StatMech.Walls


/--
[kc3_rayCount_eq_zero_of_farLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_exterioreven.lean)
-/
@[path]
private lemma kc3_rayCount_eq_zero_of_farLeft_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2}
-- given
  (hfar : ∀ p ∈ Vc.support, z 0 ≤ p 0) :
-- imply
  jec_rayCount z Vc = 0 := by
-- proof
  apply StatMech.Walls.kc3_rayCount_eq_zero_of_farLeft Vc z hfar

/--
[kc3_farLeft_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_exterioreven.lean)
-/
@[path]
private lemma kc3_farLeft_even_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2}
-- given
  (hfar : ∀ p ∈ Vc.support, z 0 ≤ p 0) :
-- imply
  Even (jec_rayCount z Vc) := by
-- proof
  apply StatMech.Walls.kc3_farLeft_even Vc z hfar

/--
[kc3_farLeft_not_mem_leftRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_exterioreven.lean)
-/
@[path]
private lemma kc3_farLeft_not_mem_leftRegion_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2}
-- given
  (hfar : ∀ p ∈ Vc.support, z 0 ≤ p 0) :
-- imply
  z ∉ jec_leftRegion Vc := by
-- proof
  apply StatMech.Walls.kc3_farLeft_not_mem_leftRegion Vc z hfar

/--
[kc3_rayParity_const_along_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_exterioreven.lean)
-/
@[path]
private lemma kc3_rayParity_const_along_walk_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : Site 2}
  {p : (hypercubicLattice 2).Walk x y}
-- given
  (hp : ∀ z ∈ p.support, z ∉ Vc.support) :
-- imply
  (Even (jec_rayCount x Vc) ↔ Even (jec_rayCount y Vc)) := by
-- proof
  apply StatMech.Walls.kc3_rayParity_const_along_walk Vc p hp

/--
[kc3_exterior_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_exterioreven.lean)
-/
@[path]
private lemma kc3_exterior_even_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z z0 : Site 2}
  {p : (hypercubicLattice 2).Walk z z0}
-- given
  (hp : ∀ w ∈ p.support, w ∉ Vc.support)
  (hfar : ∀ q ∈ Vc.support, z0 0 ≤ q 0) :
-- imply
  Even (jec_rayCount z Vc) := by
-- proof
  apply StatMech.Walls.kc3_exterior_even Vc p hp hfar

/--
[kc3_exterior_even_of_reachesFarLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_exterioreven.lean)
-/
@[path]
private lemma kc3_exterior_even_of_reachesFarLeft_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2}
-- given
  (h : ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0, (∀ w ∈ p.support, w ∉ Vc.support) ∧ (∀ q ∈ Vc.support, z0 0 ≤ q 0)) :
-- imply
  Even (jec_rayCount z Vc) := by
-- proof
  apply StatMech.Walls.kc3_exterior_even_of_reachesFarLeft Vc h

/--
[kc3_exterior_not_mem_leftRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_exterioreven.lean)
-/
@[path]
private lemma kc3_exterior_not_mem_leftRegion_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z z0 : Site 2}
  {p : (hypercubicLattice 2).Walk z z0}
-- given
  (hp : ∀ w ∈ p.support, w ∉ Vc.support)
  (hfar : ∀ q ∈ Vc.support, z0 0 ≤ q 0) :
-- imply
  z ∉ jec_leftRegion Vc := by
-- proof
  apply StatMech.Walls.kc3_exterior_not_mem_leftRegion Vc p hp hfar

/--
[kc3_exteriorEven_node](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_exterioreven.lean)
-/
@[path]
private lemma kc3_exteriorEven_node_eq :
-- imply
  (∀ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a) (z : Site 2), (∀ p ∈ Vc.support, z 0 ≤ p 0) → jec_rayCount z Vc = 0) ∧ (∀ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a) (x y : Site 2) (p : (hypercubicLattice 2).Walk x y), (∀ z ∈ p.support, z ∉ Vc.support) → (Even (jec_rayCount x Vc) ↔ Even (jec_rayCount y Vc))) ∧ (∀ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a) (z z0 : Site 2) (p : (hypercubicLattice 2).Walk z z0), (∀ w ∈ p.support, w ∉ Vc.support) → (∀ q ∈ Vc.support, z0 0 ≤ q 0) → Even (jec_rayCount z Vc)) := by
-- proof
  apply StatMech.Walls.kc3_exteriorEven_node


-- created on 2026-10-23
