import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.kc4_exterioreven
open Set SimpleGraph Function StatMech.Lattice StatMech StatMech.Walls


/--
[kc4_farLeft_rayCount_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_exterioreven.lean)
-/
@[path]
private lemma kc4_farLeft_rayCount_zero_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2}
-- given
  (hfar : ∀ p ∈ Vc.support, z 0 ≤ p 0) :
-- imply
  jec_rayCount z Vc = 0 := by
-- proof
  apply StatMech.Walls.kc4_farLeft_rayCount_zero Vc z hfar

/--
[kc4_farLeft_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_exterioreven.lean)
-/
@[path]
private lemma kc4_farLeft_even_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2}
-- given
  (hfar : ∀ p ∈ Vc.support, z 0 ≤ p 0) :
-- imply
  Even (jec_rayCount z Vc) := by
-- proof
  apply StatMech.Walls.kc4_farLeft_even Vc z hfar

/--
[kc4_farLeft_not_mem_leftRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_exterioreven.lean)
-/
@[path]
private lemma kc4_farLeft_not_mem_leftRegion_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2}
-- given
  (hfar : ∀ p ∈ Vc.support, z 0 ≤ p 0) :
-- imply
  z ∉ jec_leftRegion Vc := by
-- proof
  apply StatMech.Walls.kc4_farLeft_not_mem_leftRegion Vc z hfar

/--
[kc4_exterior_reaches_farLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_exterioreven.lean)
-/
@[path]
private lemma kc4_exterior_reaches_farLeft_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z : Site 2}
-- given
  (hR : ({z | z ∈ Vc.support} : Set (Site 2)) ⊆ box 2 R)
  (hz : z ∈ exterior 2 R) :
-- imply
  ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0, (∀ w ∈ p.support, w ∉ Vc.support) ∧ (∀ q ∈ Vc.support, z0 0 ≤ q 0) := by
-- proof
  apply StatMech.Walls.kc4_exterior_reaches_farLeft Vc R hR z hz

/--
[kc4_exterior_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_exterioreven.lean)
-/
@[path]
private lemma kc4_exterior_even_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z : Site 2}
-- given
  (hR : ({z | z ∈ Vc.support} : Set (Site 2)) ⊆ box 2 R)
  (hz : z ∈ exterior 2 R) :
-- imply
  Even (jec_rayCount z Vc) := by
-- proof
  apply StatMech.Walls.kc4_exterior_even Vc R hR z hz

/--
[kc4_exterior_not_mem_leftRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_exterioreven.lean)
-/
@[path]
private lemma kc4_exterior_not_mem_leftRegion_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {z : Site 2}
-- given
  (hR : ({z | z ∈ Vc.support} : Set (Site 2)) ⊆ box 2 R)
  (hz : z ∈ exterior 2 R) :
-- imply
  z ∉ jec_leftRegion Vc := by
-- proof
  apply StatMech.Walls.kc4_exterior_not_mem_leftRegion Vc R hR z hz

/--
[kc4_orbitLoop_exterior_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_exterioreven.lean)
-/
@[path]
private lemma kc4_orbitLoop_exterior_even_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {R : ℕ}
  {z : Site 2}
-- given
  (hR : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
  (hz : z ∈ exterior 2 R) :
-- imply
  Even (jec_rayCount z (mpl_orbitLoop K a)) := by
-- proof
  apply StatMech.Walls.kc4_orbitLoop_exterior_even K a R hR z hz

/--
[kc4_orbitLoop_exterior_not_mem_leftRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_exterioreven.lean)
-/
@[path]
private lemma kc4_orbitLoop_exterior_not_mem_leftRegion_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {R : ℕ}
  {z : Site 2}
-- given
  (hR : ({z | z ∈ (mpl_orbitLoop K a).support} : Set (Site 2)) ⊆ box 2 R)
  (hz : z ∈ exterior 2 R) :
-- imply
  z ∉ jec_leftRegion (mpl_orbitLoop K a) := by
-- proof
  apply StatMech.Walls.kc4_orbitLoop_exterior_not_mem_leftRegion K a R hR z hz

/--
[kc4_exteriorEven_node](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc4_exterioreven.lean)
-/
@[path]
private lemma kc4_exteriorEven_node_eq :
-- imply
  (∀ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a) (z : Site 2), (∀ p ∈ Vc.support, z 0 ≤ p 0) → jec_rayCount z Vc = 0) ∧ (∀ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ), ({z | z ∈ Vc.support} : Set (Site 2)) ⊆ box 2 R → ∀ z ∈ exterior 2 R, ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0, (∀ w ∈ p.support, w ∉ Vc.support) ∧ (∀ q ∈ Vc.support, z0 0 ≤ q 0)) ∧ (∀ (a : Site 2) (Vc : (hypercubicLattice 2).Walk a a) (R : ℕ), ({z | z ∈ Vc.support} : Set (Site 2)) ⊆ box 2 R → ∀ z ∈ exterior 2 R, z ∉ jec_leftRegion Vc) := by
-- proof
  apply StatMech.Walls.kc4_exteriorEven_node


-- created on 2026-10-23
