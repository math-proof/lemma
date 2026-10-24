import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.OrbitExteriorEven
open Set SimpleGraph StatMech StatMech.Lattice


/--
[oee_rayParity_const_along_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitExteriorEven.lean)
-/
@[path]
private lemma oee_rayParity_const_along_walk_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : Site 2}
  {p : (hypercubicLattice 2).Walk x y}
-- given
  (hp : ∀ z ∈ p.support, z ∉ Vc.support) :
-- imply
  (Even (jec_rayCount x Vc) ↔ Even (jec_rayCount y Vc)) := by
-- proof
  apply StatMech.Lattice.oee_rayParity_const_along_walk Vc p hp

/--
[oee_rayCount_eq_zero_of_farLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitExteriorEven.lean)
-/
@[path]
private lemma oee_rayCount_eq_zero_of_farLeft_eq
  {K : Set (Site 2)}
  {e : Dart}
  {z : Site 2}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hfar : ∀ p ∈ (olb_orbitLoop K hK e he).support, z 0 ≤ p 0) :
-- imply
  jec_rayCount z (olb_orbitLoop K hK e he) = 0 := by
-- proof
  apply StatMech.Lattice.oee_rayCount_eq_zero_of_farLeft K hK e he z hfar

/--
[oee_farLeft_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitExteriorEven.lean)
-/
@[path]
private lemma oee_farLeft_even_eq
  {K : Set (Site 2)}
  {e : Dart}
  {z : Site 2}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hfar : ∀ p ∈ (olb_orbitLoop K hK e he).support, z 0 ≤ p 0) :
-- imply
  Even (jec_rayCount z (olb_orbitLoop K hK e he)) := by
-- proof
  apply StatMech.Lattice.oee_farLeft_even K hK e he z hfar

/--
[oee_exterior_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitExteriorEven.lean)
-/
@[path]
private lemma oee_exterior_even_eq
  {K : Set (Site 2)}
  {e : Dart}
  {z z0 : Site 2}
  {p : (hypercubicLattice 2).Walk z z0}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hp : ∀ w ∈ p.support, w ∉ (olb_orbitLoop K hK e he).support)
  (hfar : ∀ q ∈ (olb_orbitLoop K hK e he).support, z0 0 ≤ q 0) :
-- imply
  Even (jec_rayCount z (olb_orbitLoop K hK e he)) := by
-- proof
  apply StatMech.Lattice.oee_exterior_even K hK e he p hp hfar

/--
[oee_outsideHalf_of_exteriorEq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/OrbitExteriorEven.lean)
-/
@[path]
private lemma oee_outsideHalf_of_exteriorEq_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hExt : ∀ z, z ∉ K → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0, (∀ w ∈ p.support, w ∉ (olb_orbitLoop K hK e he).support) ∧ (∀ q ∈ (olb_orbitLoop K hK e he).support, z0 0 ≤ q 0)) :
-- imply
  ∀ z, z ∉ K → Even (jec_rayCount z (olb_orbitLoop K hK e he)) := by
-- proof
  apply StatMech.Lattice.oee_outsideHalf_of_exteriorEq K hK e he hExt


-- created on 2026-10-23
