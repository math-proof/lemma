import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.jc9core.Part2
open Set SimpleGraph Function StatMech StatMech.Walls


/--
[jc9_crossCount_parity_side](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc9core.lean)
-/
@[path]
private lemma jc9_crossCount_parity_side_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y} :
-- imply
  Even (crossCount (jec_leftRegion (mpl_orbitLoop K a)) w) ↔ (x ∈ jec_leftRegion (mpl_orbitLoop K a) ↔ y ∈ jec_leftRegion (mpl_orbitLoop K a)) := by
-- proof
  apply StatMech.Walls.jc9_crossCount_parity_side K a w

/--
[jc9_crossCount_ge_one_of_opposite_side](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc9core.lean)
-/
@[path]
private lemma jc9_crossCount_ge_one_of_opposite_side_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (hx : x ∈ jec_leftRegion (mpl_orbitLoop K a))
  (hy : y ∉ jec_leftRegion (mpl_orbitLoop K a)) :
-- imply
  1 ≤ crossCount (jec_leftRegion (mpl_orbitLoop K a)) w := by
-- proof
  apply StatMech.Walls.jc9_crossCount_ge_one_of_opposite_side K a w hx hy

/--
[jc9_exists_farLeft_notMem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc9core.lean)
-/
@[path]
private lemma jc9_exists_farLeft_notMem_eq
  {K F : Set (Site 2)}
-- given
  (hK : K.Finite)
  (hF : F.Finite) :
-- imply
  ∃ q : Site 2, (∀ p ∈ F, q 0 ≤ p 0) ∧ q ∉ K := by
-- proof
  apply StatMech.Walls.jc9_exists_farLeft_notMem hK hF

/--
[jc9_orbitLoop_support_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc9core.lean)
-/
@[path]
private lemma jc9_orbitLoop_support_finite_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  {p : Site 2 | p ∈ (mpl_orbitLoop K a).support}.Finite := by
-- proof
  apply StatMech.Walls.jc9_orbitLoop_support_finite K a

/--
[jc9_farLeft_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc9core.lean)
-/
@[path]
private lemma jc9_farLeft_even_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {z : Site 2}
-- given
  (hfar : ∀ p ∈ (mpl_orbitLoop K a).support, z 0 ≤ p 0) :
-- imply
  Even (jec_rayCount z (mpl_orbitLoop K a)) := by
-- proof
  apply StatMech.Walls.jc9_farLeft_even K a z hfar

/--
[jc9_exterior_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc9core.lean)
-/
@[path]
private lemma jc9_exterior_even_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {z z0 : Site 2}
  {p : (hypercubicLattice 2).Walk z z0}
-- given
  (hp : ∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support)
  (hfar : ∀ q ∈ (mpl_orbitLoop K a).support, z0 0 ≤ q 0) :
-- imply
  Even (jec_rayCount z (mpl_orbitLoop K a)) := by
-- proof
  apply StatMech.Walls.jc9_exterior_even K a p hp hfar

/--
[jc9_outsideHalf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc9core.lean)
-/
@[path]
private lemma jc9_outsideHalf_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hExt : ∀ z, z ∉ K → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0, (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support) ∧ (∀ q ∈ (mpl_orbitLoop K a).support, z0 0 ≤ q 0)) :
-- imply
  ∀ z, z ∉ K → Even (jec_rayCount z (mpl_orbitLoop K a)) := by
-- proof
  apply StatMech.Walls.jc9_outsideHalf K a hExt

/--
[jc9_inside_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc9core.lean)
-/
@[path]
private lemma jc9_inside_odd_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {z0 : Site 2}
-- given
  (hz0K : z0 ∈ K)
  (hodd0 : ¬ Even (jec_rayCount z0 (mpl_orbitLoop K a)))
  (hInt : ∀ z, z ∈ K → ∃ p : (hypercubicLattice 2).Walk z z0, (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support)) :
-- imply
  ∀ z, z ∈ K → ¬ Even (jec_rayCount z (mpl_orbitLoop K a)) := by
-- proof
  apply StatMech.Walls.jc9_inside_odd K a hz0K hodd0 hInt

/--
[jc9_clusterEqLeftRegion_of_windingWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc9core.lean)
-/
@[path]
private lemma jc9_clusterEqLeftRegion_of_windingWitness_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {z0 : Site 2}
-- given
  (hExt : ∀ z, z ∉ K → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0, (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support) ∧ (∀ q ∈ (mpl_orbitLoop K a).support, z0 0 ≤ q 0))
  (hz0K : z0 ∈ K)
  (hodd0 : ¬ Even (jec_rayCount z0 (mpl_orbitLoop K a)))
  (hInt : ∀ z, z ∈ K → ∃ p : (hypercubicLattice 2).Walk z z0, (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support)) :
-- imply
  K = jec_leftRegion (mpl_orbitLoop K a) := by
-- proof
  apply StatMech.Walls.jc9_clusterEqLeftRegion_of_windingWitness K a hExt hz0K hodd0 hInt

/--
[jc9_bdEdgeMatch_of_windingWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc9core.lean)
-/
@[path]
private lemma jc9_bdEdgeMatch_of_windingWitness_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {z0 : Site 2}
-- given
  (hExt : ∀ z, z ∉ K → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0, (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support) ∧ (∀ q ∈ (mpl_orbitLoop K a).support, z0 0 ≤ q 0))
  (hz0K : z0 ∈ K)
  (hodd0 : ¬ Even (jec_rayCount z0 (mpl_orbitLoop K a)))
  (hInt : ∀ z, z ∈ K → ∃ p : (hypercubicLattice 2).Walk z z0, (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support)) :
-- imply
  pww_BdEdgeMatch K (mpl_orbitLoop K a) := by
-- proof
  apply StatMech.Walls.jc9_bdEdgeMatch_of_windingWitness K a hExt hz0K hodd0 hInt

/--
[jc9_bdEdgeMatch_iff_setIdentity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc9core.lean)
-/
@[path]
private lemma jc9_bdEdgeMatch_iff_setIdentity_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  pww_BdEdgeMatch K (mpl_orbitLoop K a) ↔ (K = jec_leftRegion (mpl_orbitLoop K a) ∨ K = (jec_leftRegion (mpl_orbitLoop K a))ᶜ) := by
-- proof
  apply StatMech.Walls.jc9_bdEdgeMatch_iff_setIdentity K a

/--
[jc9_bdEdgeMatch_of_leftRegion_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc9core.lean)
-/
@[path]
private lemma jc9_bdEdgeMatch_of_leftRegion_eq_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (h : K = jec_leftRegion (mpl_orbitLoop K a)) :
-- imply
  pww_BdEdgeMatch K (mpl_orbitLoop K a) := by
-- proof
  apply StatMech.Walls.jc9_bdEdgeMatch_of_leftRegion_eq K a h

/--
[jc9_bdEdgeMatch_iff_leftRegion_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc9core.lean)
-/
@[path]
private lemma jc9_bdEdgeMatch_iff_leftRegion_eq_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {R : ℕ}
-- given
  (hsupp : ∀ p ∈ (mpl_orbitLoop K a).support, p ∈ box 2 R)
  (hKfin : K.Finite) :
-- imply
  pww_BdEdgeMatch K (mpl_orbitLoop K a) ↔ K = jec_leftRegion (mpl_orbitLoop K a) := by
-- proof
  apply StatMech.Walls.jc9_bdEdgeMatch_iff_leftRegion_eq K a R hsupp hKfin

/--
[jc9_unitCell_bdEdgeMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc9core.lean)
-/
@[path]
private lemma jc9_unitCell_bdEdgeMatch_eq :
-- imply
  pww_BdEdgeMatch unitCell (mpl_orbitLoop unitCell ucBase) := by
-- proof
  apply StatMech.Walls.jc9_unitCell_bdEdgeMatch

/--
[jc9_unitCell_eq_leftRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc9core.lean)
-/
@[path]
private lemma jc9_unitCell_eq_leftRegion_eq :
-- imply
  unitCell = jec_leftRegion (mpl_orbitLoop unitCell ucBase) := by
-- proof
  apply StatMech.Walls.jc9_unitCell_eq_leftRegion

/--
[jc9_unitCell_windingWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc9core.lean)
-/
@[path]
private lemma jc9_unitCell_windingWitness_eq :
-- imply
  ¬ Even (jec_rayCount (![0, 0] : Site 2) (mpl_orbitLoop unitCell ucBase)) := by
-- proof
  apply StatMech.Walls.jc9_unitCell_windingWitness

/--
[jc9_FaceInsideInterval_iff_clusterInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc9core.lean)
-/
@[path]
private lemma jc9_FaceInsideInterval_iff_clusterInterval_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (h : K = jec_leftRegion (olb_orbitLoop K hK e he)) :
-- imply
  jc8c_FaceInsideInterval K hK e he ↔ (∀ i j k : ℕ, i < j → j < k → dartFace ((dartNext K)^[i] e) ∈ K → dartFace ((dartNext K)^[k] e) ∈ K → dartFace ((dartNext K)^[j] e) ∈ K) := by
-- proof
  apply StatMech.Walls.jc9_FaceInsideInterval_iff_clusterInterval K hK e he h

/--
[jc9_bdEdgeMatch_of_inputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc9core.lean)
-/
@[path]
private lemma jc9_bdEdgeMatch_of_inputs_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {z0 : Site 2}
-- given
  (h : jc9_InteriornessInputs K a z0) :
-- imply
  pww_BdEdgeMatch K (mpl_orbitLoop K a) := by
-- proof
  apply StatMech.Walls.jc9_bdEdgeMatch_of_inputs K a h

/--
[jc9_inputs_realised_unitCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc9core.lean)
-/
@[path]
private lemma jc9_inputs_realised_unitCell_eq :
-- imply
  pww_BdEdgeMatch unitCell (mpl_orbitLoop unitCell ucBase) := by
-- proof
  apply StatMech.Walls.jc9_inputs_realised_unitCell


-- created on 2026-10-23
