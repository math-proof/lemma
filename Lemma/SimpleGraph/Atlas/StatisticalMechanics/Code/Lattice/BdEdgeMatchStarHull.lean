import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.BdEdgeMatchStarHull
open Set SimpleGraph StatMech StatMech.Lattice


/--
[pbs_reach_axis_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BdEdgeMatchStarHull.lean)
-/
@[path]
private lemma pbs_reach_axis_le_eq
  {x : Site 2}
  {j : Fin 2}
  {a : ℤ}
  {n : ℕ} :
-- imply
  (hypercubicLattice 2).Reachable (Function.update x j a) (Function.update x j (a + (n : ℤ))) := by
-- proof
  apply StatMech.Lattice.pbs_reach_axis_le x j a n

/--
[pbs_reach_axis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BdEdgeMatchStarHull.lean)
-/
@[path]
private lemma pbs_reach_axis_eq
  {x : Site 2}
  {j : Fin 2}
  {a b : ℤ} :
-- imply
  (hypercubicLattice 2).Reachable (Function.update x j a) (Function.update x j b) := by
-- proof
  apply StatMech.Lattice.pbs_reach_axis x j a b

/--
[pbs_reach_all](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BdEdgeMatchStarHull.lean)
-/
@[path]
private lemma pbs_reach_all_eq
  {x y : Site 2} :
-- imply
  (hypercubicLattice 2).Reachable x y := by
-- proof
  apply StatMech.Lattice.pbs_reach_all x y

/--
[pbs_bdEdge_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BdEdgeMatchStarHull.lean)
-/
@[path]
private lemma pbs_bdEdge_compl_eq
  {S : Set (Site 2)}
  {e : Sym2 (Site 2)} :
-- imply
  bdEdge S e ↔ bdEdge Sᶜ e := by
-- proof
  apply StatMech.Lattice.pbs_bdEdge_compl S e

/--
[pbs_bdEdge_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BdEdgeMatchStarHull.lean)
-/
@[path]
private lemma pbs_bdEdge_congr_eq
  {S T : Set (Site 2)}
  {e : Sym2 (Site 2)}
-- given
  (h : S = T) :
-- imply
  bdEdge S e ↔ bdEdge T e := by
-- proof
  apply StatMech.Lattice.pbs_bdEdge_congr h e

/--
[pbs_agree_const_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BdEdgeMatchStarHull.lean)
-/
@[path]
private lemma pbs_agree_const_walk_eq
  {S T : Set (Site 2)}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (hbd : ∀ e : Sym2 (Site 2), bdEdge S e ↔ bdEdge T e) :
-- imply
  ((x ∈ S ↔ x ∈ T) ↔ (y ∈ S ↔ y ∈ T)) := by
-- proof
  apply StatMech.Lattice.pbs_agree_const_walk S T hbd w

/--
[pbs_agree_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BdEdgeMatchStarHull.lean)
-/
@[path]
private lemma pbs_agree_const_eq
  {S T : Set (Site 2)}
  {x y : Site 2}
-- given
  (hbd : ∀ e : Sym2 (Site 2), bdEdge S e ↔ bdEdge T e) :
-- imply
  ((x ∈ S ↔ x ∈ T) ↔ (y ∈ S ↔ y ∈ T)) := by
-- proof
  apply StatMech.Lattice.pbs_agree_const S T hbd x y

/--
[pbs_setIdentity_of_bdEdge_match](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BdEdgeMatchStarHull.lean)
-/
@[path]
private lemma pbs_setIdentity_of_bdEdge_match_eq
  {S T : Set (Site 2)}
-- given
  (hbd : ∀ e : Sym2 (Site 2), bdEdge S e ↔ bdEdge T e) :
-- imply
  S = T ∨ S = Tᶜ := by
-- proof
  apply StatMech.Lattice.pbs_setIdentity_of_bdEdge_match S T hbd

/--
[pbs_bdEdgeMatch_of_setIdentity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BdEdgeMatchStarHull.lean)
-/
@[path]
private lemma pbs_bdEdgeMatch_of_setIdentity_eq
  {K : Set (Site 2)}
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (h : K = jec_leftRegion Vc ∨ K = (jec_leftRegion Vc)ᶜ) :
-- imply
  pww_BdEdgeMatch K Vc := by
-- proof
  apply StatMech.Lattice.pbs_bdEdgeMatch_of_setIdentity Vc h

/--
[pbs_bdEdgeMatch_iff_setIdentity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BdEdgeMatchStarHull.lean)
-/
@[path]
private lemma pbs_bdEdgeMatch_iff_setIdentity_eq
  {K : Set (Site 2)}
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a} :
-- imply
  pww_BdEdgeMatch K Vc ↔ (K = jec_leftRegion Vc ∨ K = (jec_leftRegion Vc)ᶜ) := by
-- proof
  apply StatMech.Lattice.pbs_bdEdgeMatch_iff_setIdentity Vc

/--
[pbs_bdEdgeMatch_of_leftRegion_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BdEdgeMatchStarHull.lean)
-/
@[path]
private lemma pbs_bdEdgeMatch_of_leftRegion_eq_eq
  {K : Set (Site 2)}
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (h : K = jec_leftRegion Vc) :
-- imply
  pww_BdEdgeMatch K Vc := by
-- proof
  apply StatMech.Lattice.pbs_bdEdgeMatch_of_leftRegion_eq Vc h

/--
[pbs_bdEdgeMatch_of_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BdEdgeMatchStarHull.lean)
-/
@[path]
private lemma pbs_bdEdgeMatch_of_winding_eq
  {K : Set (Site 2)}
  {e : Dart}
  {z0 : Site 2}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hExt : ∀ z, z ∉ K → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0, (∀ w ∈ p.support, w ∉ (olb_orbitLoop K hK e he).support) ∧ (∀ q ∈ (olb_orbitLoop K hK e he).support, z0 0 ≤ q 0))
  (_hz0K : z0 ∈ K)
  (hodd0 : ¬ Even (jec_rayCount z0 (olb_orbitLoop K hK e he)))
  (hInt : ∀ z, z ∈ K → ∃ p : (hypercubicLattice 2).Walk z z0, (∀ w ∈ p.support, w ∉ (olb_orbitLoop K hK e he).support)) :
-- imply
  pww_BdEdgeMatch K (olb_orbitLoop K hK e he) := by
-- proof
  apply StatMech.Lattice.pbs_bdEdgeMatch_of_winding K hK e he hExt _hz0K hodd0 hInt

/--
[pbs_bdEdgeMatch_starHull_of_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BdEdgeMatchStarHull.lean)
-/
@[path]
private lemma pbs_bdEdgeMatch_starHull_of_winding_eq
  {K : Set (Site 2)}
  {e : Dart}
  {z0 : Site 2}
-- given
  (hSK : (ndt_StarHull K).Finite)
  (he : IsBoundaryDart (ndt_StarHull K) e)
  (hExt : ∀ z, z ∉ ndt_StarHull K → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0, (∀ w ∈ p.support, w ∉ (olb_orbitLoop (ndt_StarHull K) hSK e he).support) ∧ (∀ q ∈ (olb_orbitLoop (ndt_StarHull K) hSK e he).support, z0 0 ≤ q 0))
  (hz0K : z0 ∈ ndt_StarHull K)
  (hodd0 : ¬ Even (jec_rayCount z0 (olb_orbitLoop (ndt_StarHull K) hSK e he)))
  (hInt : ∀ z, z ∈ ndt_StarHull K → ∃ p : (hypercubicLattice 2).Walk z z0, (∀ w ∈ p.support, w ∉ (olb_orbitLoop (ndt_StarHull K) hSK e he).support)) :
-- imply
  pww_BdEdgeMatch (ndt_StarHull K) (olb_orbitLoop (ndt_StarHull K) hSK e he) := by
-- proof
  apply StatMech.Lattice.pbs_bdEdgeMatch_starHull_of_winding K hSK e he hExt hz0K hodd0 hInt

/--
[pbs_bdEdgeMatch_starHull_iff_setIdentity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BdEdgeMatchStarHull.lean)
-/
@[path]
private lemma pbs_bdEdgeMatch_starHull_iff_setIdentity_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hSK : (ndt_StarHull K).Finite)
  (he : IsBoundaryDart (ndt_StarHull K) e) :
-- imply
  pww_BdEdgeMatch (ndt_StarHull K) (olb_orbitLoop (ndt_StarHull K) hSK e he) ↔ (ndt_StarHull K = jec_leftRegion (olb_orbitLoop (ndt_StarHull K) hSK e he) ∨ ndt_StarHull K = (jec_leftRegion (olb_orbitLoop (ndt_StarHull K) hSK e he))ᶜ) := by
-- proof
  apply StatMech.Lattice.pbs_bdEdgeMatch_starHull_iff_setIdentity K hSK e he

/--
[pbs_bdEdgeMatch_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BdEdgeMatchStarHull.lean)
-/
@[path]
private lemma pbs_bdEdgeMatch_self_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a} :
-- imply
  pww_BdEdgeMatch (jec_leftRegion Vc) Vc := by
-- proof
  apply StatMech.Lattice.pbs_bdEdgeMatch_self Vc

/--
[pbs_bdEdgeMatch_originCluster_of_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BdEdgeMatchStarHull.lean)
-/
@[path]
private lemma pbs_bdEdgeMatch_originCluster_of_winding_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {e : Dart}
-- given
  (hfin : (cluster 2 ω (origin 2)).Finite)
  (he : IsBoundaryDart (cluster 2 ω (origin 2)) e)
  (ho : origin 2 ∈ cluster 2 ω (origin 2))
  (hExt : ∀ z, z ∉ cluster 2 ω (origin 2) → ∃ z0 : Site 2, ∃ p : (hypercubicLattice 2).Walk z z0, (∀ w ∈ p.support, w ∉ (olb_orbitLoop (cluster 2 ω (origin 2)) hfin e he).support) ∧ (∀ q ∈ (olb_orbitLoop (cluster 2 ω (origin 2)) hfin e he).support, z0 0 ≤ q 0))
  (hodd0 : ¬ Even (jec_rayCount (origin 2) (olb_orbitLoop (cluster 2 ω (origin 2)) hfin e he)))
  (hInt : ∀ z, z ∈ cluster 2 ω (origin 2) → ∃ p : (hypercubicLattice 2).Walk z (origin 2), (∀ w ∈ p.support, w ∉ (olb_orbitLoop (cluster 2 ω (origin 2)) hfin e he).support)) :
-- imply
  pww_BdEdgeMatch (cluster 2 ω (origin 2)) (olb_orbitLoop (cluster 2 ω (origin 2)) hfin e he) := by
-- proof
  apply StatMech.Lattice.pbs_bdEdgeMatch_originCluster_of_winding hfin e he ho hExt hodd0 hInt


-- created on 2026-10-23
