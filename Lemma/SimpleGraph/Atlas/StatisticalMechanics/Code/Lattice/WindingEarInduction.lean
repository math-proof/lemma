import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.WindingEarInduction
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[wei_mpl_orbitLoop_edges_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingEarInduction.lean)
-/
@[path]
private lemma wei_mpl_orbitLoop_edges_eq_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  (mpl_orbitLoop K a).edges = (List.range (dartOrbitPeriod K a)).map (fun k => s(dartFace ((dartNext K)^[k] a.1), dartFace ((dartNext K)^[k + 1] a.1))) := by
-- proof
  apply StatMech.Lattice.wei_mpl_orbitLoop_edges_eq K a

/--
[wei_rayCount_of_perm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingEarInduction.lean)
-/
@[path]
private lemma wei_rayCount_of_perm_eq
  {a b : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {Vc' : (hypercubicLattice 2).Walk b b}
  {z : Site 2}
-- given
  (hperm : List.Perm Vc.edges Vc'.edges) :
-- imply
  jec_rayCount z Vc = jec_rayCount z Vc' := by
-- proof
  apply StatMech.Lattice.wei_rayCount_of_perm Vc Vc' z hperm

/--
[wei_rayCount_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingEarInduction.lean)
-/
@[path]
private lemma wei_rayCount_congr_eq
  {K K' : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {a' : {e : Dart // IsBoundaryDart K' e}}
  {z : Site 2}
-- given
  (hKK : K = K')
  (ha : a.1 = a'.1) :
-- imply
  jec_rayCount z (mpl_orbitLoop K a) = jec_rayCount z (mpl_orbitLoop K' a') := by
-- proof
  apply StatMech.Lattice.wei_rayCount_congr K K' hKK a a' ha z

/--
[wei_loop_edges_diff_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingEarInduction.lean)
-/
@[path]
private lemma wei_loop_edges_diff_singleton_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {a : {e : Dart // IsBoundaryDart K e}}
  {a' : {e : Dart // IsBoundaryDart (K \ {c}) e}}
-- given
  (hval : a'.1 = a.1)
  (hnp : ∀ i, bpc_NotProbed c ((dartNext K)^[i] a.1)) :
-- imply
  (mpl_orbitLoop (K \ {c}) a').edges = (mpl_orbitLoop K a).edges := by
-- proof
  apply StatMech.Lattice.wei_loop_edges_diff_singleton K c a a' hval hnp

/--
[wei_rayCount_diff_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingEarInduction.lean)
-/
@[path]
private lemma wei_rayCount_diff_singleton_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {a : {e : Dart // IsBoundaryDart K e}}
  {a' : {e : Dart // IsBoundaryDart (K \ {c}) e}}
  {z : Site 2}
-- given
  (hval : a'.1 = a.1)
  (hnp : ∀ i, bpc_NotProbed c ((dartNext K)^[i] a.1)) :
-- imply
  jec_rayCount z (mpl_orbitLoop (K \ {c}) a') = jec_rayCount z (mpl_orbitLoop K a) := by
-- proof
  apply StatMech.Lattice.wei_rayCount_diff_singleton K c a a' hval hnp z

/--
[wei_windingWitness_transfer_diff_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingEarInduction.lean)
-/
@[path]
private lemma wei_windingWitness_transfer_diff_singleton_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {a : {e : Dart // IsBoundaryDart K e}}
  {a' : {e : Dart // IsBoundaryDart (K \ {c}) e}}
-- given
  (hval : a'.1 = a.1)
  (hnp : ∀ i, bpc_NotProbed c ((dartNext K)^[i] a.1))
  (hw : wei_WindingWitness (K \ {c}) a') :
-- imply
  wei_WindingWitness K a := by
-- proof
  apply StatMech.Lattice.wei_windingWitness_transfer_diff_singleton K c a a' hval hnp hw

/--
[wei_dartFace_trans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingEarInduction.lean)
-/
@[path]
private lemma wei_dartFace_trans_eq
  {w : Site 2}
  {e : Dart} :
-- imply
  dartFace (transDart w e) = dartFace e + w := by
-- proof
  apply StatMech.Lattice.wei_dartFace_trans w e

/--
[wei_rayEdge_trans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingEarInduction.lean)
-/
@[path]
private lemma wei_rayEdge_trans_eq
  {w z x y : Site 2} :
-- imply
  jec_rayEdge (z + w) s(x + w, y + w) ↔ jec_rayEdge z s(x, y) := by
-- proof
  apply StatMech.Lattice.wei_rayEdge_trans w z x y

/--
[wei_rayCount_trans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingEarInduction.lean)
-/
@[path]
private lemma wei_rayCount_trans_eq
  {K : Set (Site 2)}
  {w : Site 2}
  {a : {e : Dart // IsBoundaryDart K e}}
  {z : Site 2} :
-- imply
  jec_rayCount (z + w) (mpl_orbitLoop (transSet w K) (transSub K w a)) = jec_rayCount z (mpl_orbitLoop K a) := by
-- proof
  apply StatMech.Lattice.wei_rayCount_trans K w a z

/--
[wei_ucBase1_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingEarInduction.lean)
-/
@[path]
private lemma wei_ucBase1_edges_eq :
-- imply
  (mpl_orbitLoop unitCell ucBase1).edges = [s((![0, -1] : Site 2), ![-1, -1]), s((![-1, -1] : Site 2), ![-1, 0]), s((![-1, 0] : Site 2), ![0, 0]), s((![0, 0] : Site 2), ![0, -1])] := by
-- proof
  apply StatMech.Lattice.wei_ucBase1_edges

/--
[wei_ucBase2_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingEarInduction.lean)
-/
@[path]
private lemma wei_ucBase2_edges_eq :
-- imply
  (mpl_orbitLoop unitCell ucBase2).edges = [s((![-1, -1] : Site 2), ![-1, 0]), s((![-1, 0] : Site 2), ![0, 0]), s((![0, 0] : Site 2), ![0, -1]), s((![0, -1] : Site 2), ![-1, -1])] := by
-- proof
  apply StatMech.Lattice.wei_ucBase2_edges

/--
[wei_ucBase3_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingEarInduction.lean)
-/
@[path]
private lemma wei_ucBase3_edges_eq :
-- imply
  (mpl_orbitLoop unitCell ucBase3).edges = [s((![-1, 0] : Site 2), ![0, 0]), s((![0, 0] : Site 2), ![0, -1]), s((![0, -1] : Site 2), ![-1, -1]), s((![-1, -1] : Site 2), ![-1, 0])] := by
-- proof
  apply StatMech.Lattice.wei_ucBase3_edges

/--
[wei_unitCell_basepoint_rayCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingEarInduction.lean)
-/
@[path]
private lemma wei_unitCell_basepoint_rayCount_eq
  {b : {e : Dart // IsBoundaryDart unitCell e}}
-- given
  (hb : b.1 = ucDart0 ∨ b.1 = ucDart1 ∨ b.1 = ucDart2 ∨ b.1 = ucDart3) :
-- imply
  jec_rayCount (![0, 0] : Site 2) (mpl_orbitLoop unitCell b) = 1 := by
-- proof
  apply StatMech.Lattice.wei_unitCell_basepoint_rayCount b hb

/--
[wei_singleton_windingWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingEarInduction.lean)
-/
@[path]
private lemma wei_singleton_windingWitness_eq
  {v : Site 2}
  {a : {e : Dart // IsBoundaryDart ({v} : Set (Site 2)) e}} :
-- imply
  wei_WindingWitness ({v} : Set (Site 2)) a := by
-- proof
  apply StatMech.Lattice.wei_singleton_windingWitness v a

/--
[wei_windingWitness_of_descent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingEarInduction.lean)
-/
@[path]
private lemma wei_windingWitness_of_descent_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hres : wei_WindingSaturatingWitness)
  (hK : K.Finite)
  (hne : K.Nonempty) :
-- imply
  wei_WindingWitness K a := by
-- proof
  apply StatMech.Lattice.wei_windingWitness_of_descent hres K hK hne a

/--
[wei_starHull_windingWitness_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingEarInduction.lean)
-/
@[path]
private lemma wei_starHull_windingWitness_of_residue_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
-- given
  (hres : wei_WindingSaturatingWitness)
  (hSK : (ndt_StarHull K).Finite)
  (hne : (ndt_StarHull K).Nonempty) :
-- imply
  wei_WindingWitness (ndt_StarHull K) a := by
-- proof
  apply StatMech.Lattice.wei_starHull_windingWitness_of_residue hres K hSK hne a

/--
[wei_insideHalf_of_windingWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingEarInduction.lean)
-/
@[path]
private lemma wei_insideHalf_of_windingWitness_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {z0 : Site 2}
-- given
  (_hz0 : z0 ∈ K)
  (hodd0 : ¬ Even (jec_rayCount z0 (mpl_orbitLoop K a)))
  (hInt : ∀ z, z ∈ K → ∃ p : (hypercubicLattice 2).Walk z z0, (∀ w ∈ p.support, w ∉ (mpl_orbitLoop K a).support)) :
-- imply
  ∀ z, z ∈ K → ¬ Even (jec_rayCount z (mpl_orbitLoop K a)) := by
-- proof
  apply StatMech.Lattice.wei_insideHalf_of_windingWitness K a _hz0 hodd0 hInt

/--
[wei_starHull_bdEdgeMatch_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingEarInduction.lean)
-/
@[path]
private lemma wei_starHull_bdEdgeMatch_of_residue_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
-- given
  (hres : wei_WindingSaturatingWitness)
  (hSK : (ndt_StarHull K).Finite)
  (hne : (ndt_StarHull K).Nonempty)
  (hInt : ∀ z0, z0 ∈ ndt_StarHull K → ∀ z, z ∈ ndt_StarHull K → ∃ p : (hypercubicLattice 2).Walk z z0, (∀ w ∈ p.support, w ∉ (mpl_orbitLoop (ndt_StarHull K) a).support))
  (hout : ∀ z, z ∉ ndt_StarHull K → Even (jec_rayCount z (mpl_orbitLoop (ndt_StarHull K) a))) :
-- imply
  pww_BdEdgeMatch (ndt_StarHull K) (mpl_orbitLoop (ndt_StarHull K) a) := by
-- proof
  apply StatMech.Lattice.wei_starHull_bdEdgeMatch_of_residue hres K hSK hne a hInt hout

/--
[wei_unitCell_windingWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingEarInduction.lean)
-/
@[path]
private lemma wei_unitCell_windingWitness_eq :
-- imply
  wei_WindingWitness unitCell ucBase := by
-- proof
  apply StatMech.Lattice.wei_unitCell_windingWitness


-- created on 2026-10-23
