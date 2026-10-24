import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.BdEdgeMatchClose
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[bemc_bdEdge_imp_on_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BdEdgeMatchClose.lean)
-/
@[path]
private lemma bemc_bdEdge_imp_on_support_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {u v : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj u v)
  (hbd : bdEdge (jec_leftRegion Vc) s(u, v)) :
-- imply
  u ∈ Vc.support ∨ v ∈ Vc.support := by
-- proof
  apply StatMech.Lattice.bemc_bdEdge_imp_on_support Vc hadj hbd

/--
[bemc_off_support_not_bdEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BdEdgeMatchClose.lean)
-/
@[path]
private lemma bemc_off_support_not_bdEdge_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {u v : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj u v)
  (hu : u ∉ Vc.support)
  (hv : v ∉ Vc.support) :
-- imply
  ¬ bdEdge (jec_leftRegion Vc) s(u, v) := by
-- proof
  apply StatMech.Lattice.bemc_off_support_not_bdEdge Vc hadj hu hv

/--
[bemc_bdEdge_iff_membership_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BdEdgeMatchClose.lean)
-/
@[path]
private lemma bemc_bdEdge_iff_membership_flip_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {u v : Site 2} :
-- imply
  bdEdge (jec_leftRegion Vc) s(u, v) ↔ (u ∈ jec_leftRegion Vc ↔ v ∉ jec_leftRegion Vc) := by
-- proof
  apply StatMech.Lattice.bemc_bdEdge_iff_membership_flip Vc

/--
[bemc_bdEdge_iff_support_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BdEdgeMatchClose.lean)
-/
@[path]
private lemma bemc_bdEdge_iff_support_flip_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {u v : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj u v) :
-- imply
  bdEdge (jec_leftRegion Vc) s(u, v) ↔ ((u ∈ jec_leftRegion Vc ↔ v ∉ jec_leftRegion Vc) ∧ (u ∈ Vc.support ∨ v ∈ Vc.support)) := by
-- proof
  apply StatMech.Lattice.bemc_bdEdge_iff_support_flip Vc hadj

/--
[bemc_leftRegion_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BdEdgeMatchClose.lean)
-/
@[path]
private lemma bemc_leftRegion_finite_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R) :
-- imply
  (jec_leftRegion Vc).Finite := by
-- proof
  apply StatMech.Lattice.bemc_leftRegion_finite Vc R hsupp

/--
[bemc_compl_leftRegion_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BdEdgeMatchClose.lean)
-/
@[path]
private lemma bemc_compl_leftRegion_infinite_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R) :
-- imply
  (jec_leftRegion Vc)ᶜ.Infinite := by
-- proof
  apply StatMech.Lattice.bemc_compl_leftRegion_infinite Vc R hsupp

/--
[bemc_orientation_selected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BdEdgeMatchClose.lean)
-/
@[path]
private lemma bemc_orientation_selected_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {K : Set (Site 2)}
-- given
  (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R)
  (hKfin : K.Finite)
  (hid : K = jec_leftRegion Vc ∨ K = (jec_leftRegion Vc)ᶜ) :
-- imply
  K = jec_leftRegion Vc := by
-- proof
  apply StatMech.Lattice.bemc_orientation_selected Vc R hsupp hKfin hid

/--
[bemc_leftRegion_eq_of_bdEdgeMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BdEdgeMatchClose.lean)
-/
@[path]
private lemma bemc_leftRegion_eq_of_bdEdgeMatch_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {K : Set (Site 2)}
-- given
  (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R)
  (hKfin : K.Finite)
  (hmatch : pww_BdEdgeMatch K Vc) :
-- imply
  K = jec_leftRegion Vc := by
-- proof
  apply StatMech.Lattice.bemc_leftRegion_eq_of_bdEdgeMatch Vc R hsupp hKfin hmatch

/--
[bemc_bdEdgeMatch_iff_leftRegion_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BdEdgeMatchClose.lean)
-/
@[path]
private lemma bemc_bdEdgeMatch_iff_leftRegion_eq_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
  {K : Set (Site 2)}
-- given
  (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R)
  (hKfin : K.Finite) :
-- imply
  pww_BdEdgeMatch K Vc ↔ K = jec_leftRegion Vc := by
-- proof
  apply StatMech.Lattice.bemc_bdEdgeMatch_iff_leftRegion_eq Vc R hsupp hKfin

/--
[bemc_dcd_windingRegion_orientation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BdEdgeMatchClose.lean)
-/
@[path]
private lemma bemc_dcd_windingRegion_orientation_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R) :
-- imply
  (jec_leftRegion Vc).Finite ∧ (jec_leftRegion Vc)ᶜ.Infinite ∧ (∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v → (bdEdge (jec_leftRegion Vc) s(u, v) → (u ∈ Vc.support ∨ v ∈ Vc.support)) ∧ (u ∉ Vc.support → v ∉ Vc.support → ¬ bdEdge (jec_leftRegion Vc) s(u, v))) := by
-- proof
  apply StatMech.Lattice.bemc_dcd_windingRegion_orientation Vc R hsupp

/--
[bemc_minimalLoop_orientation_selected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BdEdgeMatchClose.lean)
-/
@[path]
private lemma bemc_minimalLoop_orientation_selected_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {R : ℕ}
  {J : Set (Site 2)}
-- given
  (hsupp : ∀ p ∈ (mpl_orbitLoop K a).support, p ∈ box 2 R)
  (hJfin : J.Finite)
  (hid : J = jec_leftRegion (mpl_orbitLoop K a) ∨ J = (jec_leftRegion (mpl_orbitLoop K a))ᶜ) :
-- imply
  J = jec_leftRegion (mpl_orbitLoop K a) := by
-- proof
  apply StatMech.Lattice.bemc_minimalLoop_orientation_selected K a R hsupp hJfin hid

/--
[bemc_minimalLoop_leftRegion_eq_of_bdEdgeMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BdEdgeMatchClose.lean)
-/
@[path]
private lemma bemc_minimalLoop_leftRegion_eq_of_bdEdgeMatch_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {R : ℕ}
  {J : Set (Site 2)}
-- given
  (hsupp : ∀ p ∈ (mpl_orbitLoop K a).support, p ∈ box 2 R)
  (hJfin : J.Finite)
  (hmatch : pww_BdEdgeMatch J (mpl_orbitLoop K a)) :
-- imply
  J = jec_leftRegion (mpl_orbitLoop K a) := by
-- proof
  apply StatMech.Lattice.bemc_minimalLoop_leftRegion_eq_of_bdEdgeMatch K a R hsupp hJfin hmatch

/--
[bemc_minimalLoop_bdEdgeMatch_iff_leftRegion_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BdEdgeMatchClose.lean)
-/
@[path]
private lemma bemc_minimalLoop_bdEdgeMatch_iff_leftRegion_eq_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {R : ℕ}
  {J : Set (Site 2)}
-- given
  (hsupp : ∀ p ∈ (mpl_orbitLoop K a).support, p ∈ box 2 R)
  (hJfin : J.Finite) :
-- imply
  pww_BdEdgeMatch J (mpl_orbitLoop K a) ↔ J = jec_leftRegion (mpl_orbitLoop K a) := by
-- proof
  apply StatMech.Lattice.bemc_minimalLoop_bdEdgeMatch_iff_leftRegion_eq K a R hsupp hJfin

/--
[bemc_orientation_selected_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BdEdgeMatchClose.lean)
-/
@[path]
private lemma bemc_orientation_selected_self_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R) :
-- imply
  (jec_leftRegion Vc) = jec_leftRegion Vc := by
-- proof
  apply StatMech.Lattice.bemc_orientation_selected_self Vc R hsupp

/--
[bemc_bdEdgeMatch_self_collapses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/BdEdgeMatchClose.lean)
-/
@[path]
private lemma bemc_bdEdgeMatch_self_collapses_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {R : ℕ}
-- given
  (hsupp : ∀ p ∈ Vc.support, p ∈ box 2 R) :
-- imply
  (jec_leftRegion Vc) = jec_leftRegion Vc := by
-- proof
  apply StatMech.Lattice.bemc_bdEdgeMatch_self_collapses Vc R hsupp


-- created on 2026-10-23
