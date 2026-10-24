import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.JordanFiniteDetour
open SimpleGraph Set StatMech StatMech.Lattice


/--
[jfd_shared_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanFiniteDetour.lean)
-/
@[path]
private lemma jfd_shared_exterior_eq
  {R : ℕ}
  {a b : Site 2}
-- given
  (ha : a ∈ exterior 2 (R + 1))
  (hab : (hypercubicLattice 2).Adj a b) :
-- imply
  ∀ x ∈ sharedPrimalEdge a b, x ∈ exterior 2 R := by
-- proof
  apply StatMech.Lattice.jfd_shared_exterior R ha hab

/--
[jfd_not_edge_of_not_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanFiniteDetour.lean)
-/
@[path]
private lemma jfd_not_edge_of_not_support_eq
  {H : SimpleGraph (Site 2)}
  {u v : Site 2}
-- given
  (hu : u ∉ H.support) :
-- imply
  s(u, v) ∉ H.edgeSet := by
-- proof
  apply StatMech.Lattice.jfd_not_edge_of_not_support H hu

/--
[jfd_deleted_adj_of_exterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanFiniteDetour.lean)
-/
@[path]
private lemma jfd_deleted_adj_of_exterior_eq
  {H : SimpleGraph (Site 2)}
  {R : ℕ}
  {f0 g0 : Site 2}
  {a b : Site 2}
-- given
  (hHR : ∀ v ∈ H.support, v ∈ box 2 R)
  (hf0 : f0 ∈ box 2 R)
  (hg0 : g0 ∈ box 2 R)
  (ha : a ∈ exterior 2 (R + 1))
  (_hb : b ∈ exterior 2 (R + 1))
  (hab : (hypercubicLattice 2).Adj a b) :
-- imply
  ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Adj a b := by
-- proof
  apply StatMech.Lattice.jfd_deleted_adj_of_exterior H R f0 g0 hHR hf0 hg0 ha _hb hab

/--
[jfd_exterior_reachable_deleted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanFiniteDetour.lean)
-/
@[path]
private lemma jfd_exterior_reachable_deleted_eq
  {H : SimpleGraph (Site 2)}
  {R : ℕ}
  {f0 g0 : Site 2}
  {x y : Site 2}
-- given
  (hHR : ∀ v ∈ H.support, v ∈ box 2 R)
  (hf0 : f0 ∈ box 2 R)
  (hg0 : g0 ∈ box 2 R)
  (hx : x ∈ exterior 2 (R + 1))
  (hy : y ∈ exterior 2 (R + 1)) :
-- imply
  ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable x y := by
-- proof
  apply StatMech.Lattice.jfd_exterior_reachable_deleted H R f0 g0 hHR hf0 hg0 hx hy

/--
[jfd_reconnect_of_both_escape](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanFiniteDetour.lean)
-/
@[path]
private lemma jfd_reconnect_of_both_escape_eq
  {H : SimpleGraph (Site 2)}
  {R : ℕ}
  {f0 g0 : Site 2}
  {ef eg : Site 2}
-- given
  (hHR : ∀ v ∈ H.support, v ∈ box 2 R)
  (hf0 : f0 ∈ box 2 R)
  (hg0 : g0 ∈ box 2 R)
  (hef : ef ∈ exterior 2 (R + 1))
  (heg : eg ∈ exterior 2 (R + 1))
  (hfef : ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 ef)
  (hgeg : ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable g0 eg) :
-- imply
  ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 g0 := by
-- proof
  apply StatMech.Lattice.jfd_reconnect_of_both_escape H R f0 g0 hHR hf0 hg0 hef heg hfef hgeg

/--
[jfd_reconnect_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanFiniteDetour.lean)
-/
@[path]
private lemma jfd_reconnect_split_eq
  {H : SimpleGraph (Site 2)}
  {R : ℕ}
  {f0 g0 : Site 2}
-- given
  (hHR : ∀ v ∈ H.support, v ∈ box 2 R)
  (hf0 : f0 ∈ box 2 R)
  (hg0 : g0 ∈ box 2 R)
  (hcase : (∃ ef ∈ exterior 2 (R + 1), ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 ef) ∧ (∃ eg ∈ exterior 2 (R + 1), ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable g0 eg)) :
-- imply
  ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 g0 := by
-- proof
  apply StatMech.Lattice.jfd_reconnect_split H R f0 g0 hHR hf0 hg0 hcase

/--
[jfd_sameComponent_iff_finiteKeep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanFiniteDetour.lean)
-/
@[path]
private lemma jfd_sameComponent_iff_finiteKeep_eq :
-- imply
  jfd_SameComponentResidue ↔ jkr_FiniteKeepReconnectResidue := by
-- proof
  apply StatMech.Lattice.jfd_sameComponent_iff_finiteKeep

/--
[jfd_witnesses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanFiniteDetour.lean)
-/
@[path]
private lemma jfd_witnesses_eq :
-- imply
  ((whb_faceRegion (⊥ : SimpleGraph (Site 2))).deleteEdges {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] ∧ ((whb_faceRegion (jei_pushGraph jbc_Pce ⊥)).deleteEdges {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] ∧ ((whb_faceRegion (jei_pushGraph jkd_ringP ⊥)).deleteEdges {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] ∧ jkr_lineH.edgeSet.Infinite := by
-- proof
  apply StatMech.Lattice.jfd_witnesses

/--
[jfd_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanFiniteDetour.lean)
-/
@[path]
private lemma jfd_status_eq :
-- imply
  (∀ (H : SimpleGraph (Site 2)) (R : ℕ) (f0 g0 : Site 2), (∀ v ∈ H.support, v ∈ box 2 R) → f0 ∈ box 2 R → g0 ∈ box 2 R → ∀ {ef eg : Site 2}, ef ∈ exterior 2 (R + 1) → eg ∈ exterior 2 (R + 1) → ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 ef → ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable g0 eg → ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 g0) ∧ (jfd_SameComponentResidue ↔ jkr_FiniteKeepReconnectResidue) ∧ (jwn_KeepReconnectResidue → jkr_FiniteKeepReconnectResidue) := by
-- proof
  apply StatMech.Lattice.jfd_status


-- created on 2026-10-23
