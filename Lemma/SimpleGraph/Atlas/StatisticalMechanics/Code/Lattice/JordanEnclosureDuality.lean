import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality.Part4
open SimpleGraph Set StatMech StatMech.Lattice


/--
[jed_mem_cutSet_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosureDuality.lean)
-/
@[path]
private lemma jed_mem_cutSet_iff_eq
  {c d : Site 2}
-- given
  (T : Site 2 → Prop)
  (hcd : (hypercubicLattice 2).Adj c d) :
-- imply
  sharedPrimalEdge c d ∈ jed_cutSet T ↔ (T c ↔ ¬ T d) := by
-- proof
  apply StatMech.Lattice.jed_mem_cutSet_iff T hcd

/--
[jed_sh_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosureDuality.lean)
-/
@[path]
private lemma jed_sh_right_eq
  {x y : ℤ} :
-- imply
  sharedPrimalEdge ![x, y] ![x, y - 1] = s(![x, y], ![x + 1, y]) := by
-- proof
  apply StatMech.Lattice.jed_sh_right x y

/--
[jed_sh_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosureDuality.lean)
-/
@[path]
private lemma jed_sh_left_eq
  {x y : ℤ} :
-- imply
  sharedPrimalEdge ![x - 1, y] ![x - 1, y - 1] = s(![x - 1, y], ![x, y]) := by
-- proof
  apply StatMech.Lattice.jed_sh_left x y

/--
[jed_sh_up](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosureDuality.lean)
-/
@[path]
private lemma jed_sh_up_eq
  {x y : ℤ} :
-- imply
  sharedPrimalEdge ![x, y] ![x - 1, y] = s(![x, y], ![x, y + 1]) := by
-- proof
  apply StatMech.Lattice.jed_sh_up x y

/--
[jed_sh_down](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosureDuality.lean)
-/
@[path]
private lemma jed_sh_down_eq
  {x y : ℤ} :
-- imply
  sharedPrimalEdge ![x, y - 1] ![x - 1, y - 1] = s(![x, y - 1], ![x, y]) := by
-- proof
  apply StatMech.Lattice.jed_sh_down x y

/--
[jed_cutSet_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosureDuality.lean)
-/
@[path]
private lemma jed_cutSet_even_eq
  {v : Site 2}
-- given
  (T : Site 2 → Prop) :
-- imply
  Even (jce_degree (jed_cutSet T) v) := by
-- proof
  apply StatMech.Lattice.jed_cutSet_even T v

/--
[jed_primalGraph_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosureDuality.lean)
-/
@[path]
private lemma jed_primalGraph_adj_eq
  {E : Set (Sym2 (Site 2))}
  {u w : Site 2} :
-- imply
  (jed_primalGraph E).Adj u w ↔ (hypercubicLattice 2).Adj u w ∧ s(u, w) ∈ E := by
-- proof
  apply StatMech.Lattice.jed_primalGraph_adj E u w

/--
[jed_primalGraph_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosureDuality.lean)
-/
@[path]
private lemma jed_primalGraph_le_eq
  {E : Set (Sym2 (Site 2))} :
-- imply
  jed_primalGraph E ≤ hypercubicLattice 2 := by
-- proof
  apply StatMech.Lattice.jed_primalGraph_le E

/--
[jed_primalGraph_edgeSet_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosureDuality.lean)
-/
@[path]
private lemma jed_primalGraph_edgeSet_subset_eq
  {E : Set (Sym2 (Site 2))} :
-- imply
  (jed_primalGraph E).edgeSet ⊆ E := by
-- proof
  apply StatMech.Lattice.jed_primalGraph_edgeSet_subset E

/--
[jed_nbr_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosureDuality.lean)
-/
@[path]
private lemma jed_nbr_adj_eq
  {v : Site 2}
  {i : Fin 4} :
-- imply
  (hypercubicLattice 2).Adj v (jce_nbr v i) := by
-- proof
  apply StatMech.Lattice.jed_nbr_adj v i

/--
[jed_jce_degree_primalGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosureDuality.lean)
-/
@[path]
private lemma jed_jce_degree_primalGraph_eq
  {E : Set (Sym2 (Site 2))}
  {v : Site 2} :
-- imply
  jce_degree (jed_primalGraph E).edgeSet v = jce_degree E v := by
-- proof
  apply StatMech.Lattice.jed_jce_degree_primalGraph E v

/--
[jed_degree_primalGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosureDuality.lean)
-/
@[path]
private lemma jed_degree_primalGraph_eq
  {E : Set (Sym2 (Site 2))}
  {v : Site 2} :
-- imply
  (jed_primalGraph E).degree v = jce_degree E v := by
-- proof
  apply StatMech.Lattice.jed_degree_primalGraph E v

/--
[jed_wall_mem_cutSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosureDuality.lean)
-/
@[path]
private lemma jed_wall_mem_cutSet_eq
  {H : SimpleGraph (Site 2)}
  {f0 g0 : Site 2}
-- given
  (hfg : (hypercubicLattice 2).Adj f0 g0)
  (hsep : ¬ ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 g0) :
-- imply
  sharedPrimalEdge f0 g0 ∈ jed_cutSet (fun v => ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 v) := by
-- proof
  apply StatMech.Lattice.jed_wall_mem_cutSet H f0 g0 hfg hsep

/--
[jed_cutSet_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosureDuality.lean)
-/
@[path]
private lemma jed_cutSet_subset_eq
  {H : SimpleGraph (Site 2)}
  {f0 g0 : Site 2}
-- given
  (hfg : (hypercubicLattice 2).Adj f0 g0) :
-- imply
  jed_cutSet (fun v => ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 v) ⊆ insert (sharedPrimalEdge f0 g0) H.edgeSet := by
-- proof
  apply StatMech.Lattice.jed_cutSet_subset H f0 g0 hfg

/--
[jed_cutMinusWall_degree_data](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosureDuality.lean)
-/
@[path]
private lemma jed_cutMinusWall_degree_data_eq
  {H : SimpleGraph (Site 2)}
  {p q f0 g0 : Site 2}
-- given
  (hpq : (hypercubicLattice 2).Adj p q)
  (hfg : (hypercubicLattice 2).Adj f0 g0)
  (hshared : sharedPrimalEdge f0 g0 = s(p, q))
  (hsep : ¬ ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 g0) :
-- imply
  Odd (jce_degree (jed_cutSet (fun v => ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 v) \ {s(p, q)}) p) ∧ Odd (jce_degree (jed_cutSet (fun v => ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 v) \ {s(p, q)}) q) ∧ (∀ v, v ≠ p → v ≠ q → Even (jce_degree (jed_cutSet (fun v => ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 v) \ {s(p, q)}) v)) := by
-- proof
  apply StatMech.Lattice.jed_cutMinusWall_degree_data H p q f0 g0 hpq hfg hshared hsep

/--
[jed_reachable_of_separated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosureDuality.lean)
-/
@[path]
private lemma jed_reachable_of_separated_eq
  {H : SimpleGraph (Site 2)}
  {p q f0 g0 : Site 2}
-- given
  (hfin : H.edgeSet.Finite)
  (hpq : (hypercubicLattice 2).Adj p q)
  (_hnpq : s(p, q) ∉ H.edgeSet)
  (hfg : (hypercubicLattice 2).Adj f0 g0)
  (hshared : sharedPrimalEdge f0 g0 = s(p, q))
  (hsep : ¬ ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 g0) :
-- imply
  H.Reachable p q := by
-- proof
  apply StatMech.Lattice.jed_reachable_of_separated H hfin p q f0 g0 hpq _hnpq hfg hshared hsep

/--
[jed_finiteKeepReconnect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosureDuality.lean)
-/
@[path]
private lemma jed_finiteKeepReconnect_eq :
-- imply
  jkr_FiniteKeepReconnectResidue := by
-- proof
  apply StatMech.Lattice.jed_finiteKeepReconnect

/--
[jed_sameComponentResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosureDuality.lean)
-/
@[path]
private lemma jed_sameComponentResidue_eq :
-- imply
  jfd_SameComponentResidue := by
-- proof
  apply StatMech.Lattice.jed_sameComponentResidue

/--
[jed_keepResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosureDuality.lean)
-/
@[path]
private lemma jed_keepResidue_eq
  {P : PlanarZ2Subgraph} :
-- imply
  jwc_KeepResidue P := by
-- proof
  apply StatMech.Lattice.jed_keepResidue P

/--
[jed_faithfulDiscreteJordan](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosureDuality.lean)
-/
@[path]
private lemma jed_faithfulDiscreteJordan_eq
  {P : PlanarZ2Subgraph} :
-- imply
  whc_FaithfulDiscreteJordan P := by
-- proof
  apply StatMech.Lattice.jed_faithfulDiscreteJordan P

/--
[jed_not_reachable_of_isolated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosureDuality.lean)
-/
@[path]
private lemma jed_not_reachable_of_isolated_eq
  {H : SimpleGraph (Site 2)}
  {u v : Site 2}
-- given
  (hiso : ∀ w, ¬ H.Adj u w)
  (hne : u ≠ v) :
-- imply
  ¬ H.Reachable u v := by
-- proof
  apply StatMech.Lattice.jed_not_reachable_of_isolated H u v hiso hne

/--
[jed_boxH_iso_p](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosureDuality.lean)
-/
@[path]
private lemma jed_boxH_iso_p_eq
  {w : Site 2} :
-- imply
  ¬ jed_boxH.Adj ![(0:ℤ), 0] w := by
-- proof
  apply StatMech.Lattice.jed_boxH_iso_p w

/--
[jed_boxH_iso_q](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosureDuality.lean)
-/
@[path]
private lemma jed_boxH_iso_q_eq
  {w : Site 2} :
-- imply
  ¬ jed_boxH.Adj ![(1:ℤ), 0] w := by
-- proof
  apply StatMech.Lattice.jed_boxH_iso_q w

/--
[jed_boxH_edgeSet_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosureDuality.lean)
-/
@[path]
private lemma jed_boxH_edgeSet_finite_eq :
-- imply
  jed_boxH.edgeSet.Finite := by
-- proof
  apply StatMech.Lattice.jed_boxH_edgeSet_finite

/--
[jed_enclosingBox_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosureDuality.lean)
-/
@[path]
private lemma jed_enclosingBox_witness_eq :
-- imply
  (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(1:ℤ), 0] ∧ s(![(0:ℤ), 0], ![(1:ℤ), 0]) ∉ jed_boxH.edgeSet ∧ (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(0:ℤ), -1] ∧ sharedPrimalEdge ![(0:ℤ), 0] ![(0:ℤ), -1] = s(![(0:ℤ), 0], ![(1:ℤ), 0]) ∧ ¬ jed_boxH.Reachable ![(0:ℤ), 0] ![(1:ℤ), 0] ∧ ((whb_faceRegion jed_boxH).deleteEdges {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] := by
-- proof
  apply StatMech.Lattice.jed_enclosingBox_witness

/--
[jed_witnesses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosureDuality.lean)
-/
@[path]
private lemma jed_witnesses_eq :
-- imply
  ((whb_faceRegion (⊥ : SimpleGraph (Site 2))).deleteEdges {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] ∧ ((whb_faceRegion (jei_pushGraph jbc_Pce ⊥)).deleteEdges {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] ∧ ((whb_faceRegion (jei_pushGraph jkd_ringP ⊥)).deleteEdges {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] ∧ ((whb_faceRegion jed_boxH).deleteEdges {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] ∧ jkr_lineH.edgeSet.Infinite := by
-- proof
  apply StatMech.Lattice.jed_witnesses

/--
[jed_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEnclosureDuality.lean)
-/
@[path]
private lemma jed_status_eq :
-- imply
  (∀ (T : Site 2 → Prop) (v : Site 2), Even (jce_degree (jed_cutSet T) v)) ∧ jkr_FiniteKeepReconnectResidue ∧ jfd_SameComponentResidue ∧ (∀ P : PlanarZ2Subgraph, whc_FaithfulDiscreteJordan P) := by
-- proof
  apply StatMech.Lattice.jed_status


-- created on 2026-10-23
