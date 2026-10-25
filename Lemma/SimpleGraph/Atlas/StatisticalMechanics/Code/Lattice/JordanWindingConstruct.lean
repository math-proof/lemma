import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.JordanWindingConstruct.Part3
open SimpleGraph Set StatMech StatMech.Lattice


/--
[jwn_marked_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanWindingConstruct.lean)
-/
@[path]
private lemma jwn_marked_iff_eq
  {H : SimpleGraph (Site 2)}
  {f0 g0 a b : Site 2} :
-- imply
  (wcl_cutFlip H f0 g0 a b ∨ wcl_cutFlip H f0 g0 b a) ↔ wcl_cutFlip H f0 g0 a b := by
-- proof
  apply StatMech.Lattice.jwn_marked_iff H f0 g0 a b

/--
[jwn_cutColoring_closedEven](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanWindingConstruct.lean)
-/
@[path]
private lemma jwn_cutColoring_closedEven_eq
  {H : SimpleGraph (Site 2)}
  {f0 g0 : Site 2}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (φ : Site 2 → Prop)
  (hcut : whc_CutColoring H f0 g0 φ) :
-- imply
  Even (jwn_cutCount H f0 g0 w) ↔ (φ x ↔ φ y) := by
-- proof
  apply StatMech.Lattice.jwn_cutColoring_closedEven H f0 g0 φ hcut w

/--
[jwn_no_cutColoring_of_oddLoop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanWindingConstruct.lean)
-/
@[path]
private lemma jwn_no_cutColoring_of_oddLoop_eq
  {H : SimpleGraph (Site 2)}
  {f0 g0 : Site 2}
  {x : Site 2}
  {w : (hypercubicLattice 2).Walk x x}
-- given
  (hodd : ¬ Even (jwn_cutCount H f0 g0 w)) :
-- imply
  ¬ ∃ φ : Site 2 → Prop, whc_CutColoring H f0 g0 φ := by
-- proof
  apply StatMech.Lattice.jwn_no_cutColoring_of_oddLoop H f0 g0 w hodd

/--
[jwn_cutFlip_bot_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanWindingConstruct.lean)
-/
@[path]
private lemma jwn_cutFlip_bot_iff_eq
  {a b : Site 2} :
-- imply
  wcl_cutFlip (⊥ : SimpleGraph (Site 2)) ![(0:ℤ), 0] ![(0:ℤ), -1] a b ↔ s(a, b) = s(![(0:ℤ), 0], ![(0:ℤ), -1]) := by
-- proof
  apply StatMech.Lattice.jwn_cutFlip_bot_iff a b

/--
[jwn_squareLoop_cutCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanWindingConstruct.lean)
-/
@[path]
private lemma jwn_squareLoop_cutCount_eq :
-- imply
  jwn_cutCount (⊥ : SimpleGraph (Site 2)) ![(0:ℤ), 0] ![(0:ℤ), -1] jwn_squareLoop = 1 := by
-- proof
  apply StatMech.Lattice.jwn_squareLoop_cutCount

/--
[jwn_no_cutColoring_bot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanWindingConstruct.lean)
-/
@[path]
private lemma jwn_no_cutColoring_bot_eq :
-- imply
  ¬ ∃ φ : Site 2 → Prop, whc_CutColoring (⊥ : SimpleGraph (Site 2)) ![(0:ℤ), 0] ![(0:ℤ), -1] φ := by
-- proof
  apply StatMech.Lattice.jwn_no_cutColoring_bot

/--
[jwn_bot_instance_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanWindingConstruct.lean)
-/
@[path]
private lemma jwn_bot_instance_valid_eq :
-- imply
  (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(1:ℤ), 0] ∧ s(![(0:ℤ), 0], ![(1:ℤ), 0]) ∉ (⊥ : SimpleGraph (Site 2)).edgeSet ∧ (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(0:ℤ), -1] ∧ sharedPrimalEdge ![(0:ℤ), 0] ![(0:ℤ), -1] = s(![(0:ℤ), 0], ![(1:ℤ), 0]) := by
-- proof
  apply StatMech.Lattice.jwn_bot_instance_valid

/--
[jwn_whitneyColoringResidue_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanWindingConstruct.lean)
-/
@[path]
private lemma jwn_whitneyColoringResidue_false_eq :
-- imply
  ¬ whc_WhitneyColoringResidue := by
-- proof
  apply StatMech.Lattice.jwn_whitneyColoringResidue_false

/--
[jwn_bot_reconnect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanWindingConstruct.lean)
-/
@[path]
private lemma jwn_bot_reconnect_eq :
-- imply
  ((whb_faceRegion (⊥ : SimpleGraph (Site 2))).deleteEdges {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] := by
-- proof
  apply StatMech.Lattice.jwn_bot_reconnect

/--
[jwn_cutColoring_of_closedEven](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanWindingConstruct.lean)
-/
@[path]
private lemma jwn_cutColoring_of_closedEven_eq
  {H : SimpleGraph (Site 2)}
  {f0 g0 : Site 2}
-- given
  (hce : wcl_ClosedEven (wcl_cutFlip H f0 g0)) :
-- imply
  ∃ φ : Site 2 → Prop, whc_CutColoring H f0 g0 φ := by
-- proof
  apply StatMech.Lattice.jwn_cutColoring_of_closedEven H f0 g0 hce

/--
[jwn_cutColoring_forces_closedEven](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanWindingConstruct.lean)
-/
@[path]
private lemma jwn_cutColoring_forces_closedEven_eq
  {H : SimpleGraph (Site 2)}
  {f0 g0 : Site 2}
-- given
  (φ : Site 2 → Prop)
  (hcut : whc_CutColoring H f0 g0 φ) :
-- imply
  wcl_ClosedEven (wcl_cutFlip H f0 g0) := by
-- proof
  apply StatMech.Lattice.jwn_cutColoring_forces_closedEven H f0 g0 φ hcut

/--
[jwn_keepReconnect_of_whitneyColoring](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanWindingConstruct.lean)
-/
@[path]
private lemma jwn_keepReconnect_of_whitneyColoring_eq
-- given
  (hres : whc_WhitneyColoringResidue) :
-- imply
  jwn_KeepReconnectResidue := by
-- proof
  apply StatMech.Lattice.jwn_keepReconnect_of_whitneyColoring hres

/--
[jwn_witness_square](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanWindingConstruct.lean)
-/
@[path]
private lemma jwn_witness_square_eq :
-- imply
  (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(1:ℤ), 0] ∧ s(![(0:ℤ), 0], ![(1:ℤ), 0]) ∉ (⊥ : SimpleGraph (Site 2)).edgeSet ∧ (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(0:ℤ), -1] ∧ sharedPrimalEdge ![(0:ℤ), 0] ![(0:ℤ), -1] = s(![(0:ℤ), 0], ![(1:ℤ), 0]) ∧ ¬ (⊥ : SimpleGraph (Site 2)).Reachable ![(0:ℤ), 0] ![(1:ℤ), 0] ∧ ((whb_faceRegion (⊥ : SimpleGraph (Site 2))).deleteEdges {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] := by
-- proof
  apply StatMech.Lattice.jwn_witness_square

/--
[jwn_witness_ring](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanWindingConstruct.lean)
-/
@[path]
private lemma jwn_witness_ring_eq :
-- imply
  jkd_ringP.G.Adj jkd_r0 jkd_r1 ∧ s(jkd_ringP.emb jkd_r0, jkd_ringP.emb jkd_r1) ∉ (jei_pushGraph jkd_ringP ⊥).edgeSet ∧ (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(0:ℤ), -1] ∧ sharedPrimalEdge ![(0:ℤ), 0] ![(0:ℤ), -1] = s(jkd_ringP.emb jkd_r0, jkd_ringP.emb jkd_r1) ∧ ¬ (jei_pushGraph jkd_ringP ⊥).Reachable (jkd_ringP.emb jkd_r0) (jkd_ringP.emb jkd_r1) ∧ ((whb_faceRegion (jei_pushGraph jkd_ringP ⊥)).deleteEdges {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] := by
-- proof
  apply StatMech.Lattice.jwn_witness_ring

/--
[jwn_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanWindingConstruct.lean)
-/
@[path]
private lemma jwn_status_eq :
-- imply
  ¬ whc_WhitneyColoringResidue ∧ ((whb_faceRegion (⊥ : SimpleGraph (Site 2))).deleteEdges {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] ∧ (whc_WhitneyColoringResidue → jwn_KeepReconnectResidue) := by
-- proof
  apply StatMech.Lattice.jwn_status


-- created on 2026-10-23
