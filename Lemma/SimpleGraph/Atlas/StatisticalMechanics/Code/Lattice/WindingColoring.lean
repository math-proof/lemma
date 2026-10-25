import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.WindingColoring.Part6
open SimpleGraph Set StatMech StatMech.Lattice


/--
[wcl_flipCount_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingColoring.lean)
-/
@[path]
private lemma wcl_flipCount_nil_eq
  {x : Site 2}
-- given
  (flip : Site 2 → Site 2 → Prop) :
-- imply
  wcl_flipCount flip (SimpleGraph.Walk.nil : (hypercubicLattice 2).Walk x x) = 0 := by
-- proof
  apply StatMech.Lattice.wcl_flipCount_nil flip x

/--
[wcl_flipCount_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingColoring.lean)
-/
@[path]
private lemma wcl_flipCount_cons_eq
  {a b c : Site 2}
  {p : (hypercubicLattice 2).Walk b c}
-- given
  (flip : Site 2 → Site 2 → Prop)
  (hab : (hypercubicLattice 2).Adj a b) :
-- imply
  wcl_flipCount flip (Walk.cons hab p) = (if (flip a b ∨ flip b a) then 1 else 0) + wcl_flipCount flip p := by
-- proof
  apply StatMech.Lattice.wcl_flipCount_cons flip hab p

/--
[wcl_flipCount_append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingColoring.lean)
-/
@[path]
private lemma wcl_flipCount_append_eq
  {x y z : Site 2}
  {p : (hypercubicLattice 2).Walk x y}
  {q : (hypercubicLattice 2).Walk y z}
-- given
  (flip : Site 2 → Site 2 → Prop) :
-- imply
  wcl_flipCount flip (p.append q) = wcl_flipCount flip p + wcl_flipCount flip q := by
-- proof
  apply StatMech.Lattice.wcl_flipCount_append flip p q

/--
[wcl_flipCount_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingColoring.lean)
-/
@[path]
private lemma wcl_flipCount_reverse_eq
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (flip : Site 2 → Site 2 → Prop) :
-- imply
  wcl_flipCount flip w.reverse = wcl_flipCount flip w := by
-- proof
  apply StatMech.Lattice.wcl_flipCount_reverse flip w

/--
[wcl_flipCount_parity_eq_of_closedEven](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingColoring.lean)
-/
@[path]
private lemma wcl_flipCount_parity_eq_of_closedEven_eq
  {x y : Site 2}
  {w₁ w₂ : (hypercubicLattice 2).Walk x y}
-- given
  (flip : Site 2 → Site 2 → Prop)
  (hce : wcl_ClosedEven flip) :
-- imply
  wcl_flipCount flip w₁ % 2 = wcl_flipCount flip w₂ % 2 := by
-- proof
  apply StatMech.Lattice.wcl_flipCount_parity_eq_of_closedEven flip hce w₁ w₂

/--
[wcl_windingColoring_eq_of_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingColoring.lean)
-/
@[path]
private lemma wcl_windingColoring_eq_of_walk_eq
  {o : Site 2}
  {f : Site 2}
  {w : (hypercubicLattice 2).Walk o f}
-- given
  (flip : Site 2 → Site 2 → Prop)
  (hce : wcl_ClosedEven flip) :
-- imply
  wcl_windingColoring flip o f ↔ Odd (wcl_flipCount flip w) := by
-- proof
  apply StatMech.Lattice.wcl_windingColoring_eq_of_walk flip hce o w

/--
[wcl_windingColoring_compat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingColoring.lean)
-/
@[path]
private lemma wcl_windingColoring_compat_eq
  {o : Site 2}
  {a b : Site 2}
-- given
  (flip : Site 2 → Site 2 → Prop)
  (hsymm : wcl_SymmFlip flip)
  (hce : wcl_ClosedEven flip)
  (hab : (hypercubicLattice 2).Adj a b) :
-- imply
  (flip a b ↔ (wcl_windingColoring flip o a ↔ ¬ wcl_windingColoring flip o b)) := by
-- proof
  apply StatMech.Lattice.wcl_windingColoring_compat flip hsymm hce o hab

/--
[wcl_cutFlip_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingColoring.lean)
-/
@[path]
private lemma wcl_cutFlip_symm_eq
  {H : SimpleGraph (Site 2)}
  {f0 g0 : Site 2} :
-- imply
  wcl_SymmFlip (wcl_cutFlip H f0 g0) := by
-- proof
  apply StatMech.Lattice.wcl_cutFlip_symm H f0 g0

/--
[wcl_cutColoring_iff_compat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingColoring.lean)
-/
@[path]
private lemma wcl_cutColoring_iff_compat_eq
  {H : SimpleGraph (Site 2)}
  {f0 g0 : Site 2}
-- given
  (φ : Site 2 → Prop) :
-- imply
  whc_CutColoring H f0 g0 φ ↔ ∀ a b, (hypercubicLattice 2).Adj a b → (wcl_cutFlip H f0 g0 a b ↔ (φ a ↔ ¬ φ b)) := by
-- proof
  apply StatMech.Lattice.wcl_cutColoring_iff_compat H f0 g0 φ

/--
[wcl_windingColoring_isCutColoring](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingColoring.lean)
-/
@[path]
private lemma wcl_windingColoring_isCutColoring_eq
  {H : SimpleGraph (Site 2)}
  {f0 g0 : Site 2}
  {o : Site 2}
-- given
  (hce : wcl_ClosedEven (wcl_cutFlip H f0 g0)) :
-- imply
  whc_CutColoring H f0 g0 (wcl_windingColoring (wcl_cutFlip H f0 g0) o) := by
-- proof
  apply StatMech.Lattice.wcl_windingColoring_isCutColoring H f0 g0 hce o

/--
[wcl_flipCount_parity_of_compat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingColoring.lean)
-/
@[path]
private lemma wcl_flipCount_parity_of_compat_eq
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (flip : Site 2 → Site 2 → Prop)
  (φ : Site 2 → Prop)
  (hcompat : ∀ a b, (hypercubicLattice 2).Adj a b → (flip a b ↔ (φ a ↔ ¬ φ b))) :
-- imply
  Even (wcl_flipCount flip w) ↔ (φ x ↔ φ y) := by
-- proof
  apply StatMech.Lattice.wcl_flipCount_parity_of_compat flip φ hcompat w

/--
[wcl_closedEven_of_compat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingColoring.lean)
-/
@[path]
private lemma wcl_closedEven_of_compat_eq
-- given
  (flip : Site 2 → Site 2 → Prop)
  (φ : Site 2 → Prop)
  (hcompat : ∀ a b, (hypercubicLattice 2).Adj a b → (flip a b ↔ (φ a ↔ ¬ φ b))) :
-- imply
  wcl_ClosedEven flip := by
-- proof
  apply StatMech.Lattice.wcl_closedEven_of_compat flip φ hcompat

/--
[wcl_no_cutColoring_of_odd_loop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingColoring.lean)
-/
@[path]
private lemma wcl_no_cutColoring_of_odd_loop_eq
  {H : SimpleGraph (Site 2)}
  {f0 g0 : Site 2}
  {x : Site 2}
  {w : (hypercubicLattice 2).Walk x x}
-- given
  (hodd : ¬ Even (wcl_flipCount (wcl_cutFlip H f0 g0) w)) :
-- imply
  ¬ ∃ φ : Site 2 → Prop, whc_CutColoring H f0 g0 φ := by
-- proof
  apply StatMech.Lattice.wcl_no_cutColoring_of_odd_loop H f0 g0 w hodd

/--
[wcl_exists_cutColoring_iff_closedEven](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingColoring.lean)
-/
@[path]
private lemma wcl_exists_cutColoring_iff_closedEven_eq
  {H : SimpleGraph (Site 2)}
  {f0 g0 : Site 2} :
-- imply
  (∃ φ : Site 2 → Prop, whc_CutColoring H f0 g0 φ) ↔ wcl_ClosedEven (wcl_cutFlip H f0 g0) := by
-- proof
  apply StatMech.Lattice.wcl_exists_cutColoring_iff_closedEven H f0 g0

/--
[wcl_empty_instance_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingColoring.lean)
-/
@[path]
private lemma wcl_empty_instance_valid_eq :
-- imply
  (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(1:ℤ), 0] ∧ s(![(0:ℤ), 0], ![(1:ℤ), 0]) ∉ (⊥ : SimpleGraph (Site 2)).edgeSet ∧ (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(0:ℤ), -1] ∧ sharedPrimalEdge ![(0:ℤ), 0] ![(0:ℤ), -1] = s(![(0:ℤ), 0], ![(1:ℤ), 0]) := by
-- proof
  apply StatMech.Lattice.wcl_empty_instance_valid

/--
[wcl_cutFlip_bot_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingColoring.lean)
-/
@[path]
private lemma wcl_cutFlip_bot_iff_eq
  {a b : Site 2} :
-- imply
  wcl_cutFlip (⊥ : SimpleGraph (Site 2)) ![(0:ℤ), 0] ![(0:ℤ), -1] a b ↔ s(a, b) = s(![(0:ℤ), 0], ![(0:ℤ), -1]) := by
-- proof
  apply StatMech.Lattice.wcl_cutFlip_bot_iff a b

/--
[wcl_squareLoop_flipCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingColoring.lean)
-/
@[path]
private lemma wcl_squareLoop_flipCount_eq :
-- imply
  wcl_flipCount (wcl_cutFlip (⊥ : SimpleGraph (Site 2)) ![(0:ℤ), 0] ![(0:ℤ), -1]) wcl_squareLoop = 1 := by
-- proof
  apply StatMech.Lattice.wcl_squareLoop_flipCount

/--
[wcl_whitneyColoringResidue_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingColoring.lean)
-/
@[path]
private lemma wcl_whitneyColoringResidue_false_eq :
-- imply
  ¬ whc_WhitneyColoringResidue := by
-- proof
  apply StatMech.Lattice.wcl_whitneyColoringResidue_false

/--
[wcl_faceRegion_bot_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingColoring.lean)
-/
@[path]
private lemma wcl_faceRegion_bot_adj_eq
  {a b : Site 2} :
-- imply
  (whb_faceRegion (⊥ : SimpleGraph (Site 2))).Adj a b ↔ (hypercubicLattice 2).Adj a b := by
-- proof
  apply StatMech.Lattice.wcl_faceRegion_bot_adj a b

/--
[wcl_faceRegion_bot_reconnect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingColoring.lean)
-/
@[path]
private lemma wcl_faceRegion_bot_reconnect_eq :
-- imply
  ((whb_faceRegion (⊥ : SimpleGraph (Site 2))).deleteEdges {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] := by
-- proof
  apply StatMech.Lattice.wcl_faceRegion_bot_reconnect

/--
[wcl_deleted_separated_of_closedEven](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingColoring.lean)
-/
@[path]
private lemma wcl_deleted_separated_of_closedEven_eq
  {H : SimpleGraph (Site 2)}
  {f0 g0 : Site 2}
-- given
  (hfg : (hypercubicLattice 2).Adj f0 g0)
  (hce : wcl_ClosedEven (wcl_cutFlip H f0 g0)) :
-- imply
  ¬ ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 g0 := by
-- proof
  apply StatMech.Lattice.wcl_deleted_separated_of_closedEven H hfg hce

/--
[wcl_correctColoringResidue_holds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingColoring.lean)
-/
@[path]
private lemma wcl_correctColoringResidue_holds_eq :
-- imply
  wcl_CorrectColoringResidue := by
-- proof
  apply StatMech.Lattice.wcl_correctColoringResidue_holds

/--
[wcl_witness_closedEven](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingColoring.lean)
-/
@[path]
private lemma wcl_witness_closedEven_eq :
-- imply
  wcl_ClosedEven (wcl_cutFlip whc_Htest ![(0:ℤ), 0] ![(0:ℤ), -1]) := by
-- proof
  apply StatMech.Lattice.wcl_witness_closedEven

/--
[wcl_witness_residue_fires](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingColoring.lean)
-/
@[path]
private lemma wcl_witness_residue_fires_eq :
-- imply
  ∃ φ : Site 2 → Prop, whc_CutColoring whc_Htest ![(0:ℤ), 0] ![(0:ℤ), -1] φ ∧ ¬ (φ ![(0:ℤ), 0] ↔ φ ![(0:ℤ), -1]) ∧ ¬ ((whb_faceRegion whc_Htest).deleteEdges {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] := by
-- proof
  apply StatMech.Lattice.wcl_witness_residue_fires

/--
[wcl_whitney_forward_of_closedEven](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingColoring.lean)
-/
@[path]
private lemma wcl_whitney_forward_of_closedEven_eq
  {H : SimpleGraph (Site 2)}
  {p q f0 g0 : Site 2}
-- given
  (_hpq : (hypercubicLattice 2).Adj p q)
  (_hnpq : s(p, q) ∉ H.edgeSet)
  (hfg : (hypercubicLattice 2).Adj f0 g0)
  (_hshared : sharedPrimalEdge f0 g0 = s(p, q))
  (hce : wcl_ClosedEven (wcl_cutFlip H f0 g0)) :
-- imply
  ¬ ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 g0 := by
-- proof
  apply StatMech.Lattice.wcl_whitney_forward_of_closedEven H p q f0 g0 _hpq _hnpq hfg _hshared hce


-- created on 2026-10-23
