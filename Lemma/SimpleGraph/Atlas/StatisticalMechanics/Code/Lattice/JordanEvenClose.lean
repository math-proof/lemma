import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenClose.Part5
open SimpleGraph Set StatMech StatMech.Lattice


/--
[jce_horizBelow_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenClose.lean)
-/
@[path]
private lemma jce_horizBelow_mk_eq
  {a b : ℤ}
  {x y : Site 2} :
-- imply
  jce_horizBelow a b s(x, y) ↔ (x 1 = y 1) ∧ (x 1 ≤ b) ∧ ((x 0 = a ∧ y 0 = a + 1) ∨ (x 0 = a + 1 ∧ y 0 = a)) := by
-- proof
  apply StatMech.Lattice.jce_horizBelow_mk a b x y

/--
[jce_phi_def](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenClose.lean)
-/
@[path]
private lemma jce_phi_def_eq
  {E : Finset (Sym2 (Site 2))}
  {f : Site 2} :
-- imply
  jce_phi E f ↔ Odd (E.filter (fun e => jce_horizBelow (f 0) (f 1) e)).card := by
-- proof
  apply StatMech.Lattice.jce_phi_def E f

/--
[jce_site_eq_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenClose.lean)
-/
@[path]
private lemma jce_site_eq_iff_eq
  {x : Site 2}
  {c d : ℤ} :
-- imply
  x = ![c, d] ↔ x 0 = c ∧ x 1 = d := by
-- proof
  apply StatMech.Lattice.jce_site_eq_iff x c d

/--
[jce_horizBelow_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenClose.lean)
-/
@[path]
private lemma jce_horizBelow_succ_eq
  {a b : ℤ}
  {e : Sym2 (Site 2)} :
-- imply
  jce_horizBelow a (b + 1) e ↔ (jce_horizBelow a b e ∨ e = s(![a, b + 1], ![a + 1, b + 1])) := by
-- proof
  apply StatMech.Lattice.jce_horizBelow_succ a b e

/--
[jce_succEdge_not_below](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenClose.lean)
-/
@[path]
private lemma jce_succEdge_not_below_eq
  {a b : ℤ} :
-- imply
  ¬ jce_horizBelow a b s(![a, b + 1], ![a + 1, b + 1]) := by
-- proof
  apply StatMech.Lattice.jce_succEdge_not_below a b

/--
[jce_filter_succ_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenClose.lean)
-/
@[path]
private lemma jce_filter_succ_card_eq
  {E : Finset (Sym2 (Site 2))}
  {a b : ℤ} :
-- imply
  (E.filter (fun e => jce_horizBelow a (b + 1) e)).card = (E.filter (fun e => jce_horizBelow a b e)).card + (if s(![a, b + 1], ![a + 1, b + 1]) ∈ E then 1 else 0) := by
-- proof
  apply StatMech.Lattice.jce_filter_succ_card E a b

/--
[jce_phi_topStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenClose.lean)
-/
@[path]
private lemma jce_phi_topStep_eq
  {E : Finset (Sym2 (Site 2))}
  {a b : ℤ} :
-- imply
  (s(![a, b + 1], ![a + 1, b + 1]) ∈ E ↔ (jce_phi E ![a, b] ↔ ¬ jce_phi E ![a, b + 1])) := by
-- proof
  apply StatMech.Lattice.jce_phi_topStep E a b

/--
[jce_phi_eq_odd_Hc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenClose.lean)
-/
@[path]
private lemma jce_phi_eq_odd_Hc_eq
  {E : Finset (Sym2 (Site 2))}
  {c b : ℤ} :
-- imply
  jce_phi E ![c, b] ↔ Odd (jce_Hc E c b) := by
-- proof
  apply StatMech.Lattice.jce_phi_eq_odd_Hc E c b

/--
[jce_Hc_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenClose.lean)
-/
@[path]
private lemma jce_Hc_succ_eq
  {E : Finset (Sym2 (Site 2))}
  {c b : ℤ} :
-- imply
  jce_Hc E c (b + 1) = jce_Hc E c b + (if s(![c, b + 1], ![c + 1, b + 1]) ∈ E then 1 else 0) := by
-- proof
  apply StatMech.Lattice.jce_Hc_succ E c b

/--
[jce_degree_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenClose.lean)
-/
@[path]
private lemma jce_degree_decomp_eq
  {E : Finset (Sym2 (Site 2))}
  {a r : ℤ} :
-- imply
  jce_degree (E : Set (Sym2 (Site 2))) ![a + 1, r] = (if s(![a + 1, r], ![a + 1 + 1, r]) ∈ E then 1 else 0) + (if s(![a + 1, r], ![a, r]) ∈ E then 1 else 0) + (if s(![a + 1, r], ![a + 1, r + 1]) ∈ E then 1 else 0) + (if s(![a + 1, r], ![a + 1, r - 1]) ∈ E then 1 else 0) := by
-- proof
  apply StatMech.Lattice.jce_degree_decomp E a r

/--
[jce_prop_const_of_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenClose.lean)
-/
@[path]
private lemma jce_prop_const_of_step_eq
  {b0 : ℤ}
-- given
  (Q : ℤ → Prop)
  (hstep : ∀ b, Q b ↔ Q (b + 1))
  (hb0 : Q b0) :
-- imply
  ∀ b, Q b := by
-- proof
  apply StatMech.Lattice.jce_prop_const_of_step Q hstep b0 hb0

/--
[jce_Q_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenClose.lean)
-/
@[path]
private lemma jce_Q_step_eq
  {E : Finset (Sym2 (Site 2))}
  {a b : ℤ}
-- given
  (hcc : jce_ClosedContour (E : Set (Sym2 (Site 2)))) :
-- imply
  ((jce_Hc E a b + jce_Hc E (a + 1) b + (if s(![a + 1, b], ![a + 1, b + 1]) ∈ E then 1 else 0)) % 2 = 0) ↔ ((jce_Hc E a (b + 1) + jce_Hc E (a + 1) (b + 1) + (if s(![a + 1, b + 1], ![a + 1, b + 1 + 1]) ∈ E then 1 else 0)) % 2 = 0) := by
-- proof
  apply StatMech.Lattice.jce_Q_step E hcc a b

/--
[jce_exists_lowRow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenClose.lean)
-/
@[path]
private lemma jce_exists_lowRow_eq
  {E : Finset (Sym2 (Site 2))} :
-- imply
  ∃ L : ℤ, ∀ e ∈ E, ∀ x y : Site 2, e = s(x, y) → L ≤ x 1 ∧ L ≤ y 1 := by
-- proof
  apply StatMech.Lattice.jce_exists_lowRow E

/--
[jce_Q_base](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenClose.lean)
-/
@[path]
private lemma jce_Q_base_eq
  {E : Finset (Sym2 (Site 2))}
  {a : ℤ} :
-- imply
  ∃ b0 : ℤ, (jce_Hc E a b0 + jce_Hc E (a + 1) b0 + (if s(![a + 1, b0], ![a + 1, b0 + 1]) ∈ E then 1 else 0)) % 2 = 0 := by
-- proof
  apply StatMech.Lattice.jce_Q_base E a

/--
[jce_horizStepResidue_holds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenClose.lean)
-/
@[path]
private lemma jce_horizStepResidue_holds_eq :
-- imply
  jce_HorizStepResidue := by
-- proof
  apply StatMech.Lattice.jce_horizStepResidue_holds

/--
[jce_phi_compat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenClose.lean)
-/
@[path]
private lemma jce_phi_compat_eq
  {E : Finset (Sym2 (Site 2))}
  {a b : Site 2}
-- given
  (hres : jce_HorizStepResidue)
  (hcc : jce_ClosedContour (E : Set (Sym2 (Site 2))))
  (hab : (hypercubicLattice 2).Adj a b) :
-- imply
  (sharedPrimalEdge a b ∈ (E : Set (Sym2 (Site 2))) ↔ (jce_phi E a ↔ ¬ jce_phi E b)) := by
-- proof
  apply StatMech.Lattice.jce_phi_compat hres E hcc a b hab

/--
[jce_edgeFlip_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenClose.lean)
-/
@[path]
private lemma jce_edgeFlip_symm_eq
  {E : Finset (Sym2 (Site 2))} :
-- imply
  wcl_SymmFlip (jce_edgeFlip E) := by
-- proof
  apply StatMech.Lattice.jce_edgeFlip_symm E

/--
[jce_edgeFlip_compat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenClose.lean)
-/
@[path]
private lemma jce_edgeFlip_compat_eq
  {E : Finset (Sym2 (Site 2))}
-- given
  (hres : jce_HorizStepResidue)
  (hcc : jce_ClosedContour (E : Set (Sym2 (Site 2)))) :
-- imply
  ∀ a b, (hypercubicLattice 2).Adj a b → (jce_edgeFlip E a b ↔ (jce_phi E a ↔ ¬ jce_phi E b)) := by
-- proof
  apply StatMech.Lattice.jce_edgeFlip_compat hres E hcc

/--
[jce_edgeFlip_closedEven](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenClose.lean)
-/
@[path]
private lemma jce_edgeFlip_closedEven_eq
  {E : Finset (Sym2 (Site 2))}
-- given
  (hres : jce_HorizStepResidue)
  (hcc : jce_ClosedContour (E : Set (Sym2 (Site 2)))) :
-- imply
  wcl_ClosedEven (jce_edgeFlip E) := by
-- proof
  apply StatMech.Lattice.jce_edgeFlip_closedEven hres E hcc

/--
[jce_sharedPrimalEdge_inj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenClose.lean)
-/
@[path]
private lemma jce_sharedPrimalEdge_inj_eq
  {a b c d : Site 2}
-- given
  (hab : (hypercubicLattice 2).Adj a b)
  (hcd : (hypercubicLattice 2).Adj c d) :
-- imply
  (s(a, b) = s(c, d) ↔ sharedPrimalEdge a b = sharedPrimalEdge c d) := by
-- proof
  apply StatMech.Lattice.jce_sharedPrimalEdge_inj hab hcd

/--
[jce_cutFlip_eq_edgeFlip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenClose.lean)
-/
@[path]
private lemma jce_cutFlip_eq_edgeFlip_eq
  {H : SimpleGraph (Site 2)}
  [Fintype H.edgeSet]
  {f0 g0 : Site 2}
  {a b : Site 2}
-- given
  (hfg : (hypercubicLattice 2).Adj f0 g0)
  (hab : (hypercubicLattice 2).Adj a b) :
-- imply
  (wcl_cutFlip H f0 g0 a b ↔ jce_edgeFlip (insert (sharedPrimalEdge f0 g0) H.edgeSet.toFinset) a b) := by
-- proof
  apply StatMech.Lattice.jce_cutFlip_eq_edgeFlip H f0 g0 hfg hab

/--
[jce_flipCount_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenClose.lean)
-/
@[path]
private lemma jce_flipCount_congr_eq
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (flip flip' : Site 2 → Site 2 → Prop)
  (hagree : ∀ a b, (hypercubicLattice 2).Adj a b → (flip a b ↔ flip' a b)) :
-- imply
  wcl_flipCount flip w = wcl_flipCount flip' w := by
-- proof
  apply StatMech.Lattice.jce_flipCount_congr flip flip' hagree w

/--
[jce_closedEven_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenClose.lean)
-/
@[path]
private lemma jce_closedEven_congr_eq
-- given
  (flip flip' : Site 2 → Site 2 → Prop)
  (hagree : ∀ a b, (hypercubicLattice 2).Adj a b → (flip a b ↔ flip' a b))
  (hce : wcl_ClosedEven flip') :
-- imply
  wcl_ClosedEven flip := by
-- proof
  apply StatMech.Lattice.jce_closedEven_congr flip flip' hagree hce

/--
[jce_cutFlip_closedEven](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenClose.lean)
-/
@[path]
private lemma jce_cutFlip_closedEven_eq
  {H : SimpleGraph (Site 2)}
  [Fintype H.edgeSet]
  {f0 g0 : Site 2}
-- given
  (hres : jce_HorizStepResidue)
  (hfg : (hypercubicLattice 2).Adj f0 g0)
  (hcc : jce_ClosedContour ((insert (sharedPrimalEdge f0 g0) H.edgeSet.toFinset : Finset (Sym2 (Site 2))) : Set (Sym2 (Site 2)))) :
-- imply
  wcl_ClosedEven (wcl_cutFlip H f0 g0) := by
-- proof
  apply StatMech.Lattice.jce_cutFlip_closedEven hres H f0 g0 hfg hcc

/--
[jce_whitney_forward_of_evenDegree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenClose.lean)
-/
@[path]
private lemma jce_whitney_forward_of_evenDegree_eq
  {H : SimpleGraph (Site 2)}
  [Fintype H.edgeSet]
  {p q f0 g0 : Site 2}
-- given
  (hres : jce_HorizStepResidue)
  (hpq : (hypercubicLattice 2).Adj p q)
  (hnpq : s(p, q) ∉ H.edgeSet)
  (hfg : (hypercubicLattice 2).Adj f0 g0)
  (hshared : sharedPrimalEdge f0 g0 = s(p, q))
  (hcc : jce_ClosedContour ((insert (sharedPrimalEdge f0 g0) H.edgeSet.toFinset : Finset (Sym2 (Site 2))) : Set (Sym2 (Site 2)))) :
-- imply
  ¬ ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 g0 := by
-- proof
  apply StatMech.Lattice.jce_whitney_forward_of_evenDegree hres H p q f0 g0 hpq hnpq hfg hshared hcc

/--
[jce_cutFlip_closedEven'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenClose.lean)
-/
@[path]
private lemma jce_cutFlip_closedEven'_eq
  {H : SimpleGraph (Site 2)}
  [Fintype H.edgeSet]
  {f0 g0 : Site 2}
-- given
  (hfg : (hypercubicLattice 2).Adj f0 g0)
  (hcc : jce_ClosedContour ((insert (sharedPrimalEdge f0 g0) H.edgeSet.toFinset : Finset (Sym2 (Site 2))) : Set (Sym2 (Site 2)))) :
-- imply
  wcl_ClosedEven (wcl_cutFlip H f0 g0) := by
-- proof
  apply StatMech.Lattice.jce_cutFlip_closedEven' H f0 g0 hfg hcc

/--
[jce_discreteJordanFaithful_of_evenDegree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenClose.lean)
-/
@[path]
private lemma jce_discreteJordanFaithful_of_evenDegree_eq
  {H : SimpleGraph (Site 2)}
  [Fintype H.edgeSet]
  {p q f0 g0 : Site 2}
-- given
  (hpq : (hypercubicLattice 2).Adj p q)
  (hnpq : s(p, q) ∉ H.edgeSet)
  (hfg : (hypercubicLattice 2).Adj f0 g0)
  (hshared : sharedPrimalEdge f0 g0 = s(p, q))
  (hcc : jce_ClosedContour ((insert (sharedPrimalEdge f0 g0) H.edgeSet.toFinset : Finset (Sym2 (Site 2))) : Set (Sym2 (Site 2)))) :
-- imply
  ¬ ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 g0 := by
-- proof
  apply StatMech.Lattice.jce_discreteJordanFaithful_of_evenDegree H p q f0 g0 hpq hnpq hfg hshared hcc

/--
[jce_empty_closedContour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenClose.lean)
-/
@[path]
private lemma jce_empty_closedContour_eq :
-- imply
  jce_ClosedContour ((∅ : Finset (Sym2 (Site 2))) : Set (Sym2 (Site 2))) := by
-- proof
  apply StatMech.Lattice.jce_empty_closedContour

/--
[jce_empty_closedEven](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenClose.lean)
-/
@[path]
private lemma jce_empty_closedEven_eq :
-- imply
  wcl_ClosedEven (jce_edgeFlip (∅ : Finset (Sym2 (Site 2)))) := by
-- proof
  apply StatMech.Lattice.jce_empty_closedEven

/--
[jce_singleEdge_not_closedContour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenClose.lean)
-/
@[path]
private lemma jce_singleEdge_not_closedContour_eq :
-- imply
  ¬ jce_ClosedContour (({s(![(0:ℤ), 0], ![1, 0])} : Finset (Sym2 (Site 2))) : Set (Sym2 (Site 2))) := by
-- proof
  apply StatMech.Lattice.jce_singleEdge_not_closedContour

/--
[jce_reachable_of_twoOdd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanEvenClose.lean)
-/
@[path]
private lemma jce_reachable_of_twoOdd_eq
  {H : SimpleGraph (Site 2)}
  [SimpleGraph.LocallyFinite H]
  {p q : Site 2}
-- given
  (hodd : jce_TwoOddReachable)
  (hp : Odd (H.degree p))
  (hq : Odd (H.degree q))
  (hother : ∀ v, v ≠ p → v ≠ q → Even (H.degree v)) :
-- imply
  H.Reachable p q := by
-- proof
  apply StatMech.Lattice.jce_reachable_of_twoOdd hodd H p q hp hq hother


-- created on 2026-10-23
