import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.GreenStubClose.Part6
open Set SimpleGraph Finset MeasureTheory StatMech.Lattice StatMech.RSW.Box StatMech StatMech.Universality


/--
[gst_greenConfig_eq_negConfig_in_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/GreenStubClose.lean)
-/
@[path]
private lemma gst_greenConfig_eq_negConfig_in_box_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {x y : Site 2}
-- given
  (hx : x ∈ rect 0 (n + 1) 0 n)
  (hy : y ∈ rect 0 (n + 1) 0 n) :
-- imply
  gec2_greenConfig ω n s(x, y) = des_negConfig ω s(x, y) := by
-- proof
  apply StatMech.Universality.gst_greenConfig_eq_negConfig_in_box ω n hx hy

/--
[gst_greenMatchedFrame_iff_matchedFrameDualV](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/GreenStubClose.lean)
-/
@[path]
private lemma gst_greenMatchedFrame_iff_matchedFrameDualV_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ} :
-- imply
  gec2_GreenMatchedFrame ω n ↔ mpd_MatchedFrameDualV ω n := by
-- proof
  apply StatMech.Universality.gst_greenMatchedFrame_iff_matchedFrameDualV ω n

/--
[gst_greenJordan_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/GreenStubClose.lean)
-/
@[path]
private lemma gst_greenJordan_false_eq
  {n : ℤ}
-- given
  (hn : 1 ≤ n) :
-- imply
  ¬ gec2_GreenJordan des_cutConfig n := by
-- proof
  apply StatMech.Universality.gst_greenJordan_false n hn

/--
[gst_greenDualConfig_open_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/GreenStubClose.lean)
-/
@[path]
private lemma gst_greenDualConfig_open_iff_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {e : Sym2 (Site 2)} :
-- imply
  gst_greenDualConfig ω n e = true ↔ e ∈ gst_greenSet n ∨ dualConfig ω e = true := by
-- proof
  apply StatMech.Universality.gst_greenDualConfig_open_iff ω n e

/--
[gst_greenDualConfig_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/GreenStubClose.lean)
-/
@[path]
private lemma gst_greenDualConfig_ge_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ} :
-- imply
  dualConfig ω ≤ gst_greenDualConfig ω n := by
-- proof
  apply StatMech.Universality.gst_greenDualConfig_ge ω n

/--
[gst_greenDualV_of_matchedFrameDualV](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/GreenStubClose.lean)
-/
@[path]
private lemma gst_greenDualV_of_matchedFrameDualV_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (h : mpd_MatchedFrameDualV ω n) :
-- imply
  gst_GreenDualV ω n := by
-- proof
  apply StatMech.Universality.gst_greenDualV_of_matchedFrameDualV ω n h

/--
[gst_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/GreenStubClose.lean)
-/
@[path]
private lemma gst_nonvacuous_eq
  {n : ℤ}
-- given
  (hn : 0 ≤ n) :
-- imply
  ¬ HorizontalCrossing bcc_botCfg 0 (n + 1) 0 n ∧ gst_GreenDualV bcc_botCfg n := by
-- proof
  apply StatMech.Universality.gst_nonvacuous n hn

/--
[gst_cutEdge_open_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/GreenStubClose.lean)
-/
@[path]
private lemma gst_cutEdge_open_invariant_eq
  {n : ℤ}
  {u v : Site 2}
-- given
  (h : IsOpenEdge 2 (gst_greenDualConfig des_cutConfig n) u v) :
-- imply
  (u 1 ≤ 1 ∧ v 1 ≤ 1) ∨ (u 1 = n + 1 ∧ v 1 = n + 1) := by
-- proof
  apply StatMech.Universality.gst_cutEdge_open_invariant n h

/--
[gst_cut_walk_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/GreenStubClose.lean)
-/
@[path]
private lemma gst_cut_walk_le_one_eq
  {n : ℤ}
  {S : Set (Site 2)}
  {x y : S}
-- given
  (hn : 1 ≤ n)
  (h : ConnectedWithin 2 (gst_greenDualConfig des_cutConfig n) S x y)
  (hx : (x : Site 2) 1 ≤ 1) :
-- imply
  (y : Site 2) 1 ≤ 1 := by
-- proof
  apply StatMech.Universality.gst_cut_walk_le_one n hn h hx

/--
[gst_cut_fails](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/GreenStubClose.lean)
-/
@[path]
private lemma gst_cut_fails_eq
  {n : ℤ}
-- given
  (hn : 1 ≤ n) :
-- imply
  ¬ gst_GreenDualV des_cutConfig n := by
-- proof
  apply StatMech.Universality.gst_cut_fails n hn

/--
[gst_fullWire_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/GreenStubClose.lean)
-/
@[path]
private lemma gst_fullWire_open_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {e : Sym2 (Site 2)}
-- given
  (h : e ∈ gst_fullWireSet n) :
-- imply
  gst_fullWireConfig ω n e = true := by
-- proof
  apply StatMech.Universality.gst_fullWire_open ω n h

/--
[gst_wire_reach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/GreenStubClose.lean)
-/
@[path]
private lemma gst_wire_reach_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
  {k : ℕ}
-- given
  (hn : 0 ≤ n)
  (hk : (k : ℤ) ≤ n + 1) :
-- imply
  (openSubgraphInduce 2 (gst_fullWireConfig ω n) (rect (-n) 0 0 (n + 1))).Reachable ⟨![-n, 0], by rw [mem_rect]; simp; omega⟩ ⟨![-n, (k : ℤ)], by rw [mem_rect]; simp; omega⟩ := by
-- proof
  apply StatMech.Universality.gst_wire_reach ω n hn k hk

/--
[gst_fullWire_trivial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/GreenStubClose.lean)
-/
@[path]
private lemma gst_fullWire_trivial_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hn : 0 ≤ n) :
-- imply
  VerticalCrossing (gst_fullWireConfig ω n) (-n) 0 0 (n + 1) := by
-- proof
  apply StatMech.Universality.gst_fullWire_trivial ω n hn

/--
[gst_dichotomy_of_genuine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/GreenStubClose.lean)
-/
@[path]
private lemma gst_dichotomy_of_genuine_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {n : ℤ}
-- given
  (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
  (h : gst_genuine_residue ω n) :
-- imply
  HorizontalCrossing ω 0 n 0 n ∨ DualVerticalCrossing ω 0 n 0 n := by
-- proof
  apply StatMech.Universality.gst_dichotomy_of_genuine ω n hnoH h

/--
[gst_genuine_residue_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/GreenStubClose.lean)
-/
@[path]
private lemma gst_genuine_residue_nonvacuous_eq :
-- imply
  gst_genuine_residue bcc_botCfg 2 := by
-- proof
  apply StatMech.Universality.gst_genuine_residue_nonvacuous

/--
[gst_matched_half_of_greenDichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/GreenStubClose.lean)
-/
@[path]
private lemma gst_matched_half_of_greenDichotomy_eq
  {n : ℤ}
-- given
  (hmeasH : MeasurableSet (horizontalCrossingEvent 0 (n + 1) 0 n))
  (hmeasV : MeasurableSet (verticalCrossingEvent (-n) 0 0 (n + 1)))
  (hgreen : gec2_GreenDichotomy n)
  (hsym : rba_selfDualMeasure.real (verticalCrossingEvent (-n) 0 0 (n + 1)) = rba_selfDualMeasure.real (horizontalCrossingEvent 0 (n + 1) 0 n)) :
-- imply
  (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (horizontalCrossingEvent 0 (n + 1) 0 n) := by
-- proof
  apply StatMech.Universality.gst_matched_half_of_greenDichotomy n hmeasH hmeasV hgreen hsym

/--
[gst_greenDichotomy_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/GreenStubClose.lean)
-/
@[path]
private lemma gst_greenDichotomy_false_eq
  {n : ℤ}
-- given
  (hn : 1 ≤ n) :
-- imply
  ¬ gec2_GreenDichotomy n := by
-- proof
  apply StatMech.Universality.gst_greenDichotomy_false n hn


-- created on 2026-10-23
