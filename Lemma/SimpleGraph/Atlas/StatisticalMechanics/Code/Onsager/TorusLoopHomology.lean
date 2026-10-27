import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.TorusLoopHomology.Part2
open StatMech StatMech.Onsager


/--
[ons_zmod_val_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusLoopHomology.lean)
-/
@[path]
private lemma ons_zmod_val_neg_one_eq
  {L : ℕ}
  [NeZero L] :
-- imply
  (-1 : ZMod L).val = L - 1 := by
-- proof
  apply StatMech.Onsager.ons_zmod_val_neg_one L

/--
[ons_dirExponentX_eq_val_diff_add_wrap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusLoopHomology.lean)
-/
@[path]
private lemma ons_dirExponentX_eq_val_diff_add_wrap_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L} :
-- imply
  ons_dirExponentX d.2 = (((ons_dirStep L d.2 d.1).1.val : ℕ) : ℤ) - ((d.1.1.val : ℕ) : ℤ) + (L : ℤ) * ons_xWrapSign d := by
-- proof
  apply StatMech.Onsager.ons_dirExponentX_eq_val_diff_add_wrap d

/--
[ons_dirExponentY_eq_val_diff_add_wrap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusLoopHomology.lean)
-/
@[path]
private lemma ons_dirExponentY_eq_val_diff_add_wrap_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L} :
-- imply
  ons_dirExponentY d.2 = (((ons_dirStep L d.2 d.1).2.val : ℕ) : ℤ) - ((d.1.2.val : ℕ) : ℤ) + (L : ℤ) * ons_yWrapSign d := by
-- proof
  apply StatMech.Onsager.ons_dirExponentY_eq_val_diff_add_wrap d

/--
[ons_sum_dirExponentX_eq_wrap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusLoopHomology.lean)
-/
@[path]
private lemma ons_sum_dirExponentX_eq_wrap_eq
  {L n : ℕ}
  [Fact (2 < L)]
  [NeZero n]
  {d : Fin n → ons_Dart L}
-- given
  (hvalid : ∀ k : Fin n, (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1) :
-- imply
  (∑ k, ons_dirExponentX (d k).2) = (L : ℤ) * ∑ k, ons_xWrapSign (d k) := by
-- proof
  apply StatMech.Onsager.ons_sum_dirExponentX_eq_wrap d hvalid

/--
[ons_sum_dirExponentY_eq_wrap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusLoopHomology.lean)
-/
@[path]
private lemma ons_sum_dirExponentY_eq_wrap_eq
  {L n : ℕ}
  [Fact (2 < L)]
  [NeZero n]
  {d : Fin n → ons_Dart L}
-- given
  (hvalid : ∀ k : Fin n, (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1) :
-- imply
  (∑ k, ons_dirExponentY (d k).2) = (L : ℤ) * ∑ k, ons_yWrapSign (d k) := by
-- proof
  apply StatMech.Onsager.ons_sum_dirExponentY_eq_wrap d hvalid

/--
[ons_xSeamEdge_portEdge_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusLoopHomology.lean)
-/
@[path]
private lemma ons_xSeamEdge_portEdge_iff_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L} :
-- imply
  ons_xSeamEdge L (ons_portEdge L d) ↔ ons_xWrap d := by
-- proof
  apply StatMech.Onsager.ons_xSeamEdge_portEdge_iff d

/--
[ons_ySeamEdge_portEdge_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusLoopHomology.lean)
-/
@[path]
private lemma ons_ySeamEdge_portEdge_iff_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L} :
-- imply
  ons_ySeamEdge L (ons_portEdge L d) ↔ ons_yWrap d := by
-- proof
  apply StatMech.Onsager.ons_ySeamEdge_portEdge_iff d

/--
[ons_portEdge_loop_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusLoopHomology.lean)
-/
@[path]
private lemma ons_portEdge_loop_injective_eq
  {L n : ℕ}
  [Fact (2 < L)]
  [NeZero n]
  {d : Fin n → ons_Dart L}
-- given
  (hvalid : ∀ k : Fin n, (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
  (hsite : Function.Injective (fun k => (d k).1))
  (hnu : ∀ k : Fin n, (d k).2 ≠ (d (k + 1)).2 + 2) :
-- imply
  Function.Injective (fun k => ons_portEdge L (d k)) := by
-- proof
  apply StatMech.Onsager.ons_portEdge_loop_injective d hvalid hsite hnu

/--
[ons_dartEdgeSet_filter_x](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusLoopHomology.lean)
-/
@[path]
private lemma ons_dartEdgeSet_filter_x_eq
  {L n : ℕ}
  [Fact (2 < L)]
  {d : Fin n → ons_Dart L} :
-- imply
  (ons_dartEdgeSet d).filter (ons_xSeamEdge L) = (Finset.univ.filter (fun k => ons_xWrap (d k))).image (fun k => ons_portEdge L (d k)) := by
-- proof
  apply StatMech.Onsager.ons_dartEdgeSet_filter_x d

/--
[ons_dartEdgeSet_filter_y](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusLoopHomology.lean)
-/
@[path]
private lemma ons_dartEdgeSet_filter_y_eq
  {L n : ℕ}
  [Fact (2 < L)]
  {d : Fin n → ons_Dart L} :
-- imply
  (ons_dartEdgeSet d).filter (ons_ySeamEdge L) = (Finset.univ.filter (fun k => ons_yWrap (d k))).image (fun k => ons_portEdge L (d k)) := by
-- proof
  apply StatMech.Onsager.ons_dartEdgeSet_filter_y d

/--
[ons_dartEdgeSet_xSeam_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusLoopHomology.lean)
-/
@[path]
private lemma ons_dartEdgeSet_xSeam_card_eq
  {L n : ℕ}
  [Fact (2 < L)]
  [NeZero n]
  {d : Fin n → ons_Dart L}
-- given
  (hvalid : ∀ k : Fin n, (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
  (hsite : Function.Injective (fun k => (d k).1))
  (hnu : ∀ k : Fin n, (d k).2 ≠ (d (k + 1)).2 + 2) :
-- imply
  ((ons_dartEdgeSet d).filter (ons_xSeamEdge L)).card = (Finset.univ.filter (fun k => ons_xWrap (d k))).card := by
-- proof
  apply StatMech.Onsager.ons_dartEdgeSet_xSeam_card d hvalid hsite hnu

/--
[ons_dartEdgeSet_ySeam_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusLoopHomology.lean)
-/
@[path]
private lemma ons_dartEdgeSet_ySeam_card_eq
  {L n : ℕ}
  [Fact (2 < L)]
  [NeZero n]
  {d : Fin n → ons_Dart L}
-- given
  (hvalid : ∀ k : Fin n, (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
  (hsite : Function.Injective (fun k => (d k).1))
  (hnu : ∀ k : Fin n, (d k).2 ≠ (d (k + 1)).2 + 2) :
-- imply
  ((ons_dartEdgeSet d).filter (ons_ySeamEdge L)).card = (Finset.univ.filter (fun k => ons_yWrap (d k))).card := by
-- proof
  apply StatMech.Onsager.ons_dartEdgeSet_ySeam_card d hvalid hsite hnu

/--
[ons_intParity_eq_zmod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusLoopHomology.lean)
-/
@[path]
private lemma ons_intParity_eq_zmod_eq
  {m : ℤ} :
-- imply
  ons_intParity m = (m : ZMod 2) := by
-- proof
  apply StatMech.Onsager.ons_intParity_eq_zmod m

/--
[ons_xWrapSign_cast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusLoopHomology.lean)
-/
@[path]
private lemma ons_xWrapSign_cast_eq
  {d : ons_Dart L} :
-- imply
  ((ons_xWrapSign d : ℤ) : ZMod 2) = if ons_xWrap d then 1 else 0 := by
-- proof
  apply StatMech.Onsager.ons_xWrapSign_cast d

/--
[ons_yWrapSign_cast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusLoopHomology.lean)
-/
@[path]
private lemma ons_yWrapSign_cast_eq
  {d : ons_Dart L} :
-- imply
  ((ons_yWrapSign d : ℤ) : ZMod 2) = if ons_yWrap d then 1 else 0 := by
-- proof
  apply StatMech.Onsager.ons_yWrapSign_cast d

/--
[ons_intParity_sum_xWrapSign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusLoopHomology.lean)
-/
@[path]
private lemma ons_intParity_sum_xWrapSign_eq
  {L n : ℕ}
  {d : Fin n → ons_Dart L} :
-- imply
  ons_intParity (∑ k, ons_xWrapSign (d k)) = ⟨(Finset.univ.filter (fun k => ons_xWrap (d k))).card % 2, Nat.mod_lt _ (by decide)⟩ := by
-- proof
  apply StatMech.Onsager.ons_intParity_sum_xWrapSign d

/--
[ons_intParity_sum_yWrapSign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusLoopHomology.lean)
-/
@[path]
private lemma ons_intParity_sum_yWrapSign_eq
  {L n : ℕ}
  {d : Fin n → ons_Dart L} :
-- imply
  ons_intParity (∑ k, ons_yWrapSign (d k)) = ⟨(Finset.univ.filter (fun k => ons_yWrap (d k))).card % 2, Nat.mod_lt _ (by decide)⟩ := by
-- proof
  apply StatMech.Onsager.ons_intParity_sum_yWrapSign d

/--
[ons_evenHomology_dartEdgeSet_eq_windingParity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusLoopHomology.lean)
-/
@[path]
private lemma ons_evenHomology_dartEdgeSet_eq_windingParity_eq
  {L n : ℕ}
  [Fact (2 < L)]
  [NeZero n]
  {d : Fin n → ons_Dart L}
  {mx my : ℤ}
-- given
  (hvalid : ∀ k : Fin n, (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
  (hsite : Function.Injective (fun k => (d k).1))
  (hnu : ∀ k : Fin n, (d k).2 ≠ (d (k + 1)).2 + 2)
  (hmx : (∑ k, ons_dirExponentX (d k).2) = (L : ℤ) * mx)
  (hmy : (∑ k, ons_dirExponentY (d k).2) = (L : ℤ) * my) :
-- imply
  ons_evenHomology L (ons_dartEdgeSet d) = ons_windingParity mx my := by
-- proof
  apply StatMech.Onsager.ons_evenHomology_dartEdgeSet_eq_windingParity d hvalid hsite hnu mx my hmx hmy

/--
[ons_dartEdgeSet_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusLoopHomology.lean)
-/
@[path]
private lemma ons_dartEdgeSet_card_eq
  {L n : ℕ}
  [Fact (2 < L)]
  [NeZero n]
  {d : Fin n → ons_Dart L}
-- given
  (hvalid : ∀ k : Fin n, (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
  (hsite : Function.Injective (fun k => (d k).1))
  (hnu : ∀ k : Fin n, (d k).2 ≠ (d (k + 1)).2 + 2) :
-- imply
  (ons_dartEdgeSet d).card = n := by
-- proof
  apply StatMech.Onsager.ons_dartEdgeSet_card d hvalid hsite hnu

/--
[ons_loopWeight_spinPhase_eq_homology](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusLoopHomology.lean)
-/
@[path]
private lemma ons_loopWeight_spinPhase_eq_homology_eq
  {L n : ℕ}
  [Fact (2 < L)]
  [NeZero n]
  {x omega : ℂ}
  {a b : Fin 2}
  {d : Fin n → ons_Dart L}
-- given
  (hvalid : ∀ k : Fin n, (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
  (hsite : Function.Injective (fun k => (d k).1))
  (hnu : ∀ k : Fin n, (d k).2 ≠ (d (k + 1)).2 + 2) :
-- imply
  ons_loopWeight (ons_KWmatPhase L x omega (ons_spinPhase L a) (ons_spinPhase L b)) d = ons_spinLinearCharacter a b (ons_evenHomology L (ons_dartEdgeSet d)) * ons_loopWeight (ons_KWmat L x omega) d := by
-- proof
  apply StatMech.Onsager.ons_loopWeight_spinPhase_eq_homology x omega a b d hvalid hsite hnu

/--
[ons_loopWeight_spinPhase_eq_spinCharacter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusLoopHomology.lean)
-/
@[path]
private lemma ons_loopWeight_spinPhase_eq_spinCharacter_eq
  {L n : ℕ}
  [Fact (2 < L)]
  [NeZero n]
  {x omega : ℂ}
  {a b : Fin 2}
  {d : Fin n → ons_Dart L}
-- given
  (hvalid : ∀ k : Fin n, (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1)
  (hsite : Function.Injective (fun k => (d k).1))
  (hnu : ∀ k : Fin n, (d k).2 ≠ (d (k + 1)).2 + 2)
  (hgeom : ons_loopWeight (ons_KWmat L x omega) d = -(ons_spinCharacter 0 0 (ons_evenHomology L (ons_dartEdgeSet d)) : ℂ) * x ^ n) :
-- imply
  ons_loopWeight (ons_KWmatPhase L x omega (ons_spinPhase L a) (ons_spinPhase L b)) d = -(ons_spinCharacter a b (ons_evenHomology L (ons_dartEdgeSet d)) : ℂ) * x ^ n := by
-- proof
  apply StatMech.Onsager.ons_loopWeight_spinPhase_eq_spinCharacter x omega a b d hvalid hsite hnu hgeom


-- created on 2026-10-23
