import Mathlib
import Initialize.Tactic.Attr.Basic
import Structure.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part4
open StatMech StatMech.Universality StatMech.Universality.HLHRTruncatedTwoHalfData StatMech.Universality.HLHRAugmentedTwoHalfData


/--
[hlhr_exists_extremum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma hlhr_exists_extremum_eq
  {f : ℕ → ℝ}
  {up : Bool}
  {lo hi : ℕ}
-- given
  (hlo : lo ≤ hi) :
-- imply
  ∃ k, HLHRIsExtremum f up lo hi k := by
-- proof
  apply StatMech.Universality.hlhr_exists_extremum f up hlo

/--
[hlhr_lastExtremum_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma hlhr_lastExtremum_spec_eq
  {f : ℕ → ℝ}
  {up : Bool}
  {lo hi : ℕ}
-- given
  (hlo : lo ≤ hi) :
-- imply
  HLHRIsExtremum f up lo hi (hlhr_lastExtremum f up lo hi) := by
-- proof
  apply StatMech.Universality.hlhr_lastExtremum_spec f up hlo

/--
[hlhr_lastExtremum_lo_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma hlhr_lastExtremum_lo_le_eq
  {f : ℕ → ℝ}
  {up : Bool}
  {lo hi : ℕ}
-- given
  (hlo : lo ≤ hi) :
-- imply
  lo ≤ hlhr_lastExtremum f up lo hi := by
-- proof
  apply StatMech.Universality.hlhr_lastExtremum_lo_le f up hlo

/--
[hlhr_lastExtremum_le_hi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma hlhr_lastExtremum_le_hi_eq
  {f : ℕ → ℝ}
  {up : Bool}
  {lo hi : ℕ}
-- given
  (hlo : lo ≤ hi) :
-- imply
  hlhr_lastExtremum f up lo hi ≤ hi := by
-- proof
  apply StatMech.Universality.hlhr_lastExtremum_le_hi f up hlo

/--
[hlhr_lastExtremum_is_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma hlhr_lastExtremum_is_last_eq
  {f : ℕ → ℝ}
  {up : Bool}
  {lo hi j : ℕ}
-- given
  (hlo : lo ≤ hi)
  (hj : hlhr_lastExtremum f up lo hi < j)
  (hjhi : j ≤ hi) :
-- imply
  ¬ HLHRIsExtremum f up lo hi j := by
-- proof
  apply StatMech.Universality.hlhr_lastExtremum_is_last f up hlo hj hjhi

/--
[hlhr_cut_gt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma hlhr_cut_gt_eq
  {f : ℕ → ℝ}
  {up : Bool}
  {lo hi : ℕ}
-- given
  (h : lo < hi) :
-- imply
  lo < hlhr_cut f up lo hi := by
-- proof
  apply StatMech.Universality.hlhr_cut_gt f up h

/--
[hlhr_cut_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma hlhr_cut_le_eq
  {f : ℕ → ℝ}
  {up : Bool}
  {lo hi : ℕ}
-- given
  (h : lo ≤ hi) :
-- imply
  hlhr_cut f up lo hi ≤ hi := by
-- proof
  apply StatMech.Universality.hlhr_cut_le f up h

/--
[hlhr_signed_not](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma hlhr_signed_not_eq
  {up : Bool}
  {x : ℝ} :
-- imply
  hlhr_signed (!up) x = -hlhr_signed up x := by
-- proof
  apply StatMech.Universality.hlhr_signed_not up x

/--
[hlhr_lastExtremum_gt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma hlhr_lastExtremum_gt_eq
  {f : ℕ → ℝ}
  {up : Bool}
  {lo hi : ℕ}
-- given
  (hlt : lo < hi)
  (hahead : HLHRAhead f up lo hi) :
-- imply
  lo < hlhr_lastExtremum f up lo hi := by
-- proof
  apply StatMech.Universality.hlhr_lastExtremum_gt f up hlt hahead

/--
[hlhr_cut_eq_lastExtremum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma hlhr_cut_eq_lastExtremum_eq
  {f : ℕ → ℝ}
  {up : Bool}
  {lo hi : ℕ}
-- given
  (hlt : lo < hi)
  (hahead : HLHRAhead f up lo hi) :
-- imply
  hlhr_cut f up lo hi = hlhr_lastExtremum f up lo hi := by
-- proof
  apply StatMech.Universality.hlhr_cut_eq_lastExtremum f up hlt hahead

/--
[hlhr_lastExtremum_strict_after](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma hlhr_lastExtremum_strict_after_eq
  {f : ℕ → ℝ}
  {up : Bool}
  {lo hi : ℕ}
  {j : ℕ}
-- given
  (hlt : lo < hi)
  (hj : hlhr_lastExtremum f up lo hi < j)
  (hjhi : j ≤ hi) :
-- imply
  hlhr_signed up (f j) < hlhr_signed up (f (hlhr_lastExtremum f up lo hi)) := by
-- proof
  apply StatMech.Universality.hlhr_lastExtremum_strict_after f up hlt hj hjhi

/--
[hlhr_ahead_next](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma hlhr_ahead_next_eq
  {f : ℕ → ℝ}
  {up : Bool}
  {lo hi : ℕ}
-- given
  (hlt : lo < hi) :
-- imply
  HLHRAhead f (!up) (hlhr_lastExtremum f up lo hi) hi := by
-- proof
  apply StatMech.Universality.hlhr_ahead_next f up hlt

/--
[hlhr_orientedSpan_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma hlhr_orientedSpan_pos_eq
  {f : ℕ → ℝ}
  {up : Bool}
  {lo hi : ℕ}
-- given
  (hlt : lo < hi)
  (hahead : HLHRAhead f up lo hi) :
-- imply
  0 < hlhr_orientedSpan f up lo (hlhr_lastExtremum f up lo hi) := by
-- proof
  apply StatMech.Universality.hlhr_orientedSpan_pos f up hlt hahead

/--
[hlhr_orientedSpan_next_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma hlhr_orientedSpan_next_lt_eq
  {f : ℕ → ℝ}
  {up : Bool}
  {lo hi : ℕ}
-- given
  (hlt : lo < hi)
  (hahead : HLHRAhead f up lo hi)
  (hk : hlhr_lastExtremum f up lo hi < hi) :
-- imply
  hlhr_orientedSpan f (!up) (hlhr_lastExtremum f up lo hi) (hlhr_lastExtremum f (!up) (hlhr_lastExtremum f up lo hi) hi) < hlhr_orientedSpan f up lo (hlhr_lastExtremum f up lo hi) := by
-- proof
  apply StatMech.Universality.hlhr_orientedSpan_next_lt f up hlt hahead hk

/--
[hlhr_intervalSpan_eq_oriented](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma hlhr_intervalSpan_eq_oriented_eq
  {f : ℕ → ℝ}
  {up : Bool}
  {lo hi : ℕ}
-- given
  (hlt : lo < hi)
  (hahead : HLHRAhead f up lo hi) :
-- imply
  hlhr_intervalSpan f (lo, hlhr_lastExtremum f up lo hi) = hlhr_orientedSpan f up lo (hlhr_lastExtremum f up lo hi) := by
-- proof
  apply StatMech.Universality.hlhr_intervalSpan_eq_oriented f up hlt hahead

/--
[hlhr_intervalSpans_ordered](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma hlhr_intervalSpans_ordered_eq
  {f : ℕ → ℝ}
  {up : Bool}
-- given
  (hi fuel lo : ℕ)
  (hlt : lo < hi)
  (hahead : HLHRAhead f up lo hi) :
-- imply
  let ws := hlhr_intervalSpans f (hlhr_intervalsAux f hi fuel up lo) ws.Pairwise (· > ·) ∧ (∀ w ∈ ws, 0 < w) ∧ (∀ w ∈ ws, w ≤ hlhr_orientedSpan f up lo (hlhr_lastExtremum f up lo hi)) := by
-- proof
  apply StatMech.Universality.hlhr_intervalSpans_ordered f hi fuel lo up hlt hahead

/--
[hlhr_intervalsAux_reconstruct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma hlhr_intervalsAux_reconstruct_eq
  {f : ℕ → ℝ}
  {root : List ℤ}
  {fuel lo : ℕ}
  {up : Bool}
-- given
  (hlo : lo ≤ root.length)
  (hfuel : root.length - lo ≤ fuel)
  (hahead : lo < root.length → HLHRAhead f up lo root.length) :
-- imply
  hlhr_intervalTurns root (hlhr_intervalsAux f root.length fuel up lo) = root.drop lo := by
-- proof
  apply StatMech.Universality.hlhr_intervalsAux_reconstruct f root fuel lo up hlo hfuel hahead

/--
[hlhr_intervalsAux_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma hlhr_intervalsAux_bounds_eq
  {f : ℕ → ℝ}
  {up : Bool}
-- given
  (hi fuel lo : ℕ)
  (hlt : lo < hi)
  (hahead : HLHRAhead f up lo hi) :
-- imply
  ∀ p ∈ hlhr_intervalsAux f hi fuel up lo, lo ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ hi := by
-- proof
  apply StatMech.Universality.hlhr_intervalsAux_bounds f hi fuel lo up hlt hahead

/--
[hlhr_literalHalfSpace_ahead](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma hlhr_literalHalfSpace_ahead_eq
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hhalf : HLHRLiteralHalfSpace h0 ts) :
-- imply
  HLHRAhead (hlhr_height h0 ts) true 0 ts.length := by
-- proof
  apply StatMech.Universality.hlhr_literalHalfSpace_ahead h0 ts hhalf

/--
[hlhr_literalIntervals_reconstruct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma hlhr_literalIntervals_reconstruct_eq
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hhalf : HLHRLiteralHalfSpace h0 ts) :
-- imply
  hlhr_intervalTurns ts (hlhr_literalIntervals h0 ts) = ts := by
-- proof
  apply StatMech.Universality.hlhr_literalIntervals_reconstruct h0 ts hhalf

/--
[hlhr_literalSpans_pairwise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma hlhr_literalSpans_pairwise_eq
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hhalf : HLHRLiteralHalfSpace h0 ts) :
-- imply
  (hlhr_literalSpans h0 ts).Pairwise (· > ·) := by
-- proof
  apply StatMech.Universality.hlhr_literalSpans_pairwise h0 ts hhalf

/--
[hlhr_literalSpans_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma hlhr_literalSpans_pos_eq
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hhalf : HLHRLiteralHalfSpace h0 ts) :
-- imply
  ∀ w ∈ hlhr_literalSpans h0 ts, 0 < w := by
-- proof
  apply StatMech.Universality.hlhr_literalSpans_pos h0 ts hhalf

/--
[hlhr_piecesAux_reconstruct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma hlhr_piecesAux_reconstruct_eq
  {f : ℕ → ℝ}
  {up : Bool}
  {ts : List ℤ}
-- given
  (hi fuel lo : ℕ) :
-- imply
  hlhr_pieceTurns (hlhr_piecesAux f hi fuel up lo ts) = ts := by
-- proof
  apply StatMech.Universality.hlhr_piecesAux_reconstruct f hi fuel lo up ts

/--
[hlhr_pieces_reconstruct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma hlhr_pieces_reconstruct_eq
  {f : ℕ → ℝ}
  {ts : List ℤ} :
-- imply
  hlhr_pieceTurns (hlhr_pieces f ts) = ts := by
-- proof
  apply StatMech.Universality.hlhr_pieces_reconstruct f ts

/--
[hlhr_piecesAux_slice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma hlhr_piecesAux_slice_eq
  {f : ℕ → ℝ}
  {root : List ℤ}
  {fuel : ℕ}
  {up : Bool}
  {lo : ℕ}
-- given
  (hlo : lo ≤ root.length) :
-- imply
  ∀ p ∈ hlhr_piecesAux f root.length fuel up lo (root.drop lo), p.2 = (root.drop p.1).take p.2.length ∧ p.1 + p.2.length ≤ root.length := by
-- proof
  apply StatMech.Universality.hlhr_piecesAux_slice f root fuel up lo hlo

/--
[hlhr_pieces_slice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma hlhr_pieces_slice_eq
  {f : ℕ → ℝ}
  {root : List ℤ} :
-- imply
  ∀ p ∈ hlhr_pieces f root, p.2 = (root.drop p.1).take p.2.length ∧ p.1 + p.2.length ≤ root.length := by
-- proof
  apply StatMech.Universality.hlhr_pieces_slice f root

/--
[hlhr_piecesAux_content_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma hlhr_piecesAux_content_ne_eq
  {f : ℕ → ℝ}
  {root : List ℤ}
  {fuel : ℕ}
  {up : Bool}
  {lo : ℕ}
-- given
  (hlo : lo ≤ root.length) :
-- imply
  ∀ p ∈ hlhr_piecesAux f root.length fuel up lo (root.drop lo), p.2 ≠ [] := by
-- proof
  apply StatMech.Universality.hlhr_piecesAux_content_ne f root fuel up lo hlo

/--
[hlhr_pieces_content_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma hlhr_pieces_content_ne_eq
  {f : ℕ → ℝ}
  {root : List ℤ} :
-- imply
  ∀ p ∈ hlhr_pieces f root, p.2 ≠ [] := by
-- proof
  apply StatMech.Universality.hlhr_pieces_content_ne f root

/--
[hlhr_slice_legal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma hlhr_slice_legal_eq
  {a : ℂ}
  {ts : List ℤ}
  {lo len : ℕ}
-- given
  (h0 : ℤ)
  (hleg : (ofTurns a h0 ts).IsLegalSAW)
  (hbound : lo + len ≤ ts.length) :
-- imply
  (ofTurns (hlhr_pieceMid a h0 ts lo) (hlhr_pieceHead h0 ts lo) ((ts.drop lo).take len)).IsLegalSAW := by
-- proof
  apply StatMech.Universality.hlhr_slice_legal a h0 ts hleg hbound

/--
[hlhr_slice_legal_rebase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma hlhr_slice_legal_rebase_eq
  {a a' : ℂ}
  {ts : List ℤ}
  {lo len : ℕ}
-- given
  (h0 : ℤ)
  (hleg : (ofTurns a h0 ts).IsLegalSAW)
  (hbound : lo + len ≤ ts.length) :
-- imply
  (ofTurns a' (hlhr_pieceHead h0 ts lo) ((ts.drop lo).take len)).IsLegalSAW := by
-- proof
  apply StatMech.Universality.hlhr_slice_legal_rebase a a' h0 ts hleg hbound

/--
[hlhr_literalInterval_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma hlhr_literalInterval_bounds_eq
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hhalf : HLHRLiteralHalfSpace h0 ts) :
-- imply
  ∀ p ∈ hlhr_literalIntervals h0 ts, p.1 < p.2 ∧ p.2 ≤ ts.length := by
-- proof
  apply StatMech.Universality.hlhr_literalInterval_bounds h0 ts hhalf

/--
[hlhr_literalInterval_legal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma hlhr_literalInterval_legal_eq
  {a : ℂ}
  {ts : List ℤ}
  {p : ℕ × ℕ}
-- given
  (h0 : ℤ)
  (hleg : (ofTurns a h0 ts).IsLegalSAW)
  (hhalf : HLHRLiteralHalfSpace h0 ts)
  (hp : p ∈ hlhr_literalIntervals h0 ts) :
-- imply
  (ofTurns (hlhr_pieceMid a h0 ts p.1) (hlhr_pieceHead h0 ts p.1) (hlhr_intervalContent ts p)).IsLegalSAW := by
-- proof
  apply StatMech.Universality.hlhr_literalInterval_legal a h0 ts hleg hhalf hp

/--
[hlhr_literalInterval_legal_rebase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma hlhr_literalInterval_legal_rebase_eq
  {a a' : ℂ}
  {ts : List ℤ}
  {p : ℕ × ℕ}
-- given
  (h0 : ℤ)
  (hleg : (ofTurns a h0 ts).IsLegalSAW)
  (hhalf : HLHRLiteralHalfSpace h0 ts)
  (hp : p ∈ hlhr_literalIntervals h0 ts) :
-- imply
  (ofTurns a' (hlhr_pieceHead h0 ts p.1) (hlhr_intervalContent ts p)).IsLegalSAW := by
-- proof
  apply StatMech.Universality.hlhr_literalInterval_legal_rebase a a' h0 ts hleg hhalf hp

/--
[hlhr_literalInterval_reflected_legal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma hlhr_literalInterval_reflected_legal_eq
  {a a' : ℂ}
  {ts : List ℤ}
  {p : ℕ × ℕ}
-- given
  (h0 : ℤ)
  (hleg : (ofTurns a h0 ts).IsLegalSAW)
  (hhalf : HLHRLiteralHalfSpace h0 ts)
  (hp : p ∈ hlhr_literalIntervals h0 ts) :
-- imply
  (ofTurns a' (hlhr_pieceHead h0 ts p.1) (hsc_negTurns (hlhr_intervalContent ts p))).IsLegalSAW := by
-- proof
  apply StatMech.Universality.hlhr_literalInterval_reflected_legal a a' h0 ts hleg hhalf hp

/--
[hlhr_intervalWeight_eq_pow_turns](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma hlhr_intervalWeight_eq_pow_turns_eq
  {x : ℝ}
  {ts : List ℤ}
  {ps : List (ℕ × ℕ)} :
-- imply
  (ps.map (hlhr_intervalWeight x ts)).prod = x ^ (hlhr_intervalTurns ts ps).length := by
-- proof
  apply StatMech.Universality.hlhr_intervalWeight_eq_pow_turns x ts ps

/--
[hlhr_literalInterval_weight_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma hlhr_literalInterval_weight_factor_eq
  {ts : List ℤ}
  {x : ℝ}
-- given
  (h0 : ℤ)
  (hhalf : HLHRLiteralHalfSpace h0 ts) :
-- imply
  ((hlhr_literalIntervals h0 ts).map (hlhr_intervalWeight x ts)).prod = x ^ ts.length := by
-- proof
  apply StatMech.Universality.hlhr_literalInterval_weight_factor h0 ts hhalf x

/--
[hlhr_coordRun_geometry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma hlhr_coordRun_geometry_eq
  {p d : HexReturnCoord}
  {m s : ℂ}
  {ts : List ℤ}
-- given
  (h : ℤ)
  (hdir : halfStep h = d.value * s)
  (hlegal : ∀ t ∈ ts, t = 1 ∨ t = -1) :
-- imply
  let r := hlhr_coordRun p d ts hexInfra_midAccum m h ts + halfStep (hexInfra_headAccum h ts) = m + halfStep h + 2 * ((r.pos.value - p.value) * s) ∧ halfStep (hexInfra_headAccum h ts) = r.dir.value * s := by
-- proof
  apply StatMech.Universality.hlhr_coordRun_geometry p d m s h ts hdir hlegal

/--
[hlhr_halfStep_zero_re](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma hlhr_halfStep_zero_re_eq :
-- imply
  (halfStep 0).re = Real.sqrt 3 / 4 := by
-- proof
  apply StatMech.Universality.hlhr_halfStep_zero_re

/--
[hlhr_halfStep_two_re](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma hlhr_halfStep_two_re_eq :
-- imply
  (halfStep 2).re = -(Real.sqrt 3 / 4) := by
-- proof
  apply StatMech.Universality.hlhr_halfStep_two_re

/--
[hlhr_eisenstein_horizontal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma hlhr_eisenstein_horizontal_eq
  {d : HexReturnCoord} :
-- imply
  (2 * (d.value * halfStep 0)).re = (Real.sqrt 3 / 2) * (d.x - d.y) := by
-- proof
  apply StatMech.Universality.hlhr_eisenstein_horizontal d

/--
[hlhr_height_eq_latticeHeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma hlhr_height_eq_latticeHeight_eq
  {ts : List ℤ}
  {k : ℕ}
-- given
  (hlegal : (ofTurns 0 0 ts).LegalTurns) :
-- imply
  hlhr_height 0 ts k = Real.sqrt 3 / 4 + (Real.sqrt 3 / 2) * hlhr_latticeHeight ts k := by
-- proof
  apply StatMech.Universality.hlhr_height_eq_latticeHeight ts hlegal k

/--
[hlhr_natAbs_cast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma hlhr_natAbs_cast_eq
  {z : ℤ} :
-- imply
  ((z.natAbs : ℕ) : ℝ) = := by
-- proof
  apply StatMech.Universality.hlhr_natAbs_cast z

/--
[hlhr_intervalSpan_eq_latticeWidth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma hlhr_intervalSpan_eq_latticeWidth_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
-- given
  (hlegal : (ofTurns 0 0 ts).LegalTurns) :
-- imply
  hlhr_intervalSpan (hlhr_height 0 ts) p = (Real.sqrt 3 / 2) * hlhr_latticeWidth ts p := by
-- proof
  apply StatMech.Universality.hlhr_intervalSpan_eq_latticeWidth ts hlegal p

/--
[hlhr_latticeWidth_pos_of_span_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma hlhr_latticeWidth_pos_of_span_pos_eq
  {ts : List ℤ}
  {p : ℕ × ℕ}
-- given
  (hlegal : (ofTurns 0 0 ts).LegalTurns)
  (hspan : 0 < hlhr_intervalSpan (hlhr_height 0 ts) p) :
-- imply
  0 < hlhr_latticeWidth ts p := by
-- proof
  apply StatMech.Universality.hlhr_latticeWidth_pos_of_span_pos ts hlegal p hspan

/--
[hlhr_latticeWidth_gt_of_span_gt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma hlhr_latticeWidth_gt_of_span_gt_eq
  {ts : List ℤ}
  {p q : ℕ × ℕ}
-- given
  (hlegal : (ofTurns 0 0 ts).LegalTurns)
  (hspan : hlhr_intervalSpan (hlhr_height 0 ts) p > hlhr_intervalSpan (hlhr_height 0 ts) q) :
-- imply
  hlhr_latticeWidth ts p > hlhr_latticeWidth ts q := by
-- proof
  apply StatMech.Universality.hlhr_latticeWidth_gt_of_span_gt ts hlegal p q hspan

/--
[hlhr_literalWidths_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma hlhr_literalWidths_pos_eq
  {ts : List ℤ}
-- given
  (hleg : (ofTurns 0 0 ts).IsLegalSAW)
  (hhalf : HLHRLiteralHalfSpace 0 ts) :
-- imply
  ∀ T ∈ hlhr_literalWidths ts, 0 < T := by
-- proof
  apply StatMech.Universality.hlhr_literalWidths_pos ts hleg hhalf

/--
[hlhr_literalWidths_pairwise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma hlhr_literalWidths_pairwise_eq
  {ts : List ℤ}
-- given
  (hleg : (ofTurns 0 0 ts).IsLegalSAW)
  (hhalf : HLHRLiteralHalfSpace 0 ts) :
-- imply
  (hlhr_literalWidths ts).Pairwise (· > ·) := by
-- proof
  apply StatMech.Universality.hlhr_literalWidths_pairwise ts hleg hhalf

/--
[hlhr_literalBridge_width](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma hlhr_literalBridge_width_eq
  {ts : List ℤ}
  (hleg hhalf)
  (p) :
-- imply
  (hlhr_literalBridge ts hleg hhalf p).width = hlhr_latticeWidth ts p.1 := by
-- proof
  apply StatMech.Universality.hlhr_literalBridge_width ts

/--
[hlhr_literalBridge_content](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma hlhr_literalBridge_content_eq
  {ts : List ℤ}
  (hleg hhalf)
  (p) :
-- imply
  (hlhr_literalBridge ts hleg hhalf p).content = hlhr_intervalContent ts p.1 := by
-- proof
  apply StatMech.Universality.hlhr_literalBridge_content ts

/--
[hlhr_literalBridgeList_contents](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma hlhr_literalBridgeList_contents_eq
  {ts : List ℤ}
-- given
  (hleg : (ofTurns 0 0 ts).IsLegalSAW)
  (hhalf : HLHRLiteralHalfSpace 0 ts) :
-- imply
  ((hlhr_literalBridgeList ts hleg hhalf).map HexBridge.content).flatten = ts := by
-- proof
  apply StatMech.Universality.hlhr_literalBridgeList_contents ts hleg hhalf

/--
[hlhr_literalBridgeList_widths](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma hlhr_literalBridgeList_widths_eq
  {ts : List ℤ}
-- given
  (hleg : (ofTurns 0 0 ts).IsLegalSAW)
  (hhalf : HLHRLiteralHalfSpace 0 ts) :
-- imply
  (hlhr_literalBridgeList ts hleg hhalf).map HexBridge.width = hlhr_literalWidths ts := by
-- proof
  apply StatMech.Universality.hlhr_literalBridgeList_widths ts hleg hhalf

/--
[hlhr_literalBridgeList_strict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma hlhr_literalBridgeList_strict_eq
  {ts : List ℤ}
-- given
  (hleg : (ofTurns 0 0 ts).IsLegalSAW)
  (hhalf : HLHRLiteralHalfSpace 0 ts) :
-- imply
  StrictDecreasingWidths (hlhr_literalBridgeList ts hleg hhalf) := by
-- proof
  apply StatMech.Universality.hlhr_literalBridgeList_strict ts hleg hhalf

/--
[hlhr_contentHalf_turns](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma hlhr_contentHalf_turns_eq
  {ts : List ℤ}
-- given
  (hleg : (ofTurns 0 0 ts).IsLegalSAW)
  (hhalf : HLHRLiteralHalfSpace 0 ts) :
-- imply
  hhc_halfTurns (hlhr_contentHalf ts hleg hhalf) = ts := by
-- proof
  apply StatMech.Universality.hlhr_contentHalf_turns ts hleg hhalf

/--
[hlhr_singleLeft_legal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma hlhr_singleLeft_legal_eq :
-- imply
  (ofTurns 0 0 [(1 : ℤ)]).IsLegalSAW := by
-- proof
  apply StatMech.Universality.hlhr_singleLeft_legal

/--
[hlhr_singleLeft_not_halfSpace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma hlhr_singleLeft_not_halfSpace_eq :
-- imply
  ¬ HLHRLiteralHalfSpace 0 [(1 : ℤ)] := by
-- proof
  apply StatMech.Universality.hlhr_singleLeft_not_halfSpace

/--
[hlhr_no_unaugmented_split_singleLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma hlhr_no_unaugmented_split_singleLeft_eq :
-- imply
  ¬ ∃ lower upper : List ℤ, [(1 : ℤ)] = lower ++ upper ∧ HLHRLiteralHalfSpace 0 lower ∧ HLHRLiteralHalfSpace 0 upper := by
-- proof
  apply StatMech.Universality.hlhr_no_unaugmented_split_singleLeft

/--
[hlhr_truncatedTwoHalfData_isEmpty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma hlhr_truncatedTwoHalfData_isEmpty_eq :
-- imply
  IsEmpty (HLHRTruncatedTwoHalfData 0 0 2) := by
-- proof
  apply StatMech.Universality.hlhr_truncatedTwoHalfData_isEmpty

/--
[halves_reconstruct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma halves_reconstruct_eq
  {a : ℂ}
  {h0 : ℤ}
  {N : ℕ}
  {H : HLHRTruncatedTwoHalfData a h0 N}
  {d : hhc_Dn a h0 N} :
-- imply
  d.1 = hhc_halfTurns (H.lowerHalf d) ++ hhc_halfTurns (H.upperHalf d) := by
-- proof
  apply StatMech.Universality.HLHRTruncatedTwoHalfData.halves_reconstruct H d

/--
[finite_partial_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma finite_partial_bound_eq
  {a : ℂ}
  {h0 : ℤ}
  {N : ℕ}
  {H : HLHRTruncatedTwoHalfData a h0 N}
  {x : ℝ}
-- given
  (hx : 0 ≤ x) :
-- imply
  ∑ n ∈ Finset.range N, (hlc_sawCount a h0 n : ℝ) * x ^ n ≤ (∑ s ∈ H.contentDecomp.lowerImage, hhc_halfWeight x s) * (∑ s ∈ H.contentDecomp.upperImage, hhc_halfWeight x s) := by
-- proof
  apply StatMech.Universality.HLHRTruncatedTwoHalfData.finite_partial_bound H hx

/--
[lower_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma lower_tail_eq
  {a : ℂ}
  {h0 : ℤ}
  {N : ℕ}
  {H : HLHRAugmentedTwoHalfData a h0 N}
  {d : hhc_Dn a h0 N} :
-- imply
  (H.lower d).tail = H.lowerCore d := by
-- proof
  apply StatMech.Universality.HLHRAugmentedTwoHalfData.lower_tail H d

/--
[upper_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma upper_tail_eq
  {a : ℂ}
  {h0 : ℤ}
  {N : ℕ}
  {H : HLHRAugmentedTwoHalfData a h0 N}
  {d : hhc_Dn a h0 N} :
-- imply
  (H.upper d).tail = H.upperCore d := by
-- proof
  apply StatMech.Universality.HLHRAugmentedTwoHalfData.upper_tail H d

/--
[decode_augmented](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma decode_augmented_eq
  {a : ℂ}
  {h0 : ℤ}
  {N : ℕ}
  {H : HLHRAugmentedTwoHalfData a h0 N}
  {d : hhc_Dn a h0 N} :
-- imply
  H.decode (H.lower d).head! (H.lower d).tail (H.upper d).head! (H.upper d).tail = d.1 := by
-- proof
  apply StatMech.Universality.HLHRAugmentedTwoHalfData.decode_augmented H d

/--
[length_add_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma length_add_two_eq
  {a : ℂ}
  {h0 : ℤ}
  {N : ℕ}
  {H : HLHRAugmentedTwoHalfData a h0 N}
  {d : hhc_Dn a h0 N} :
-- imply
  (H.lower d).length + (H.upper d).length = d.1.length + 2 := by
-- proof
  apply StatMech.Universality.HLHRAugmentedTwoHalfData.length_add_two H d

/--
[lowerBoundary_legal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma lowerBoundary_legal_eq
  {a : ℂ}
  {h0 : ℤ}
  {N : ℕ}
  {H : HLHRAugmentedTwoHalfData a h0 N}
  {d : hhc_Dn a h0 N} :
-- imply
  H.lowerBoundary d = 1 ∨ H.lowerBoundary d = -1 := by
-- proof
  apply StatMech.Universality.HLHRAugmentedTwoHalfData.lowerBoundary_legal H d

/--
[upperBoundary_legal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma upperBoundary_legal_eq
  {a : ℂ}
  {h0 : ℤ}
  {N : ℕ}
  {H : HLHRAugmentedTwoHalfData a h0 N}
  {d : hhc_Dn a h0 N} :
-- imply
  H.upperBoundary d = 1 ∨ H.upperBoundary d = -1 := by
-- proof
  apply StatMech.Universality.HLHRAugmentedTwoHalfData.upperBoundary_legal H d

/--
[lowerBoundary_outward](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma lowerBoundary_outward_eq
  {a : ℂ}
  {h0 : ℤ}
  {N : ℕ}
  {H : HLHRAugmentedTwoHalfData a h0 N}
  {d : hhc_Dn a h0 N} :
-- imply
  hlhr_height 0 (H.lower d) 0 < hlhr_height 0 (H.lower d) 1 := by
-- proof
  apply StatMech.Universality.HLHRAugmentedTwoHalfData.lowerBoundary_outward H d

/--
[upperBoundary_outward](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma upperBoundary_outward_eq
  {a : ℂ}
  {h0 : ℤ}
  {N : ℕ}
  {H : HLHRAugmentedTwoHalfData a h0 N}
  {d : hhc_Dn a h0 N} :
-- imply
  hlhr_height 0 (H.upper d) 0 < hlhr_height 0 (H.upper d) 1 := by
-- proof
  apply StatMech.Universality.HLHRAugmentedTwoHalfData.upperBoundary_outward H d

/--
[listPair_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma listPair_injective_eq
  {a : ℂ}
  {h0 : ℤ}
  {N : ℕ}
  {H : HLHRAugmentedTwoHalfData a h0 N} :
-- imply
  Function.Injective (fun d => (H.lower d, H.upper d)) := by
-- proof
  apply StatMech.Universality.HLHRAugmentedTwoHalfData.listPair_injective H

/--
[lowerHalf_turns](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma lowerHalf_turns_eq
  {a : ℂ}
  {h0 : ℤ}
  {N : ℕ}
  {H : HLHRAugmentedTwoHalfData a h0 N}
  {d : hhc_Dn a h0 N} :
-- imply
  hhc_halfTurns (H.lowerHalf d) = H.lower d := by
-- proof
  apply StatMech.Universality.HLHRAugmentedTwoHalfData.lowerHalf_turns H d

/--
[upperHalf_turns](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma upperHalf_turns_eq
  {a : ℂ}
  {h0 : ℤ}
  {N : ℕ}
  {H : HLHRAugmentedTwoHalfData a h0 N}
  {d : hhc_Dn a h0 N} :
-- imply
  hhc_halfTurns (H.upperHalf d) = H.upper d := by
-- proof
  apply StatMech.Universality.HLHRAugmentedTwoHalfData.upperHalf_turns H d

/--
[contentPair_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma contentPair_injective_eq
  {a : ℂ}
  {h0 : ℤ}
  {N : ℕ}
  {H : HLHRAugmentedTwoHalfData a h0 N} :
-- imply
  Function.Injective H.contentPair := by
-- proof
  apply StatMech.Universality.HLHRAugmentedTwoHalfData.contentPair_injective H

/--
[source_weight_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma source_weight_factor_eq
  {a : ℂ}
  {h0 : ℤ}
  {N : ℕ}
  {H : HLHRAugmentedTwoHalfData a h0 N}
  {x : ℝ}
  {d : hhc_Dn a h0 N}
-- given
  (hx : 0 < x) :
-- imply
  x ^ d.1.length = (x ^ 2)⁻¹ * (hhc_halfWeight x (H.lowerHalf d) * hhc_halfWeight x (H.upperHalf d)) := by
-- proof
  apply StatMech.Universality.HLHRAugmentedTwoHalfData.source_weight_factor H x hx d

/--
[sum_eq_pairImage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma sum_eq_pairImage_eq
  {a : ℂ}
  {h0 : ℤ}
  {N : ℕ}
  {H : HLHRAugmentedTwoHalfData a h0 N}
  {x : ℝ} :
-- imply
  ∑ d : hhc_Dn a h0 N, hhc_halfWeight x (H.lowerHalf d) * hhc_halfWeight x (H.upperHalf d) = ∑ p ∈ H.pairImage, hhc_halfWeight x p.1 * hhc_halfWeight x p.2 := by
-- proof
  apply StatMech.Universality.HLHRAugmentedTwoHalfData.sum_eq_pairImage H x

/--
[pairImage_subset_product](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma pairImage_subset_product_eq
  {a : ℂ}
  {h0 : ℤ}
  {N : ℕ}
  {H : HLHRAugmentedTwoHalfData a h0 N} :
-- imply
  H.pairImage ⊆ H.lowerImage ×ˢ H.upperImage := by
-- proof
  apply StatMech.Universality.HLHRAugmentedTwoHalfData.pairImage_subset_product H

/--
[pair_sum_le_product](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma pair_sum_le_product_eq
  {a : ℂ}
  {h0 : ℤ}
  {N : ℕ}
  {H : HLHRAugmentedTwoHalfData a h0 N}
  {x : ℝ}
-- given
  (hx : 0 ≤ x) :
-- imply
  (∑ p ∈ H.pairImage, hhc_halfWeight x p.1 * hhc_halfWeight x p.2) ≤ (∑ s ∈ H.lowerImage, hhc_halfWeight x s) * (∑ s ∈ H.upperImage, hhc_halfWeight x s) := by
-- proof
  apply StatMech.Universality.HLHRAugmentedTwoHalfData.pair_sum_le_product H hx

/--
[finite_partial_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean)
-/
@[path]
private lemma finite_partial_bound_eq_2
  {a : ℂ}
  {h0 : ℤ}
  {N : ℕ}
  {H : HLHRAugmentedTwoHalfData a h0 N}
  {x : ℝ}
-- given
  (hx : 0 < x) :
-- imply
  ∑ n ∈ Finset.range N, (hlc_sawCount a h0 n : ℝ) * x ^ n ≤ (x ^ 2)⁻¹ * ((∑ s ∈ H.lowerImage, hhc_halfWeight x s) * (∑ s ∈ H.upperImage, hhc_halfWeight x s)) := by
-- proof
  apply StatMech.Universality.HLHRAugmentedTwoHalfData.finite_partial_bound H hx


-- created on 2026-10-23
