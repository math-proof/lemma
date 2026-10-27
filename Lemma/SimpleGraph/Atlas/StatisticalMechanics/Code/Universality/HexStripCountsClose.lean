import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexStripCountsClose.Part3
open StatMech StatMech.Universality


/--
[hsc_negTurns_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripCountsClose.lean)
-/
@[path]
private lemma hsc_negTurns_nil_eq :
-- imply
  hsc_negTurns [] = [] := by
-- proof
  apply StatMech.Universality.hsc_negTurns_nil

/--
[hsc_negTurns_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripCountsClose.lean)
-/
@[path]
private lemma hsc_negTurns_cons_eq
  {t : ℤ}
  {ts : List ℤ} :
-- imply
  hsc_negTurns (t :: ts) = (-t) :: hsc_negTurns ts := by
-- proof
  apply StatMech.Universality.hsc_negTurns_cons t ts

/--
[hsc_negTurns_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripCountsClose.lean)
-/
@[path]
private lemma hsc_negTurns_length_eq
  {ts : List ℤ} :
-- imply
  (hsc_negTurns ts).length = ts.length := by
-- proof
  apply StatMech.Universality.hsc_negTurns_length ts

/--
[hsc_negTurns_negTurns](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripCountsClose.lean)
-/
@[path]
private lemma hsc_negTurns_negTurns_eq
  {ts : List ℤ} :
-- imply
  hsc_negTurns (hsc_negTurns ts) = ts := by
-- proof
  apply StatMech.Universality.hsc_negTurns_negTurns ts

/--
[hsc_refl_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripCountsClose.lean)
-/
@[path]
private lemma hsc_refl_fixed_eq
  {a0 : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  hsc_refl a0 h0 a0 = a0 := by
-- proof
  apply StatMech.Universality.hsc_refl_fixed a0 h0

/--
[hsc_refl_invol](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripCountsClose.lean)
-/
@[path]
private lemma hsc_refl_invol_eq
  {a0 : ℂ}
  {z : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  hsc_refl a0 h0 (hsc_refl a0 h0 z) = z := by
-- proof
  apply StatMech.Universality.hsc_refl_invol a0 h0 z

/--
[hsc_refl_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripCountsClose.lean)
-/
@[path]
private lemma hsc_refl_injective_eq
  {a0 : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  Function.Injective (hsc_refl a0 h0) := by
-- proof
  apply StatMech.Universality.hsc_refl_injective a0 h0

/--
[hsc_conj_hexUnit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripCountsClose.lean)
-/
@[path]
private lemma hsc_conj_hexUnit_eq
-- given
  (h : ℤ) :
-- imply
  (starRingEnd ℂ) (hexUnit h) = hexUnit (-1 - h) := by
-- proof
  apply StatMech.Universality.hsc_conj_hexUnit h

/--
[hsc_genHexUnit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripCountsClose.lean)
-/
@[path]
private lemma hsc_genHexUnit_eq
-- given
  (h0 h : ℤ) :
-- imply
  hexUnit (2 * h0 - h) = (hexUnit h0)^2 * (starRingEnd ℂ) (hexUnit h) := by
-- proof
  apply StatMech.Universality.hsc_genHexUnit h0 h

/--
[hsc_genHalfStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripCountsClose.lean)
-/
@[path]
private lemma hsc_genHalfStep_eq
-- given
  (h0 h : ℤ) :
-- imply
  HexWalk.halfStep (2 * h0 - h) = (hexUnit h0)^2 * (starRingEnd ℂ) (HexWalk.halfStep h) := by
-- proof
  apply StatMech.Universality.hsc_genHalfStep h0 h

/--
[hsc_genHeadAccum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripCountsClose.lean)
-/
@[path]
private lemma hsc_genHeadAccum_eq
  {ts : List ℤ}
-- given
  (h0 h : ℤ) :
-- imply
  hexInfra_headAccum (2 * h0 - h) (hsc_negTurns ts) = 2 * h0 - hexInfra_headAccum h ts := by
-- proof
  apply StatMech.Universality.hsc_genHeadAccum h0 h ts

/--
[hsc_genMidAccum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripCountsClose.lean)
-/
@[path]
private lemma hsc_genMidAccum_eq
  {a0 : ℂ}
  {m : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (h : ℤ) :
-- imply
  hexInfra_midAccum (hsc_refl a0 h0 m) (2 * h0 - h) (hsc_negTurns ts) = hsc_refl a0 h0 (hexInfra_midAccum m h ts) := by
-- proof
  apply StatMech.Universality.hsc_genMidAccum a0 h0 m h ts

/--
[hsc_genMidsAux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripCountsClose.lean)
-/
@[path]
private lemma hsc_genMidsAux_eq
  {a0 : ℂ}
  {m : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (h : ℤ) :
-- imply
  HexWalk.midsAux (hsc_refl a0 h0 m) (2 * h0 - h) (hsc_negTurns ts) = (HexWalk.midsAux m h ts).map (hsc_refl a0 h0) := by
-- proof
  apply StatMech.Universality.hsc_genMidsAux a0 h0 m h ts

/--
[hsc_genVerticesAux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripCountsClose.lean)
-/
@[path]
private lemma hsc_genVerticesAux_eq
  {a0 : ℂ}
  {m : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (h : ℤ) :
-- imply
  HexWalk.verticesAux (hsc_refl a0 h0 m) (2 * h0 - h) (hsc_negTurns ts) = (HexWalk.verticesAux m h ts).map (hsc_refl a0 h0) := by
-- proof
  apply StatMech.Universality.hsc_genVerticesAux a0 h0 m h ts

/--
[hsc_genEndMid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripCountsClose.lean)
-/
@[path]
private lemma hsc_genEndMid_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ) :
-- imply
  (HexWalk.ofTurns a h0 (hsc_negTurns ts)).endMid = hsc_refl a h0 ((HexWalk.ofTurns a h0 ts).endMid) := by
-- proof
  apply StatMech.Universality.hsc_genEndMid a h0 ts

/--
[hsc_genIsSAW](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripCountsClose.lean)
-/
@[path]
private lemma hsc_genIsSAW_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hsaw : (HexWalk.ofTurns a h0 ts).IsSAW) :
-- imply
  (HexWalk.ofTurns a h0 (hsc_negTurns ts)).IsSAW := by
-- proof
  apply StatMech.Universality.hsc_genIsSAW a h0 ts hsaw

/--
[hsc_genLegalTurns](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripCountsClose.lean)
-/
@[path]
private lemma hsc_genLegalTurns_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (hlt : (HexWalk.ofTurns a h0 ts).LegalTurns) :
-- imply
  (HexWalk.ofTurns a h0 (hsc_negTurns ts)).LegalTurns := by
-- proof
  apply StatMech.Universality.hsc_genLegalTurns a h0 ts hlt

/--
[hsc_genStaysIn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripCountsClose.lean)
-/
@[path]
private lemma hsc_genStaysIn_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (region : ℂ → Prop)
  (h0 : ℤ)
  (hsym : ∀ m, region m → region (hsc_refl a h0 m))
  (hstays : (HexWalk.ofTurns a h0 ts).StaysIn region) :
-- imply
  (HexWalk.ofTurns a h0 (hsc_negTurns ts)).StaysIn region := by
-- proof
  apply StatMech.Universality.hsc_genStaysIn region a h0 ts hsym hstays

/--
[hsc_genNumVertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripCountsClose.lean)
-/
@[path]
private lemma hsc_genNumVertices_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ) :
-- imply
  (HexWalk.ofTurns a h0 (hsc_negTurns ts)).numVertices = (HexWalk.ofTurns a h0 ts).numVertices := by
-- proof
  apply StatMech.Universality.hsc_genNumVertices a h0 ts

/--
[hsc_genTurning_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripCountsClose.lean)
-/
@[path]
private lemma hsc_genTurning_neg_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ) :
-- imply
  (HexWalk.ofTurns a h0 (hsc_negTurns ts)).turning = -(HexWalk.ofTurns a h0 ts).turning := by
-- proof
  apply StatMech.Universality.hsc_genTurning_neg a h0 ts

/--
[hsc_cw_refl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripCountsClose.lean)
-/
@[path]
private lemma hsc_cw_refl_eq
  {a : ℂ}
  {z : ℂ}
  {x : ℝ}
  {ts : List ℤ}
-- given
  (region : ℂ → Prop)
  (h0 : ℤ)
  (hsym : ∀ m, region m → region (hsc_refl a h0 m)) :
-- imply
  hexClosed_cw region a h0 (hsc_refl a h0 z) x (hsc_negTurns ts) = hexClosed_cw region a h0 z x ts := by
-- proof
  apply StatMech.Universality.hsc_cw_refl region a h0 z x hsym ts

/--
[hsc_countObs_refl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripCountsClose.lean)
-/
@[path]
private lemma hsc_countObs_refl_eq
  {a : ℂ}
  {z : ℂ}
  {x : ℝ}
-- given
  (region : ℂ → Prop)
  (h0 : ℤ)
  (hsym : ∀ m, region m → region (hsc_refl a h0 m)) :
-- imply
  hexClosed_countObs region a h0 (hsc_refl a h0 z) x = hexClosed_countObs region a h0 z x := by
-- proof
  apply StatMech.Universality.hsc_countObs_refl region a h0 z x hsym

/--
[hsc_detb_of_dett](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripCountsClose.lean)
-/
@[path]
private lemma hsc_detb_of_dett_eq
  {a : ℂ}
  {z : ℂ}
  {W : ℝ}
-- given
  (region : ℂ → Prop)
  (h0 : ℤ)
  (hsym : ∀ m, region m → region (hsc_refl a h0 m))
  (hdett : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW ∧ (HexWalk.ofTurns a h0 ts).StaysIn region ∧ (HexWalk.ofTurns a h0 ts).EndsAt z → (HexWalk.ofTurns a h0 ts).turning = W) :
-- imply
  ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW ∧ (HexWalk.ofTurns a h0 ts).StaysIn region ∧ (HexWalk.ofTurns a h0 ts).EndsAt (hsc_refl a h0 z) → (HexWalk.ofTurns a h0 ts).turning = -W := by
-- proof
  apply StatMech.Universality.hsc_detb_of_dett region a h0 z W hsym hdett

/--
[hsc_sidePhaseLock_single](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripCountsClose.lean)
-/
@[path]
private lemma hsc_sidePhaseLock_single_eq
  {a : ℂ}
  {z : ℂ}
  {σ x W : ℝ}
-- given
  (region : ℂ → Prop)
  (h0 : ℤ)
  (hsym : ∀ m, region m → region (hsc_refl a h0 m))
  (hdett : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW ∧ (HexWalk.ofTurns a h0 ts).StaysIn region ∧ (HexWalk.ofTurns a h0 ts).EndsAt z → (HexWalk.ofTurns a h0 ts).turning = W) :
-- imply
  parafObservable region a h0 z σ x + parafObservable region a h0 (hsc_refl a h0 z) σ x = ((2 * Real.cos (σ * W) * hexClosed_countObs region a h0 z x : ℝ) : ℂ) := by
-- proof
  apply StatMech.Universality.hsc_sidePhaseLock_single region a h0 z σ x W hsym hdett

/--
[hsc_full_region_sym](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripCountsClose.lean)
-/
@[path]
private lemma hsc_full_region_sym_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  ∀ m, (fun _ : ℂ => True) m → (fun _ : ℂ => True) (hsc_refl a h0 m) := by
-- proof
  apply StatMech.Universality.hsc_full_region_sym a h0

/--
[hsc_countObs_refl_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripCountsClose.lean)
-/
@[path]
private lemma hsc_countObs_refl_full_eq
  {a : ℂ}
  {z : ℂ}
  {x : ℝ}
-- given
  (h0 : ℤ) :
-- imply
  hexClosed_countObs (fun _ => True) a h0 (hsc_refl a h0 z) x = hexClosed_countObs (fun _ => True) a h0 z x := by
-- proof
  apply StatMech.Universality.hsc_countObs_refl_full a h0 z x

/--
[hsc_sidePhaseLock_zeroWinding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexStripCountsClose.lean)
-/
@[path]
private lemma hsc_sidePhaseLock_zeroWinding_eq
  {a : ℂ}
  {z : ℂ}
  {σ x : ℝ}
-- given
  (h0 : ℤ)
  (hdet0 : ∀ ts, (HexWalk.ofTurns a h0 ts).IsLegalSAW ∧ (HexWalk.ofTurns a h0 ts).StaysIn (fun _ => True) ∧ (HexWalk.ofTurns a h0 ts).EndsAt z → (HexWalk.ofTurns a h0 ts).turning = 0) :
-- imply
  parafObservable (fun _ => True) a h0 z σ x + parafObservable (fun _ => True) a h0 (hsc_refl a h0 z) σ x = ((2 * hexClosed_countObs (fun _ => True) a h0 z x : ℝ) : ℂ) := by
-- proof
  apply StatMech.Universality.hsc_sidePhaseLock_zeroWinding a h0 z σ x hdet0


-- created on 2026-10-23
