import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexConnClosed
open StatMech StatMech.Universality


/--
[hexClosed_cw_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConnClosed.lean)
-/
@[path]
private lemma hexClosed_cw_nonneg_eq
  {a : ℂ}
  {z : ℂ}
  {x : ℝ}
  {ts : List ℤ}
-- given
  (inRegion : ℂ → Prop)
  (h0 : ℤ)
  (hx : 0 ≤ x) :
-- imply
  0 ≤ hexClosed_cw inRegion a h0 z x ts := by
-- proof
  apply StatMech.Universality.hexClosed_cw_nonneg inRegion a h0 z hx ts

/--
[hexClosed_parafSummand_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConnClosed.lean)
-/
@[path]
private lemma hexClosed_parafSummand_factor_eq
  {a : ℂ}
  {z : ℂ}
  {σ x W : ℝ}
  {ts : List ℤ}
-- given
  (inRegion : ℂ → Prop)
  (h0 : ℤ)
  (hdet : (ofTurns a h0 ts).IsLegalSAW ∧ (ofTurns a h0 ts).StaysIn inRegion ∧ (ofTurns a h0 ts).EndsAt z → (ofTurns a h0 ts).turning = W) :
-- imply
  parafSummand inRegion a h0 z σ x ts = Complex.exp (-Complex.I * (σ : ℂ) * (W : ℂ)) * ((hexClosed_cw inRegion a h0 z x ts : ℝ) : ℂ) := by
-- proof
  apply StatMech.Universality.hexClosed_parafSummand_factor inRegion a h0 z σ x W ts hdet

/--
[hexClosed_parafObservable_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConnClosed.lean)
-/
@[path]
private lemma hexClosed_parafObservable_factor_eq
  {a : ℂ}
  {z : ℂ}
  {σ x W : ℝ}
-- given
  (inRegion : ℂ → Prop)
  (h0 : ℤ)
  (hdet : ∀ ts, (ofTurns a h0 ts).IsLegalSAW ∧ (ofTurns a h0 ts).StaysIn inRegion ∧ (ofTurns a h0 ts).EndsAt z → (ofTurns a h0 ts).turning = W) :
-- imply
  parafObservable inRegion a h0 z σ x = Complex.exp (-Complex.I * (σ : ℂ) * (W : ℂ)) * ((hexClosed_countObs inRegion a h0 z x : ℝ) : ℂ) := by
-- proof
  apply StatMech.Universality.hexClosed_parafObservable_factor inRegion a h0 z σ x W hdet

/--
[hexClosed_sidePhaseLock_of_reflection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConnClosed.lean)
-/
@[path]
private lemma hexClosed_sidePhaseLock_of_reflection_eq
  {a : ℂ}
  {zt zb : ℂ}
  {σ x W r : ℝ}
-- given
  (inRegion : ℂ → Prop)
  (h0 : ℤ)
  (hdett : ∀ ts, (ofTurns a h0 ts).IsLegalSAW ∧ (ofTurns a h0 ts).StaysIn inRegion ∧ (ofTurns a h0 ts).EndsAt zt → (ofTurns a h0 ts).turning = W)
  (hdetb : ∀ ts, (ofTurns a h0 ts).IsLegalSAW ∧ (ofTurns a h0 ts).StaysIn inRegion ∧ (ofTurns a h0 ts).EndsAt zb → (ofTurns a h0 ts).turning = -W)
  (hreflt : hexClosed_countObs inRegion a h0 zt x = r)
  (hreflb : hexClosed_countObs inRegion a h0 zb x = r) :
-- imply
  parafObservable inRegion a h0 zt σ x + parafObservable inRegion a h0 zb σ x = ((2 * Real.cos (σ * W) * r : ℝ) : ℂ) := by
-- proof
  apply StatMech.Universality.hexClosed_sidePhaseLock_of_reflection inRegion a h0 zt zb σ x W r hdett hdetb hreflt hreflb

/--
[hexClosed_cos_sigmaPi_eq_neg_cl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConnClosed.lean)
-/
@[path]
private lemma hexClosed_cos_sigmaPi_eq_neg_cl_eq :
-- imply
  Real.cos ((5 / 8 : ℝ) * Real.pi) = -hexBdryCl := by
-- proof
  apply StatMech.Universality.hexClosed_cos_sigmaPi_eq_neg_cl

/--
[hexClosed_term_le_colSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConnClosed.lean)
-/
@[path]
private lemma hexClosed_term_le_colSum_eq
  {a : ℂ}
  {T : ℕ}
  {χ : ℝ}
  (hreach hsummable hle_one)
  {x : ℝ}
  {b : List ℤ}
-- given
  (h0 : ℤ)
  (mem : List ℤ → Prop)
  (hx : 0 ≤ x)
  (hb : mem b)
  (hxsum : Summable (fun w : {ts // mem ts} => x ^ (HexWalk.ofTurns a h0 w.1).numVertices)) :
-- imply
  x ^ (HexWalk.ofTurns a h0 b).numVertices ≤ (hexColumnOfWidth a h0 T χ mem hreach hsummable hle_one).colSum x := by
-- proof
  apply StatMech.Universality.hexClosed_term_le_colSum a h0 T χ mem hx b hb hxsum

/--
[hexClosed_topSidePhase_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConnClosed.lean)
-/
@[path]
private lemma hexClosed_topSidePhase_eq_eq
  {a : ℂ}
  {zt zb : ℂ}
  {σ x W r coeff cval θ : ℝ}
-- given
  (inRegion : ℂ → Prop)
  (h0 : ℤ)
  (hdett : ∀ ts, (ofTurns a h0 ts).IsLegalSAW ∧ (ofTurns a h0 ts).StaysIn inRegion ∧ (ofTurns a h0 ts).EndsAt zt → (ofTurns a h0 ts).turning = W)
  (hdetb : ∀ ts, (ofTurns a h0 ts).IsLegalSAW ∧ (ofTurns a h0 ts).StaysIn inRegion ∧ (ofTurns a h0 ts).EndsAt zb → (ofTurns a h0 ts).turning = -W)
  (hreflt : hexClosed_countObs inRegion a h0 zt x = r)
  (hreflb : hexClosed_countObs inRegion a h0 zb x = r)
  (hcoeff : Real.cos (σ * W) = coeff)
  (hval : r = cval)
  (htilt : θ = 0) :
-- imply
  parafObservable inRegion a h0 zt σ x + parafObservable inRegion a h0 zb σ x = 2 * Complex.exp ((θ : ℝ) * Complex.I) * ((coeff * cval : ℝ) : ℂ) := by
-- proof
  apply StatMech.Universality.hexClosed_topSidePhase_eq inRegion a h0 zt zb σ x W r coeff cval θ hdett hdetb hreflt hreflb hcoeff hval htilt

/--
[hexClosed_colDomination](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConnClosed.lean)
-/
@[path]
private lemma hexClosed_colDomination_eq
  {a : ℂ}
  {T : ℕ}
  {χ : ℝ}
  (hreach hsummable hle_one)
  {x : ℝ}
  {b : List ℤ}
-- given
  (h0 : ℤ)
  (mem : List ℤ → Prop)
  (hx0 : 0 ≤ x)
  (hχ : 0 < χ)
  (hxχ : x ≤ χ)
  (hb : mem b) :
-- imply
  x ^ (HexWalk.ofTurns a h0 b).numVertices ≤ (hexColumnOfWidth a h0 T χ mem hreach hsummable hle_one).colSum x := by
-- proof
  apply StatMech.Universality.hexClosed_colDomination a h0 T χ mem hx0 hχ hxχ b hb

/--
[hexClosed_factor_at_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConnClosed.lean)
-/
@[path]
private lemma hexClosed_factor_at_zero_eq
  {a : ℂ}
  {z : ℂ}
  {σ x : ℝ}
-- given
  (inRegion : ℂ → Prop)
  (h0 : ℤ)
  (hdet : ∀ ts, (ofTurns a h0 ts).IsLegalSAW ∧ (ofTurns a h0 ts).StaysIn inRegion ∧ (ofTurns a h0 ts).EndsAt z → (ofTurns a h0 ts).turning = 0) :
-- imply
  parafObservable inRegion a h0 z σ x = ((hexClosed_countObs inRegion a h0 z x : ℝ) : ℂ) := by
-- proof
  apply StatMech.Universality.hexClosed_factor_at_zero inRegion a h0 z σ x hdet

/--
[hexClosed_term_le_colSum_trivial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConnClosed.lean)
-/
@[path]
private lemma hexClosed_term_le_colSum_trivial_eq
  {a : ℂ}
  {T : ℕ}
  {χ : ℝ}
  (hreach hsummable hle_one)
  {x : ℝ}
-- given
  (h0 : ℤ)
  (mem : List ℤ → Prop)
  (hx : 0 ≤ x)
  (hb : mem ([] : List ℤ))
  (hxsum : Summable (fun w : {ts // mem ts} => x ^ (HexWalk.ofTurns a h0 w.1).numVertices)) :
-- imply
  x ^ (HexWalk.ofTurns a h0 ([] : List ℤ)).numVertices ≤ (hexColumnOfWidth a h0 T χ mem hreach hsummable hle_one).colSum x := by
-- proof
  apply StatMech.Universality.hexClosed_term_le_colSum_trivial a h0 T χ mem hx hb hxsum


-- created on 2026-10-23
