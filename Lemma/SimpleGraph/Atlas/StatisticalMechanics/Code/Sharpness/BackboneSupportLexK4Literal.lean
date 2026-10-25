import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSupportLexK4Literal.Part3
open Finset SimpleGraph StatMech StatMech.Sharpness


/--
[shb_current_tsum_eq_paritySeriesMassOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexK4Literal.lean)
-/
@[path]
private lemma shb_current_tsum_eq_paritySeriesMassOn_eq
  [DecidableEq E]
  {S : Finset E}
  [DecidablePred P]
  {x : ℝ}
-- given
  (P : Finset E → Prop)
  (hx : 0 ≤ x) :
-- imply
  (∑' m : ↑S → ℕ, if P (shbParitySupportOn S m) then ∏ e : ↑S, shbCurrentTerm x (m e) else 0) = shbParitySeriesMassOn S P x := by
-- proof
  apply StatMech.Sharpness.shb_current_tsum_eq_paritySeriesMassOn S P x hx

/--
[shbK4_backboneNumSupport_eq_seriesMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexK4Literal.lean)
-/
@[path]
private lemma shbK4_backboneNumSupport_eq_seriesMass_eq
  {E : Finset shbK4Edge}
  {x : ℝ}
-- given
  (h03 : shbK4Edge.e03 ∈ E)
  (hx : 0 ≤ x) :
-- imply
  shb_backboneNumSupport (shbK4Graph E) x (fun _ ↦ 1) 0 3 (shbK4DirectPath E h03) = shbK4DirectFiberSeriesMass E x := by
-- proof
  apply StatMech.Sharpness.shbK4_backboneNumSupport_eq_seriesMass E h03 x hx

/--
[shbK4_currentSum_empty_eq_seriesMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexK4Literal.lean)
-/
@[path]
private lemma shbK4_currentSum_empty_eq_seriesMass_eq
  {E : Finset shbK4Edge}
  {x : ℝ}
-- given
  (hx : 0 ≤ x) :
-- imply
  currentSum (shbK4Graph E) x (fun _ ↦ 1) ∅ = shbK4VacuumSeriesMass E x := by
-- proof
  apply StatMech.Sharpness.shbK4_currentSum_empty_eq_seriesMass E x hx

/--
[shbK4_rhoSupport_eq_directRhoSeries](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexK4Literal.lean)
-/
@[path]
private lemma shbK4_rhoSupport_eq_directRhoSeries_eq
  {E : Finset shbK4Edge}
  {x : ℝ}
-- given
  (h03 : shbK4Edge.e03 ∈ E)
  (hx : 0 ≤ x) :
-- imply
  shb_rhoSupport (shbK4Graph E) x (fun _ ↦ 1) 0 3 (shbK4DirectPath E h03) = shbK4DirectRhoSeries E x := by
-- proof
  apply StatMech.Sharpness.shbK4_rhoSupport_eq_directRhoSeries E h03 x hx

/--
[shb_supportLex_literal_P3_counterexample](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexK4Literal.lean)
-/
@[path]
private lemma shb_supportLex_literal_P3_counterexample_eq :
-- imply
  shb_rhoSupport (shbK4Graph shbK4H) (Real.artanh (2 / 3)) (fun _ ↦ 1) 0 3 (shbK4DirectPath shbK4H (by decide)) < shb_rhoSupport (shbK4Graph shbK4G) (Real.artanh (2 / 3)) (fun _ ↦ 1) 0 3 (shb_pathMapLe (shbK4Graph_mono shbK4H_subset_shbK4G) (shbK4DirectPath shbK4H (by decide))) := by
-- proof
  apply StatMech.Sharpness.shb_supportLex_literal_P3_counterexample


-- created on 2026-10-23
