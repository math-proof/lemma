import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.Z2GaugeTransform
open Finset StatMech StatMech.FrontierA


/--
[localGaugeTransform_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTransform.lean)
-/
@[path]
private lemma localGaugeTransform_apply_eq
  [Fintype E]
  [DecidableEq E]
  {v : Q}
  {omega : GaugeConfig E}
  {e : E}
-- given
  (star : Q -> Finset E) :
-- imply
  localGaugeTransform star v omega e = if e ∈ star v then !(omega e) else omega e := by
-- proof
  apply StatMech.FrontierA.localGaugeTransform_apply star v omega e

/--
[localGaugeTransform_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTransform.lean)
-/
@[path]
private lemma localGaugeTransform_involutive_eq
  [Fintype E]
  [DecidableEq E]
  {v : Q}
  {omega : GaugeConfig E}
-- given
  (star : Q -> Finset E) :
-- imply
  localGaugeTransform star v (localGaugeTransform star v omega) = omega := by
-- proof
  apply StatMech.FrontierA.localGaugeTransform_involutive star v omega

/--
[gaugeEdgeSpin_localGaugeTransform](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTransform.lean)
-/
@[path]
private lemma gaugeEdgeSpin_localGaugeTransform_eq
  [Fintype E]
  [DecidableEq E]
  {v : Q}
  {omega : GaugeConfig E}
  {e : E}
-- given
  (star : Q -> Finset E) :
-- imply
  gaugeEdgeSpin (localGaugeTransform star v omega) e = (if e ∈ star v then (-1 : ℝ) else 1) * gaugeEdgeSpin omega e := by
-- proof
  apply StatMech.FrontierA.gaugeEdgeSpin_localGaugeTransform star v omega e

/--
[prod_star_sign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTransform.lean)
-/
@[path]
private lemma prod_star_sign_eq
  [Fintype E]
  [DecidableEq E]
  {v : Q}
  {A : Finset E}
-- given
  (star : Q -> Finset E) :
-- imply
  (∏ e ∈ A, if e ∈ star v then (-1 : ℝ) else 1) = (-1 : ℝ) ^ (A ∩ star v).card := by
-- proof
  apply StatMech.FrontierA.prod_star_sign star v A

/--
[plaquetteSpin_localGaugeTransform](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTransform.lean)
-/
@[path]
private lemma plaquetteSpin_localGaugeTransform_eq
  [Fintype E]
  [DecidableEq E]
  {v : Q}
  {omega : GaugeConfig E}
  {p : P}
-- given
  (incidence : P -> Finset E)
  (star : Q -> Finset E) :
-- imply
  plaquetteSpin incidence (localGaugeTransform star v omega) p = (-1 : ℝ) ^ (incidence p ∩ star v).card * plaquetteSpin incidence omega p := by
-- proof
  apply StatMech.FrontierA.plaquetteSpin_localGaugeTransform incidence star v omega p

/--
[plaquetteSpin_localGaugeTransform_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTransform.lean)
-/
@[path]
private lemma plaquetteSpin_localGaugeTransform_eq_eq
  [Fintype E]
  [DecidableEq E]
  {v : Q}
  {omega : GaugeConfig E}
  {p : P}
-- given
  (incidence : P -> Finset E)
  (star : Q -> Finset E)
  (hcomplex : HasEvenPlaquetteStarIncidence incidence star) :
-- imply
  plaquetteSpin incidence (localGaugeTransform star v omega) p = plaquetteSpin incidence omega p := by
-- proof
  apply StatMech.FrontierA.plaquetteSpin_localGaugeTransform_eq incidence star hcomplex v omega p

/--
[gaugeAction_localGaugeTransform_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTransform.lean)
-/
@[path]
private lemma gaugeAction_localGaugeTransform_eq_eq
  [Fintype E]
  [DecidableEq E]
  {v : Q}
  {omega : GaugeConfig E}
-- given
  (incidence : P -> Finset E)
  (star : Q -> Finset E)
  (hcomplex : HasEvenPlaquetteStarIncidence incidence star)
  (K : P -> ℝ) :
-- imply
  gaugeAction incidence K (localGaugeTransform star v omega) = gaugeAction incidence K omega := by
-- proof
  apply StatMech.FrontierA.gaugeAction_localGaugeTransform_eq incidence star hcomplex K v omega

/--
[gaugeWeight_localGaugeTransform_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTransform.lean)
-/
@[path]
private lemma gaugeWeight_localGaugeTransform_eq_eq
  [Fintype E]
  [DecidableEq E]
  {v : Q}
  {omega : GaugeConfig E}
-- given
  (incidence : P -> Finset E)
  (star : Q -> Finset E)
  (hcomplex : HasEvenPlaquetteStarIncidence incidence star)
  (K : P -> ℝ) :
-- imply
  gaugeWeight incidence K (localGaugeTransform star v omega) = gaugeWeight incidence K omega := by
-- proof
  apply StatMech.FrontierA.gaugeWeight_localGaugeTransform_eq incidence star hcomplex K v omega

/--
[wilsonSpin_localGaugeTransform](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTransform.lean)
-/
@[path]
private lemma wilsonSpin_localGaugeTransform_eq
  [Fintype E]
  [DecidableEq E]
  {v : Q}
  {L : Finset E}
  {omega : GaugeConfig E}
-- given
  (star : Q -> Finset E) :
-- imply
  wilsonSpin L (localGaugeTransform star v omega) = (-1 : ℝ) ^ (L ∩ star v).card * wilsonSpin L omega := by
-- proof
  apply StatMech.FrontierA.wilsonSpin_localGaugeTransform star v L omega

/--
[wilsonSpin_localGaugeTransform_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTransform.lean)
-/
@[path]
private lemma wilsonSpin_localGaugeTransform_eq_eq
  [Fintype E]
  [DecidableEq E]
  {L : Finset E}
  {v : Q}
  {omega : GaugeConfig E}
-- given
  (star : Q -> Finset E)
  (hclosed : IsGaugeClosed star L) :
-- imply
  wilsonSpin L (localGaugeTransform star v omega) = wilsonSpin L omega := by
-- proof
  apply StatMech.FrontierA.wilsonSpin_localGaugeTransform_eq star L hclosed v omega


-- created on 2026-10-23
