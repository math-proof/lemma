import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardGauge
open StatMech StatMech.FrontierA


/--
[kw_det_gaugeConjugate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardGauge.lean)
-/
@[path]
private lemma kw_det_gaugeConjugate_eq
  [Fintype D]
  [DecidableEq D]
  {M : Matrix D D ℂ}
-- given
  (gauge : D -> ℂ)
  (hgauge : ∀ i, gauge i ≠ 0) :
-- imply
  (kwGaugeConjugate gauge M).det = M.det := by
-- proof
  apply StatMech.FrontierA.kw_det_gaugeConjugate gauge M hgauge

/--
[kwGaugeConjugate_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardGauge.lean)
-/
@[path]
private lemma kwGaugeConjugate_one_eq
  [Fintype D]
  [DecidableEq D]
-- given
  (gauge : D -> ℂ)
  (hgauge : ∀ i, gauge i ≠ 0) :
-- imply
  kwGaugeConjugate gauge (1 : Matrix D D ℂ) = 1 := by
-- proof
  apply StatMech.FrontierA.kwGaugeConjugate_one gauge hgauge

/--
[kwGaugeConjugate_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardGauge.lean)
-/
@[path]
private lemma kwGaugeConjugate_sub_eq
  [Fintype D]
  [DecidableEq D]
  {M N : Matrix D D ℂ}
-- given
  (gauge : D -> ℂ) :
-- imply
  kwGaugeConjugate gauge (M - N) = kwGaugeConjugate gauge M - kwGaugeConjugate gauge N := by
-- proof
  apply StatMech.FrontierA.kwGaugeConjugate_sub gauge M N

/--
[kw_det_one_sub_gaugeConjugate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardGauge.lean)
-/
@[path]
private lemma kw_det_one_sub_gaugeConjugate_eq
  [Fintype D]
  [DecidableEq D]
  {M : Matrix D D ℂ}
-- given
  (gauge : D -> ℂ)
  (hgauge : ∀ i, gauge i ≠ 0) :
-- imply
  (1 - kwGaugeConjugate gauge M).det = (1 - M).det := by
-- proof
  apply StatMech.FrontierA.kw_det_one_sub_gaugeConjugate gauge M hgauge

/--
[kw_loopWeight_gaugeConjugate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardGauge.lean)
-/
@[path]
private lemma kw_loopWeight_gaugeConjugate_eq
  [Fintype D]
  [DecidableEq D]
  {n : ℕ}
  [NeZero n]
  {M : Matrix D D ℂ}
-- given
  (gauge : D -> ℂ)
  (hgauge : ∀ i, gauge i ≠ 0)
  (loop : Fin n -> D) :
-- imply
  StatMech.Onsager.ons_loopWeight (kwGaugeConjugate gauge M) loop = StatMech.Onsager.ons_loopWeight M loop := by
-- proof
  apply StatMech.FrontierA.kw_loopWeight_gaugeConjugate gauge M hgauge loop

/--
[kacWard_theta_gauge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardGauge.lean)
-/
@[path]
private lemma kacWard_theta_gauge_eq
  {omega : ℂ}
-- given
  (homega : omega ≠ 0)
  (hI : omega ^ 2 = Complex.I)
  (x : Fin 3 -> ℂ)
  (gauge : (Fin 3 ⊕ Fin 3) -> ℂ)
  (hgauge : ∀ i, gauge i ≠ 0) :
-- imply
  (1 - kwGaugeConjugate gauge (kwThetaTransition omega x)).det = (kwThetaEvenPolynomial x) ^ 2 := by
-- proof
  apply StatMech.FrontierA.kacWard_theta_gauge omega homega hI x gauge hgauge


-- created on 2026-10-23
