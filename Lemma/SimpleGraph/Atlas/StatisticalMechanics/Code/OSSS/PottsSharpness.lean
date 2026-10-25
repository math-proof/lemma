import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.OSSS.PottsSharpness
open Real Set StatMech StatMech.OSSS StatMech.OSSS.PottsSharpness


/--
[potts_subcritical_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/PottsSharpness.lean)
-/
@[path]
private lemma potts_subcritical_decay_eq
  {q : ℝ}
  {a b rate : ℝ}
  {θ θ' : ℝ → ℝ}
  {pottsCorr : ℝ}
-- given
  (hq : 2 ≤ q)
  (hab : a < b)
  (hrate : 0 < rate)
  (hd : ∀ x ∈ Icc a b, HasDerivAt θ (θ' x) x)
  (hFKineq : ∀ x ∈ Icc a b, rate * θ x ≤ θ' x)
  (hθa : 0 ≤ θ a)
  (hθb : θ b ≤ 1)
  (hES : pottsCorr = (q - 1) / q * θ a) :
-- imply
  0 ≤ pottsCorr ∧ pottsCorr ≤ Real.exp (-(rate * (b - a))) ∧ Real.exp (-(rate * (b - a))) < 1 := by
-- proof
  apply StatMech.OSSS.PottsSharpness.potts_subcritical_decay q hq a b rate hab hrate θ θ' hd hFKineq hθa hθb pottsCorr hES

/--
[potts_subcritical_decay_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/PottsSharpness.lean)
-/
@[path]
private lemma potts_subcritical_decay_box_eq
  {q : ℝ}
  {a b c : ℝ}
  {n : ℕ}
  {θ θ' : ℝ → ℝ}
  {pottsCorr : ℝ}
-- given
  (hq : 2 ≤ q)
  (hab : a < b)
  (hc : 0 < c)
  (hn : 1 ≤ n)
  (hd : ∀ x ∈ Icc a b, HasDerivAt θ (θ' x) x)
  (hFKineq : ∀ x ∈ Icc a b, (c * n) * θ x ≤ θ' x)
  (hθa : 0 ≤ θ a)
  (hθb : θ b ≤ 1)
  (hES : pottsCorr = (q - 1) / q * θ a) :
-- imply
  0 ≤ pottsCorr ∧ pottsCorr ≤ Real.exp (-(c * n * (b - a))) := by
-- proof
  apply StatMech.OSSS.PottsSharpness.potts_subcritical_decay_box q hq a b c n hab hc hn θ θ' hd hFKineq hθa hθb pottsCorr hES

/--
[potts_corr_le_of_fk_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/PottsSharpness.lean)
-/
@[path]
private lemma potts_corr_le_of_fk_decay_eq
  {q : ℝ}
  {c pottsCorr fkCross : ℝ}
-- given
  (hq : 2 ≤ q)
  (hES : pottsCorr = (q - 1) / q * fkCross)
  (hfk_nonneg : 0 ≤ fkCross)
  (hfk_decay : fkCross ≤ Real.exp (-c)) :
-- imply
  0 ≤ pottsCorr ∧ pottsCorr ≤ Real.exp (-c) := by
-- proof
  apply StatMech.OSSS.PottsSharpness.potts_corr_le_of_fk_decay q hq c pottsCorr fkCross hES hfk_nonneg hfk_decay


-- created on 2026-10-23
