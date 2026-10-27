import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.OSSS.SharpnessFK
open Finset Real Set StatMech StatMech.OSSS StatMech.OSSS.SharpnessFK


/--
[var_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/SharpnessFK.lean)
-/
@[path]
private lemma var_indicator_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {f : ConfigSpace E → ℝ}
-- given
  (hf : ∀ ω, f ω = 0 ∨ f ω = 1) :
-- imply
  var ν f = expect ν f * (1 - expect ν f) := by
-- proof
  apply StatMech.OSSS.SharpnessFK.var_indicator f hf

/--
[indicator_zero_or_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/SharpnessFK.lean)
-/
@[path]
private lemma indicator_zero_or_one_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {A : Set (ConfigSpace E)}
  {ω : ConfigSpace E} :
-- imply
  A.indicator (fun _ => (1 : ℝ)) ω = 0 ∨ A.indicator (fun _ => (1 : ℝ)) ω = 1 := by
-- proof
  apply StatMech.OSSS.SharpnessFK.indicator_zero_or_one A ω

/--
[var_eventIndicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/SharpnessFK.lean)
-/
@[path]
private lemma var_eventIndicator_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {A : Set (ConfigSpace E)} :
-- imply
  var ν (A.indicator (fun _ => (1 : ℝ))) = expect ν (A.indicator (fun _ => (1 : ℝ))) * (1 - expect ν (A.indicator (fun _ => (1 : ℝ)))) := by
-- proof
  apply StatMech.OSSS.SharpnessFK.var_eventIndicator A

/--
[covSum_ge_of_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/SharpnessFK.lean)
-/
@[path]
private lemma covSum_ge_of_indicator_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  [Fintype κ]
  [Nonempty κ]
  {A : Set (ConfigSpace E)}
  {T : κ → DecisionTree E}
  {R : κ → E → ℝ}
  {c₀ : ℝ}
  {D : ℝ}
-- given
  (hν : IsProbWeight ν)
  (hA : IsIncreasing A)
  (hT : ∀ k, (T k).evalR = A.indicator (fun _ => (1 : ℝ)))
  (hR : ∀ k e, reveal ν (T k) e ≤ R k e)
  (hc₀nn : 0 ≤ c₀)
  (hc₀ : ∀ e, c₀ ≤ ν e true * ν e false)
  (hDnn : 0 ≤ D)
  (hD : ∀ e, (∑ k, R k e) ≤ D) :
-- imply
  (Fintype.card κ : ℝ) * c₀ * (expect ν (A.indicator (fun _ => (1 : ℝ))) * (1 - expect ν (A.indicator (fun _ => (1 : ℝ))))) ≤ D * ∑ e, cov ν (coordI e) (A.indicator (fun _ => (1 : ℝ))) := by
-- proof
  apply StatMech.OSSS.SharpnessFK.covSum_ge_of_indicator hν hA T hT R hR c₀ hc₀nn hc₀ D hDnn hD

/--
[gronwall_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/SharpnessFK.lean)
-/
@[path]
private lemma gronwall_lower_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {a b lam : ℝ}
  {f f' : ℝ → ℝ}
-- given
  (hab : a ≤ b)
  (hd : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
  (hineq : ∀ x ∈ Icc a b, lam * f x ≤ f' x) :
-- imply
  Real.exp (lam * (b - a)) * f a ≤ f b := by
-- proof
  apply StatMech.OSSS.SharpnessFK.gronwall_lower a b lam hab f f' hd hineq

/--
[differential_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/SharpnessFK.lean)
-/
@[path]
private lemma differential_inequality_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {n : ℕ}
  {c₀ cR D θ θ' S : ℝ}
-- given
  (hD : 0 < D)
  (hcov : (n : ℝ) * c₀ * (θ * (1 - θ)) ≤ D * S)
  (hRusso : cR * S ≤ θ')
  (hcR : 0 ≤ cR) :
-- imply
  (n : ℝ) * c₀ * cR / D * (θ * (1 - θ)) ≤ θ' := by
-- proof
  apply StatMech.OSSS.SharpnessFK.differential_inequality n c₀ cR D θ θ' S hD hcov hRusso hcR

/--
[subcritical_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/SharpnessFK.lean)
-/
@[path]
private lemma subcritical_decay_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {a b rate : ℝ}
  {θn θn' : ℝ → ℝ}
-- given
  (hab : a < b)
  (hrate : 0 < rate)
  (hd : ∀ x ∈ Icc a b, HasDerivAt θn (θn' x) x)
  (hineq : ∀ x ∈ Icc a b, rate * θn x ≤ θn' x)
  (hθa : 0 ≤ θn a)
  (hθb : θn b ≤ 1) :
-- imply
  0 ≤ θn a ∧ θn a ≤ Real.exp (-(rate * (b - a))) ∧ Real.exp (-(rate * (b - a))) < 1 := by
-- proof
  apply StatMech.OSSS.SharpnessFK.subcritical_decay a b rate hab hrate θn θn' hd hineq hθa hθb

/--
[subcritical_decay_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/SharpnessFK.lean)
-/
@[path]
private lemma subcritical_decay_box_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {a b c : ℝ}
  {n : ℕ}
  {θn θn' : ℝ → ℝ}
-- given
  (hab : a < b)
  (hc : 0 < c)
  (hn : 1 ≤ n)
  (hd : ∀ x ∈ Icc a b, HasDerivAt θn (θn' x) x)
  (hineq : ∀ x ∈ Icc a b, (c * n) * θn x ≤ θn' x)
  (hθa : 0 ≤ θn a)
  (hθb : θn b ≤ 1) :
-- imply
  θn a ≤ Real.exp (-(c * n * (b - a))) := by
-- proof
  apply StatMech.OSSS.SharpnessFK.subcritical_decay_box a b c n hab hc hn θn θn' hd hineq hθa hθb

/--
[potts_decay_of_fk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/SharpnessFK.lean)
-/
@[path]
private lemma potts_decay_of_fk_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
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
  apply StatMech.OSSS.SharpnessFK.potts_decay_of_fk q hq c pottsCorr fkCross hES hfk_nonneg hfk_decay


-- created on 2026-10-23
