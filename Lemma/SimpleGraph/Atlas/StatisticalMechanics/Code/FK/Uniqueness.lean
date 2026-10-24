import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.Uniqueness
open Set Filter Topology StatMech StatMech.FK


/--
[fk_unique_of_edgeMarg_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Uniqueness.lean)
-/
@[path]
private lemma fk_unique_of_edgeMarg_eq_eq
  [Fintype E]
  [DecidableEq E]
  {P : ConfigSpace E × ConfigSpace E → ℝ}
  {μ ν : ConfigSpace E → ℝ}
  {A : Set (ConfigSpace E)}
-- given
  (hP : IsMonotoneCouplingFun P μ ν)
  (hmarg : ∀ e : E, edgeMargProb μ e = edgeMargProb ν e)
  (hA : IsIncreasing A) :
-- imply
  eventMassProb μ A = eventMassProb ν A := by
-- proof
  apply StatMech.FK.fk_unique_of_edgeMarg_eq hP hmarg hA

/--
[countable_discontinuities](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Uniqueness.lean)
-/
@[path]
private lemma countable_discontinuities_eq
  [Fintype E]
  [DecidableEq E]
  {a b : ℝ → ℝ}
-- given
  (hb : Monotone b) :
-- imply
  {p : ℝ | ¬ ContinuousAt b p}.Countable := by
-- proof
  apply StatMech.FK.countable_discontinuities hb

/--
[eq_on_continuousAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Uniqueness.lean)
-/
@[path]
private lemma eq_on_continuousAt_eq
  [Fintype E]
  [DecidableEq E]
  {a b : ℝ → ℝ}
  {p : ℝ}
-- given
  (heq_at_cont : ∀ p : ℝ, ContinuousAt b p → a p = b p)
  (hp : ContinuousAt b p) :
-- imply
  a p = b p := by
-- proof
  apply StatMech.FK.eq_on_continuousAt heq_at_cont hp

/--
[countable_edgeMarg_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Uniqueness.lean)
-/
@[path]
private lemma countable_edgeMarg_ne_eq
  [Fintype E]
  [DecidableEq E]
  {a b : ℝ → ℝ}
-- given
  (hb : Monotone b)
  (heq_at_cont : ∀ p : ℝ, ContinuousAt b p → a p = b p) :
-- imply
  {p : ℝ | a p ≠ b p}.Countable := by
-- proof
  apply StatMech.FK.countable_edgeMarg_ne hb heq_at_cont

/--
[phi0_eq_phi1_off_countable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Uniqueness.lean)
-/
@[path]
private lemma phi0_eq_phi1_off_countable_eq
  [Fintype E]
  [DecidableEq E]
  {μ ν : ℝ → ConfigSpace E → ℝ}
  {e : E}
  {P : ℝ → ConfigSpace E × ConfigSpace E → ℝ}
-- given
  (hcoup : ∀ p, IsMonotoneCouplingFun (P p) (μ p) (ν p))
  (hb : Monotone (fun p => edgeMargProb (ν p) e))
  (heq_at_cont : ∀ p : ℝ, ContinuousAt (fun p => edgeMargProb (ν p) e) p → ∀ e' : E, edgeMargProb (μ p) e' = edgeMargProb (ν p) e') :
-- imply
  ∃ S : Set ℝ, S.Countable ∧ ∀ p ∉ S, ∀ {A : Set (ConfigSpace E)}, IsIncreasing A → eventMassProb (μ p) A = eventMassProb (ν p) A := by
-- proof
  apply StatMech.FK.phi0_eq_phi1_off_countable μ ν e P hcoup hb heq_at_cont

/--
[countable_phi_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/Uniqueness.lean)
-/
@[path]
private lemma countable_phi_ne_eq
  [Fintype E]
  [DecidableEq E]
  {μ ν : ℝ → ConfigSpace E → ℝ}
  {e : E}
  {P : ℝ → ConfigSpace E × ConfigSpace E → ℝ}
-- given
  (hcoup : ∀ p, IsMonotoneCouplingFun (P p) (μ p) (ν p))
  (hb : Monotone (fun p => edgeMargProb (ν p) e))
  (heq_at_cont : ∀ p : ℝ, ContinuousAt (fun p => edgeMargProb (ν p) e) p → ∀ e' : E, edgeMargProb (μ p) e' = edgeMargProb (ν p) e') :
-- imply
  {p : ℝ | ∃ A : Set (ConfigSpace E), IsIncreasing A ∧ eventMassProb (μ p) A ≠ eventMassProb (ν p) A}.Countable := by
-- proof
  apply StatMech.FK.countable_phi_ne μ ν e P hcoup hb heq_at_cont


-- created on 2026-10-23
