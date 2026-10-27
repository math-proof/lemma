import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.PressureDiff
open Set Filter Topology StatMech StatMech.FK


/--
[pressureRightDeriv_monotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PressureDiff.lean)
-/
@[path]
private lemma pressureRightDeriv_monotone_eq
  {g : ℝ → ℝ}
-- given
  (hg : ConvexOn ℝ univ g) :
-- imply
  Monotone (pressureRightDeriv g) := by
-- proof
  apply StatMech.FK.pressureRightDeriv_monotone hg

/--
[pressureLeftDeriv_monotone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PressureDiff.lean)
-/
@[path]
private lemma pressureLeftDeriv_monotone_eq
  {g : ℝ → ℝ}
-- given
  (hg : ConvexOn ℝ univ g) :
-- imply
  Monotone (pressureLeftDeriv g) := by
-- proof
  apply StatMech.FK.pressureLeftDeriv_monotone hg

/--
[pressureLeftDeriv_le_rightDeriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PressureDiff.lean)
-/
@[path]
private lemma pressureLeftDeriv_le_rightDeriv_eq
  {g : ℝ → ℝ}
  {x : ℝ}
-- given
  (hg : ConvexOn ℝ univ g) :
-- imply
  pressureLeftDeriv g x ≤ pressureRightDeriv g x := by
-- proof
  apply StatMech.FK.pressureLeftDeriv_le_rightDeriv hg x

/--
[pressureRightDeriv_le_leftDeriv_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PressureDiff.lean)
-/
@[path]
private lemma pressureRightDeriv_le_leftDeriv_of_lt_eq
  {g : ℝ → ℝ}
  {z x : ℝ}
-- given
  (hg : ConvexOn ℝ univ g)
  (hzx : z < x) :
-- imply
  pressureRightDeriv g z ≤ pressureLeftDeriv g x := by
-- proof
  apply StatMech.FK.pressureRightDeriv_le_leftDeriv_of_lt hg hzx

/--
[pressureLeftDeriv_eq_rightDeriv_of_continuousAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PressureDiff.lean)
-/
@[path]
private lemma pressureLeftDeriv_eq_rightDeriv_of_continuousAt_eq
  {g : ℝ → ℝ}
  {x : ℝ}
-- given
  (hg : ConvexOn ℝ univ g)
  (hc : ContinuousAt (pressureRightDeriv g) x) :
-- imply
  pressureLeftDeriv g x = pressureRightDeriv g x := by
-- proof
  apply StatMech.FK.pressureLeftDeriv_eq_rightDeriv_of_continuousAt hg hc

/--
[countable_leftDeriv_ne_rightDeriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PressureDiff.lean)
-/
@[path]
private lemma countable_leftDeriv_ne_rightDeriv_eq
  {g : ℝ → ℝ}
-- given
  (hg : ConvexOn ℝ univ g) :
-- imply
  {x : ℝ | pressureLeftDeriv g x ≠ pressureRightDeriv g x}.Countable := by
-- proof
  apply StatMech.FK.countable_leftDeriv_ne_rightDeriv hg

/--
[pressure_convex_countable_density_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PressureDiff.lean)
-/
@[path]
private lemma pressure_convex_countable_density_ne_eq
  [Fintype E]
  [DecidableEq E]
  {g : ℝ → ℝ}
  {μ ν : ℝ → ConfigSpace E → ℝ}
  {e : E}
-- given
  (hg : ConvexOn ℝ univ g)
  (ha_eq : ∀ p, edgeMargProb (μ p) e = pressureLeftDeriv g p)
  (hb_eq : ∀ p, edgeMargProb (ν p) e = pressureRightDeriv g p) :
-- imply
  {p : ℝ | edgeMargProb (μ p) e ≠ edgeMargProb (ν p) e}.Countable := by
-- proof
  apply StatMech.FK.pressure_convex_countable_density_ne g hg μ ν e ha_eq hb_eq

/--
[fk_uniqueness_of_pressure_convex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PressureDiff.lean)
-/
@[path]
private lemma fk_uniqueness_of_pressure_convex_eq
  [Fintype E]
  [DecidableEq E]
  {g : ℝ → ℝ}
  {μ ν : ℝ → ConfigSpace E → ℝ}
  {e : E}
  {P : ℝ → ConfigSpace E × ConfigSpace E → ℝ}
-- given
  (hg : ConvexOn ℝ univ g)
  (hcoup : ∀ p, IsMonotoneCouplingFun (P p) (μ p) (ν p))
  (hb_eq : ∀ p, edgeMargProb (ν p) e = pressureRightDeriv g p)
  (heq_at_cont : ∀ p : ℝ, ContinuousAt (fun p => edgeMargProb (ν p) e) p → ∀ e' : E, edgeMargProb (μ p) e' = edgeMargProb (ν p) e') :
-- imply
  ∃ S : Set ℝ, S.Countable ∧ ∀ p ∉ S, ∀ {A : Set (ConfigSpace E)}, IsIncreasing A → eventMassProb (μ p) A = eventMassProb (ν p) A := by
-- proof
  apply StatMech.FK.fk_uniqueness_of_pressure_convex g hg μ ν e P hcoup hb_eq heq_at_cont

/--
[countable_phi_ne_of_pressure_convex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PressureDiff.lean)
-/
@[path]
private lemma countable_phi_ne_of_pressure_convex_eq
  [Fintype E]
  [DecidableEq E]
  {g : ℝ → ℝ}
  {μ ν : ℝ → ConfigSpace E → ℝ}
  {e : E}
  {P : ℝ → ConfigSpace E × ConfigSpace E → ℝ}
-- given
  (hg : ConvexOn ℝ univ g)
  (hcoup : ∀ p, IsMonotoneCouplingFun (P p) (μ p) (ν p))
  (hb_eq : ∀ p, edgeMargProb (ν p) e = pressureRightDeriv g p)
  (heq_at_cont : ∀ p : ℝ, ContinuousAt (fun p => edgeMargProb (ν p) e) p → ∀ e' : E, edgeMargProb (μ p) e' = edgeMargProb (ν p) e') :
-- imply
  {p : ℝ | ∃ A : Set (ConfigSpace E), IsIncreasing A ∧ eventMassProb (μ p) A ≠ eventMassProb (ν p) A}.Countable := by
-- proof
  apply StatMech.FK.countable_phi_ne_of_pressure_convex g hg μ ν e P hcoup hb_eq heq_at_cont


-- created on 2026-10-23
