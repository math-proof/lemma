import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.FKUniquenessDensity
open Set Filter Topology StatMech StatMech.FK


/--
[fud_eq_at_continuousAt_of_convex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessDensity.lean)
-/
@[path]
private lemma fud_eq_at_continuousAt_of_convex_eq
  {a b g : ℝ → ℝ}
  {p : ℝ}
-- given
  (hg : ConvexOn ℝ univ g)
  (ha_eq : ∀ p, a p = pressureLeftDeriv g p)
  (hb_eq : ∀ p, b p = pressureRightDeriv g p)
  (hp : ContinuousAt b p) :
-- imply
  a p = b p := by
-- proof
  apply StatMech.FK.fud_eq_at_continuousAt_of_convex hg ha_eq hb_eq hp

/--
[fud_heq_at_cont_of_convexPerEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessDensity.lean)
-/
@[path]
private lemma fud_heq_at_cont_of_convexPerEdge_eq
  [Fintype E]
  [DecidableEq E]
  {μ ν : ℝ → ConfigSpace E → ℝ}
  {e : E}
  {g : E → ℝ → ℝ}
-- given
  (hg : ∀ e', ConvexOn ℝ univ (g e'))
  (ha_eq : ∀ e' p, edgeMargProb (μ p) e' = pressureLeftDeriv (g e') p)
  (hb_eq : ∀ e' p, edgeMargProb (ν p) e' = pressureRightDeriv (g e') p)
  (hlink : ∀ p : ℝ, ContinuousAt (fun p => edgeMargProb (ν p) e) p → ∀ e' : E, ContinuousAt (fun p => edgeMargProb (ν p) e') p) :
-- imply
  ∀ p : ℝ, ContinuousAt (fun p => edgeMargProb (ν p) e) p → ∀ e' : E, edgeMargProb (μ p) e' = edgeMargProb (ν p) e' := by
-- proof
  apply StatMech.FK.fud_heq_at_cont_of_convexPerEdge μ ν e g hg ha_eq hb_eq hlink

/--
[fud_heq_at_cont_of_homogeneous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessDensity.lean)
-/
@[path]
private lemma fud_heq_at_cont_of_homogeneous_eq
  [Fintype E]
  [DecidableEq E]
  {μ ν : ℝ → ConfigSpace E → ℝ}
  {e : E}
  {a b g : ℝ → ℝ}
-- given
  (hg : ConvexOn ℝ univ g)
  (ha_hom : ∀ e' p, edgeMargProb (μ p) e' = a p)
  (hb_hom : ∀ e' p, edgeMargProb (ν p) e' = b p)
  (ha_eq : ∀ p, a p = pressureLeftDeriv g p)
  (hb_eq : ∀ p, b p = pressureRightDeriv g p) :
-- imply
  ∀ p : ℝ, ContinuousAt (fun p => edgeMargProb (ν p) e) p → ∀ e' : E, edgeMargProb (μ p) e' = edgeMargProb (ν p) e' := by
-- proof
  apply StatMech.FK.fud_heq_at_cont_of_homogeneous μ ν e hg ha_hom hb_hom ha_eq hb_eq

/--
[fud_countable_phi_ne_of_convexPerEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessDensity.lean)
-/
@[path]
private lemma fud_countable_phi_ne_of_convexPerEdge_eq
  [Fintype E]
  [DecidableEq E]
  {μ ν : ℝ → ConfigSpace E → ℝ}
  {e : E}
  {P : ℝ → ConfigSpace E × ConfigSpace E → ℝ}
  {g : E → ℝ → ℝ}
-- given
  (hcoup : ∀ p, IsMonotoneCouplingFun (P p) (μ p) (ν p))
  (hb : Monotone (fun p => edgeMargProb (ν p) e))
  (hg : ∀ e', ConvexOn ℝ univ (g e'))
  (ha_eq : ∀ e' p, edgeMargProb (μ p) e' = pressureLeftDeriv (g e') p)
  (hb_eq : ∀ e' p, edgeMargProb (ν p) e' = pressureRightDeriv (g e') p)
  (hlink : ∀ p : ℝ, ContinuousAt (fun p => edgeMargProb (ν p) e) p → ∀ e' : E, ContinuousAt (fun p => edgeMargProb (ν p) e') p) :
-- imply
  {p : ℝ | ∃ A : Set (ConfigSpace E), IsIncreasing A ∧ eventMassProb (μ p) A ≠ eventMassProb (ν p) A}.Countable := by
-- proof
  apply StatMech.FK.fud_countable_phi_ne_of_convexPerEdge μ ν e P hcoup hb g hg ha_eq hb_eq hlink

/--
[fud_countable_phi_ne_of_homogeneous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessDensity.lean)
-/
@[path]
private lemma fud_countable_phi_ne_of_homogeneous_eq
  [Fintype E]
  [DecidableEq E]
  {μ ν : ℝ → ConfigSpace E → ℝ}
  {e : E}
  {P : ℝ → ConfigSpace E × ConfigSpace E → ℝ}
  {a b g : ℝ → ℝ}
-- given
  (hcoup : ∀ p, IsMonotoneCouplingFun (P p) (μ p) (ν p))
  (hb_mono : Monotone (fun p => edgeMargProb (ν p) e))
  (hg : ConvexOn ℝ univ g)
  (ha_hom : ∀ e' p, edgeMargProb (μ p) e' = a p)
  (hb_hom : ∀ e' p, edgeMargProb (ν p) e' = b p)
  (ha_eq : ∀ p, a p = pressureLeftDeriv g p)
  (hb_eq : ∀ p, b p = pressureRightDeriv g p) :
-- imply
  {p : ℝ | ∃ A : Set (ConfigSpace E), IsIncreasing A ∧ eventMassProb (μ p) A ≠ eventMassProb (ν p) A}.Countable := by
-- proof
  apply StatMech.FK.fud_countable_phi_ne_of_homogeneous μ ν e P hcoup hb_mono hg ha_hom hb_hom ha_eq hb_eq

/--
[fud_norm_rightDeriv_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessDensity.lean)
-/
@[path]
private lemma fud_norm_rightDeriv_zero_eq
  [Fintype E]
  [DecidableEq E] :
-- imply
  pressureRightDeriv (fun x : ℝ => ‖x‖) 0 = 1 := by
-- proof
  apply StatMech.FK.fud_norm_rightDeriv_zero

/--
[fud_norm_leftDeriv_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessDensity.lean)
-/
@[path]
private lemma fud_norm_leftDeriv_zero_eq
  [Fintype E]
  [DecidableEq E] :
-- imply
  pressureLeftDeriv (fun x : ℝ => ‖x‖) 0 = -1 := by
-- proof
  apply StatMech.FK.fud_norm_leftDeriv_zero

/--
[fud_homogeneous_datum_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessDensity.lean)
-/
@[path]
private lemma fud_homogeneous_datum_nonvacuous_eq
  [Fintype E]
  [DecidableEq E] :
-- imply
  ∃ g : ℝ → ℝ, ConvexOn ℝ univ g ∧ pressureLeftDeriv g 0 ≠ pressureRightDeriv g 0 := by
-- proof
  apply StatMech.FK.fud_homogeneous_datum_nonvacuous


-- created on 2026-10-23
