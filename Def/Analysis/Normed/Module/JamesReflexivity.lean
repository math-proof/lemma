/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Normed/Module/JamesReflexivity.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Analysis.Normed.Module.DoubleDual
import Lemma.Nat.Closure
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Tactic.Linarith
/-!
# James' reflexivity theorem

This file characterizes reflexive Banach spaces over `ℝ` or `ℂ` by norm attainment of every
continuous linear functional on the closed unit ball.
-/


namespace MathlibExt.Analysis.FunctionalAnalysis.BanachSpaceWanted

open Set Metric

open Filter

def jamesClusterSet {X : Type*} [TopologicalSpace X] (u : ℕ → X) : Set X :=
  {x | MapClusterPt x atTop u}

def jamesClusterHull {X : Type*} [TopologicalSpace X]
    [AddCommGroup X] [Module ℝ X] (u : ℕ → X) : Set X :=
  closedConvexHull ℝ (jamesClusterSet u)

def jamesDualBall (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Set (WeakDual ℝ E) :=
  WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ E) 1

end MathlibExt.Analysis.FunctionalAnalysis.BanachSpaceWanted
