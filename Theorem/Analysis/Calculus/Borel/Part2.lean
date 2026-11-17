/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Compactness.DeltaGeneratedSpace
public import Mathlib.Topology.UniformSpace.Uniformizable
public import Def.Analysis.Calculus.Borel.Part2

/-!
# Borel's theorem on arbitrary jets at a point (real line)
-/

public section


namespace Real.Calculus.Borel

open scoped Topology ContDiff

lemma polyBound_nonneg (m : ℕ) : 0 ≤ polyBound m :=
  (Classical.choose_spec
    ((hasCompactSupport_poly m).exists_bound_iteratedFDeriv (contDiff_poly m) m)).1

lemma norm_iteratedFDeriv_poly_le {m i : ℕ} (hi : i ≤ m) (y : ℝ) :
    ‖iteratedFDeriv ℝ i (poly m) y‖ ≤ polyBound m :=
  (Classical.choose_spec
    ((hasCompactSupport_poly m).exists_bound_iteratedFDeriv (contDiff_poly m) m)).2 i hi y

end Real.Calculus.Borel
