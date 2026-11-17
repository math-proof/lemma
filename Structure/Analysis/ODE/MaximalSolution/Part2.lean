/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.ODE.Basic
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Set.Piecewise
public import Mathlib.Topology.Sequences
public import Theorem.Analysis.ODE.MaximalSolution
public section

open Filter Function Metric Set
open scoped NNReal Topology

/-!
# Maximal solutions of ordinary differential equations

This file proves global existence for continuous vector fields that are globally Lipschitz in the
state variable, and constructs maximal solutions for locally Lipschitz vector fields on open
subsets of spacetime.  The latter solutions eventually leave every compact subset at each finite
or infinite end of their interval of definition.
-/


namespace ODE.MaximalSolutionWanted

structure OdeMaximalSolutionOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set (ℝ × E)) (f : ℝ × E → E) (I : Set ℝ) (x : ℝ → E) : Prop where
  isOpen : IsOpen I
  ordConnected : I.OrdConnected
  graph_mem : ∀ t ∈ I, (t, x t) ∈ U
  hasDerivAt : ∀ t ∈ I, HasDerivAt x (f (t, x t)) t

structure OdeMaximalCandidate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set (ℝ × E)) (f : ℝ × E → E) (t₀ : ℝ) (x₀ : E) where
  I : Set ℝ
  x : ℝ → E
  solution : OdeMaximalSolutionOn U f I x
  mem_domain : t₀ ∈ I
  initial : x t₀ = x₀

end ODE.MaximalSolutionWanted
