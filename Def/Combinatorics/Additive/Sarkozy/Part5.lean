/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

module

public import Mathlib.Data.Finset.Card
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.InnerProductSpace.MeanErgodic
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Dynamics.BirkhoffSum.Basic
public import Mathlib.Dynamics.BirkhoffSum.Average
public import Mathlib.Topology.Algebra.LinearMapCompletion
public import Mathlib.Topology.Algebra.Module.Basic
public import Theorem.Combinatorics.Additive.Sarkozy.Part3

@[expose] public section

namespace MathlibExt.Combinatorics.Additive.SarkozyWanted

open scoped InnerProductSpace

/-- The GNS core structure from `γ`. -/
@[instance_reducible]
noncomputable def sarkozyToepCore (γ : ℤ → ℝ) (hsymm : ∀ d, γ (-d) = γ d)
    (hpos : ∀ s : Finset ℤ, ∀ c : ℤ → ℝ,
      0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * c j * γ (i - j)) :
    PreInnerProductSpace.Core ℝ (sarkozyToep γ) where
  inner c d := sarkozyToepInnerAux γ c d
  conj_inner_symm c d := sarkozyToepInnerAux_symm γ hsymm c d
  re_inner_nonneg c := sarkozyToepInnerAux_nonneg γ hpos c
  add_left c₁ c₂ d := sarkozyToepInnerAux_add_left γ c₁ c₂ d
  smul_left c d r := sarkozyToepInnerAux_smul_left γ r c d

@[instance_reducible]
noncomputable def sarkozyToep_seminormed (γ : ℤ → ℝ)
    (hsymm : ∀ d, γ (-d) = γ d)
    (hpos : ∀ s : Finset ℤ, ∀ c : ℤ → ℝ,
      0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * c j * γ (i - j)) :
    SeminormedAddCommGroup (sarkozyToep γ) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup
    (c := sarkozyToepCore γ hsymm hpos)

@[instance_reducible]
noncomputable def sarkozyToep_innerProd (γ : ℤ → ℝ)
    (hsymm : ∀ d, γ (-d) = γ d)
    (hpos : ∀ s : Finset ℤ, ∀ c : ℤ → ℝ,
      0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * c j * γ (i - j)) := by
  letI := sarkozyToep_seminormed γ hsymm hpos
  exact InnerProductSpace.ofCore (sarkozyToepCore γ hsymm hpos)

/-- The forward shift on the type synonym. -/
noncomputable def sarkozyShift (γ : ℤ → ℝ) :
    sarkozyToep γ →ₗ[ℝ] sarkozyToep γ :=
  Finsupp.lmapDomain ℝ ℝ (fun i : ℤ => i + 1)

/-- The shift as a linear isometry of the synonym (a real linear isometry). -/
noncomputable def sarkozyShiftIso (γ : ℤ → ℝ)
    (hsymm : ∀ d, γ (-d) = γ d)
    (hpos : ∀ s : Finset ℤ, ∀ c : ℤ → ℝ,
      0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * c j * γ (i - j)) := by
  letI := sarkozyToep_seminormed γ hsymm hpos
  letI := sarkozyToep_innerProd γ hsymm hpos
  refine @LinearMap.isometryOfInner ℝ (sarkozyToep γ) _ _ _ (sarkozyToep γ) _ _
    (sarkozyShift γ) (fun c d => ?_)
  have e1 : ∀ c : sarkozyToep γ, ((sarkozyShift γ) c : ℤ →₀ ℝ)
      = Finsupp.mapDomain (fun i : ℤ => i + 1) (c : ℤ →₀ ℝ) :=
    fun c => rfl
  have hAux : sarkozyToepInnerAux γ ((sarkozyShift γ) c) ((sarkozyShift γ) d)
      = sarkozyToepInnerAux γ c d := by
    rw [e1 c, e1 d]
    exact sarkozyShift_inner_aux γ _ _
  exact hAux

end MathlibExt.Combinatorics.Additive.SarkozyWanted
