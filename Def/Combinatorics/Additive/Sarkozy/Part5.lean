/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Data.Finset.Card
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Tactic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Sequences
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.Data.Finsupp.Basic
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.Algebra.Module.Basic
import Theorem.Combinatorics.Additive.Sarkozy.Part3


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
