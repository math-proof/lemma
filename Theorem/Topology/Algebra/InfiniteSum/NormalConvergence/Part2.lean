import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Def.Topology.Algebra.InfiniteSum.NormalConvergence.Part2
open Topology
open scoped ENNReal

variable {X E : Type*} [SeminormedAddCommGroup E]

variable [TopologicalSpace X]

/-!
# Normal convergence of series of functions

This module defines normal convergence of a series of functions `f : ℕ → X → E`
with values in a seminormed additive commutative group, on a set `S : Set X`,
via the extended-nonnegative-real supremum norm, together with the local version
and the basic API: behaviour on the empty set and for the zero series, and
monotonicity under shrinking the domain, both globally and locally.

The supremum is taken in `ENNReal`, so unbounded families still have a well-defined
supremum; finiteness of the `ENNReal` tsum is the convergence condition (`Summable`
is not suitable as the primary predicate for `ENNReal`, where an infinite sum may
legitimately converge to `∞`).

The declarations live at the root level with the function family first and the
set last, mirroring nearby Mathlib function-series APIs such as
`TendstoUniformlyOn` and `TendstoLocallyUniformlyOn`.
-/


/-- Projection from local normal convergence at a point: at any `x ∈ S`,
some neighbourhood intersected with `S` carries normal convergence. -/
theorem ConvergesLocallyNormallyOn.exists_nhds_inter {f : ℕ → X → E} {S : Set X}
    {x : X} (h : ConvergesLocallyNormallyOn f S) (hx : x ∈ S) :
    ∃ U ∈ 𝓝 x, ConvergesNormallyOn f (U ∩ S) :=
  h x hx

/-- Every function series converges locally normally on the empty set. -/
@[simp]
theorem convergesLocallyNormallyOn_empty (f : ℕ → X → E) :
    ConvergesLocallyNormallyOn f ∅ :=
  fun x hx => absurd hx (Set.notMem_empty x)

/-- The zero series converges locally normally on every set. -/
@[simp]
theorem convergesLocallyNormallyOn_zero (S : Set X) :
    ConvergesLocallyNormallyOn (0 : ℕ → X → E) S := by
  intro x _
  exact ⟨Set.univ, Filter.univ_mem, by simp⟩

/-- Local normal convergence persists when the domain shrinks. -/
theorem ConvergesLocallyNormallyOn.mono {f : ℕ → X → E} {S T : Set X}
    (h : ConvergesLocallyNormallyOn f S) (hTS : T ⊆ S) :
    ConvergesLocallyNormallyOn f T := by
  intro x hx
  obtain ⟨U, hU, hconv⟩ := h x (hTS hx)
  exact ⟨U, hU, hconv.mono (Set.inter_subset_inter (fun x hx => hx) hTS)⟩

