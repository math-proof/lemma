import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Def.Topology.Algebra.InfiniteSum.NormalConvergence
open Topology
open scoped ENNReal

variable {X E : Type*} [SeminormedAddCommGroup E]

/-!
# Normal convergence of series of functions

This module defines normal convergence of a series of functions `f : ℕ → X → E`
with values in a seminormed additive commutative group, on a set `S : Set X`,
via the extended-nonnegative-real supremum norm, together with the local version
and the basic API: behaviour on the empty set and for the zero series, and
monotonicity under shrinking the domain, both globally and locally.

The supremum is taken in `ℝ≥0∞`, so unbounded families still have a well-defined
supremum; finiteness of the `ℝ≥0∞` tsum is the convergence condition (`Summable`
is not suitable as the primary predicate for `ℝ≥0∞`, where an infinite sum may
legitimately converge to `∞`).

The declarations live at the root level with the function family first and the
set last, mirroring nearby Mathlib function-series APIs such as
`TendstoUniformlyOn` and `TendstoLocallyUniformlyOn`.
-/


/-- The sup norm over the empty set vanishes. -/
@[simp]
theorem supNormOn_empty (g : X → E) : supNormOn g ∅ = 0 := by
  unfold supNormOn
  rw [iSup_of_empty]
  rfl

/-- The sup norm of the zero function vanishes. -/
@[simp]
theorem supNormOn_zero (S : Set X) : supNormOn (0 : X → E) S = 0 := by
  simp [supNormOn]

/-- The sup norm shrinks when the domain shrinks. -/
theorem supNormOn_mono {S T : Set X} (h : T ⊆ S) (g : X → E) :
    supNormOn g T ≤ supNormOn g S := by
  unfold supNormOn
  apply iSup_mono'
  intro x
  exact ⟨⟨x.1, h x.2⟩, le_rfl⟩

/-- Every function series converges normally on the empty set. -/
@[simp]
theorem convergesNormallyOn_empty (f : ℕ → X → E) : ConvergesNormallyOn f ∅ := by
  simp [ConvergesNormallyOn, supNormOn_empty]

/-- The zero series converges normally on every set. -/
@[simp]
theorem convergesNormallyOn_zero (S : Set X) :
    ConvergesNormallyOn (0 : ℕ → X → E) S := by
  simp [ConvergesNormallyOn, supNormOn_zero]

/-- Normal convergence persists when the domain shrinks. -/
theorem ConvergesNormallyOn.mono {f : ℕ → X → E} {S T : Set X}
    (h : ConvergesNormallyOn f S) (hTS : T ⊆ S) : ConvergesNormallyOn f T := by
  unfold ConvergesNormallyOn at h ⊢
  exact ne_top_of_le_ne_top h (ENNReal.tsum_le_tsum fun n => supNormOn_mono hTS _)

