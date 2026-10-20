/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Normed/Series/NormalConvergence.lean -/

import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

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

open Topology
open scoped ENNReal

variable {X E : Type*} [SeminormedAddCommGroup E]

/-- Supremum norm of `g` on `S`, valued in `ℝ≥0∞`. -/
noncomputable def supNormOn (g : X → E) (S : Set X) : ℝ≥0∞ :=
  ⨆ x : S, ENNReal.ofReal ‖g x‖

/-- Normal convergence of the function series `f` on `S`: the sup-norm series
is finite in `ℝ≥0∞`. -/
def ConvergesNormallyOn (f : ℕ → X → E) (S : Set X) : Prop :=
  ∑' n, supNormOn (f n) S ≠ ∞

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

variable [TopologicalSpace X]

/-- Local normal convergence of the function series `f` on `S`: every `x ∈ S`
has a neighbourhood whose intersection with `S` carries normal convergence. -/
def ConvergesLocallyNormallyOn (f : ℕ → X → E) (S : Set X) : Prop :=
  ∀ x ∈ S, ∃ U ∈ 𝓝 x, ConvergesNormallyOn f (U ∩ S)

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
