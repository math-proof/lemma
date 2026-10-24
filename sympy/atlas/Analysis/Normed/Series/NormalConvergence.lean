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

/-- Local normal convergence of the function series `f` on `S`: every `x ∈ S`
has a neighbourhood whose intersection with `S` carries normal convergence. -/
def ConvergesLocallyNormallyOn (f : ℕ → X → E) (S : Set X) : Prop :=
  ∀ x ∈ S, ∃ U ∈ 𝓝 x, ConvergesNormallyOn f (U ∩ S)
