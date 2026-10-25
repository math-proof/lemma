/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/LaplaceTransform/Basic.lean -/

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-!
# One-sided Laplace transform

This file defines the convergence predicate, the one-sided Laplace transform, and the
packaged `HasLaplace` relation, following Mathlib's `MellinConvergent` / `mellin` /
`HasMellin` pattern with the domain restricted to the open ray `Set.Ioi 0`.

This stage provides only the basic definitions; further API is out of scope.

## Main definitions

* `LaplaceConvergent`
* `laplace`
* `HasLaplace`
-/


/-- Laplace convergence: the one-sided Laplace integrand is integrable on `Set.Ioi 0`.

ATLAS `NumberTheoryI` Definition 16.9 introduces the Laplace transform for real-valued
functions; here functions are complex-valued (or complex Banach-valued), and the source's
real-valued case is covered by coercion. -/
def LaplaceConvergent (f : ℝ → E) (s : ℂ) : Prop :=
  IntegrableOn (fun t : ℝ => Complex.exp (-s * (t : ℂ)) • f t) (Set.Ioi 0)

/-- One-sided Laplace transform, defined unconditionally as the set integral over
`Set.Ioi 0`; no convergence hypothesis is imposed here (see `LaplaceConvergent`). -/
noncomputable def laplace (f : ℝ → E) (s : ℂ) : E :=
  ∫ t : ℝ in Set.Ioi 0, Complex.exp (-s * (t : ℂ)) • f t

/-- `HasLaplace f s v` packages Laplace convergence at `s` with the value
`laplace f s`. -/
def HasLaplace (f : ℝ → E) (s : ℂ) (v : E) : Prop :=
  LaplaceConvergent f s ∧ laplace f s = v

