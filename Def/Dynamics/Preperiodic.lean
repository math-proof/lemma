/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/Preperiodic.lean -/

import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Range
import Mathlib.Dynamics.PeriodicPts.Defs
import Lean.Elab.Tactic.Omega


namespace Function

variable {α : Type*} {f : α → α} {x y z : α} {m n : ℕ}

/-!
# Forward and grand orbits

The forward orbit and preperiodicity follow
[Ghioca--Shadgar, arXiv:2607.26044v1](https://arxiv.org/abs/2607.26044v1), line 201.
The grand orbit follows
[Pasten--Silverman, arXiv:2307.12097v2](https://arxiv.org/abs/2307.12097v2), lines 635--661.
Preperiodicity of type `(m, n)` follows
[Sadek--Wafik--Yesin, arXiv:2403.04397v1](https://arxiv.org/abs/2403.04397v1),
lines 193--194.
-/

/-- Forward orbit of `x` under the self-map `f`. -/
def forwardOrbit (f : α → α) (x : α) : Set α :=
  Set.range fun n : ℕ => f^[n] x

/-- A point is preperiodic when its forward orbit is finite. -/
def IsPreperiodicPt (f : α → α) (x : α) : Prop :=
  (forwardOrbit f x).Finite

/-- A strictly preperiodic point is preperiodic but not periodic. -/
def IsStrictlyPreperiodicPt (f : α → α) (x : α) : Prop :=
  IsPreperiodicPt f x ∧ x ∉ periodicPts f

/-- A point is preperiodic of type `(m, n)` when its `m`th iterate has
positive period `n`. -/
def IsPreperiodicPtOfType (f : α → α) (m n : ℕ) (x : α) : Prop :=
  0 < n ∧ f^[m + n] x = f^[m] x

/-- Two points lie in the same grand orbit when two of their forward iterates agree. -/
def GrandOrbitRel (f : α → α) (x y : α) : Prop :=
  ∃ m n : ℕ, f^[m] x = f^[n] y

end Function
