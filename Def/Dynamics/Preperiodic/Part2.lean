/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/Preperiodic.lean -/

module

public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Dynamics.PeriodicPts.Defs
public import Lean.Elab.Tactic.Omega
public import Theorem.Dynamics.Preperiodic

@[expose] public section

namespace Function

variable {α : Type*} {f : α → α} {x y z : α} {m n : ℕ}

/-- The setoid whose classes are grand orbits of `f`. -/
def grandOrbitSetoid (f : α → α) : Setoid α where
  r := GrandOrbitRel f
  iseqv := grandOrbitRel_equivalence f

/-- Grand orbit of `x`, viewed as its equivalence class. -/
def grandOrbit (f : α → α) (x : α) : Set α :=
  {y | GrandOrbitRel f x y}

end Function
