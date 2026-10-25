/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/Preperiodic.lean -/

import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Range
import Mathlib.Dynamics.PeriodicPts.Defs
import Lean.Elab.Tactic.Omega
import Theorem.Dynamics.Preperiodic


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
