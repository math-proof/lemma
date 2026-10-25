/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MacaulayMonomialShadow.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Nat.Find
import Mathlib.Order.Fin.Basic
import Mathlib.Order.Fin.Tuple
import Theorem.Combinatorics.Enumerative.MacaulayMonomialShadow.Part3


namespace MetaMathlibExt

open BigOperators

section

/-- Delete one copy of coordinate `p`. -/
noncomputable def mms_lower (p : ℕ) (a : ℕ →₀ ℕ) : ℕ →₀ ℕ :=
  a.update p (a p - 1)

/-- Add one copy of coordinate `p`. -/
noncomputable def mms_raise (p : ℕ) (a : ℕ →₀ ℕ) : ℕ →₀ ℕ :=
  a.update p (a p + 1)

/-- The one-step lower shadow of a monomial family. -/
noncomputable def mms_shadow (A : Finset (ℕ →₀ ℕ)) : Finset (ℕ →₀ ℕ) :=
  A.biUnion fun a => a.support.image fun i => mms_lower i a

end
end MetaMathlibExt
