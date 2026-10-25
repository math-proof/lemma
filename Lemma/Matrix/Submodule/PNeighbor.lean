import Mathlib
import sympy.Basic
import Def.LinearAlgebra.Submodule.PNeighbor
open Submodule


namespace Submodule

/--
[arePNeighbors_comm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Submodule/PNeighbor.lean)
-/
@[path]
lemma arePNeighbors_comm
  [CommRing R] [AddCommGroup M] [Module R M]
  {p : ℕ}
  {L₁ L₂ : Submodule R M} :
-- imply
  ArePNeighbors p L₁ L₂ ↔ ArePNeighbors p L₂ L₁ := by
-- proof
  unfold ArePNeighbors
  rw [inf_comm]
  aesop

end Submodule

namespace Submodule

/--
[not_arePNeighbors_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Submodule/PNeighbor.lean)
-/
@[path]
lemma not_arePNeighbors_one
  [CommRing R] [AddCommGroup M] [Module R M]
  {L₁ L₂ : Submodule R M} :
-- imply
  ¬ArePNeighbors 1 L₁ L₂ := by
-- proof
  intro h
  exact Nat.not_prime_one h.1

end Submodule


-- created on 2026-10-20
-- updated on 2026-10-23
