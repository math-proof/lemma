import Mathlib
import sympy.Basic
import sympy.atlas.LinearAlgebra.Submodule.PNeighbor
open Submodule


/--
[arePNeighbors_comm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Submodule/PNeighbor.lean)
-/
@[path]
private lemma arePNeighbors_comm_eq
  [CommRing R] [AddCommGroup M] [Module R M]
  {p : ℕ}
  {L₁ L₂ : Submodule R M} :
-- imply
  ArePNeighbors p L₁ L₂ ↔ ArePNeighbors p L₂ L₁ := by
-- proof
  apply Submodule.arePNeighbors_comm p L₁ L₂

/--
[not_arePNeighbors_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Submodule/PNeighbor.lean)
-/
@[path]
private lemma not_arePNeighbors_one_eq
  [CommRing R] [AddCommGroup M] [Module R M]
  {L₁ L₂ : Submodule R M} :
-- imply
  ¬ArePNeighbors 1 L₁ L₂ := by
-- proof
  apply Submodule.not_arePNeighbors_one L₁ L₂


-- created on 2026-10-20
