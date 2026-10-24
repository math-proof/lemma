/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/LinearAlgebra/Submodule/PNeighbor.lean -/


import sympy.atlas.LinearAlgebra.Submodule.PNeighbor
import Lemma.Matrix.Submodule.PNeighbor

namespace Submodule

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

example (p : ℕ) (L₁ L₂ : Submodule R M) :
    ArePNeighbors p L₁ L₂ ↔ ArePNeighbors p L₂ L₁ :=
  arePNeighbors_comm p L₁ L₂

example (L₁ L₂ : Submodule R M) : ¬ArePNeighbors 1 L₁ L₂ :=
  not_arePNeighbors_one L₁ L₂

example (p : ℕ) (L₁ L₂ : Submodule R M) (h : ArePNeighbors p L₁ L₂) :
    Nat.card (L₁ ⧸ Submodule.comap L₁.subtype (L₁ ⊓ L₂)) = p :=
  h.2.1

example (p : ℕ) (L₁ L₂ : Submodule R M) (h : ArePNeighbors p L₁ L₂) :
    Nat.card (L₂ ⧸ Submodule.comap L₂.subtype (L₁ ⊓ L₂)) = p :=
  h.2.2

end Submodule
