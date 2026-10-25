import Mathlib
import Def.HeckeGalois_EichlerShimura

set_option autoImplicit false

noncomputable section

namespace ModularCurve

variable {G : Type*} [Group G]
  {J : Type*} [AddCommGroup J] [Module HeckeAlg J] [DistribMulAction G J]

def toricMonodromyPart (q : ℕ) (I : Subgroup G) : Submodule HeckeAlg J :=
  Submodule.span HeckeAlg
    {y : J | ∃ σ ∈ I, ∃ x : J, (∃ m : ℕ, 0 < m ∧ m.Coprime q ∧ m • x = 0) ∧ y = σ • x - x}

end ModularCurve

end
