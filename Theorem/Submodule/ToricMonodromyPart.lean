module

public import Mathlib
public import Def.HeckeGalois_EichlerShimura
public import Def.ModularCurve_ToricMonodromyPart

public noncomputable section

set_option autoImplicit false

noncomputable section

namespace ModularCurve

variable {G : Type*} [Group G]
  {J : Type*} [AddCommGroup J] [Module HeckeAlg J] [DistribMulAction G J]


public theorem smul_sub_self_mem_toricMonodromyPart {q : ℕ} {I : Subgroup G} {σ : G} (hσ : σ ∈ I) {x : J}
    {m : ℕ} (hm : 0 < m) (hmq : m.Coprime q) (hx : m • x = 0) :
    σ • x - x ∈ toricMonodromyPart (J := J) q I :=
  Submodule.subset_span ⟨σ, hσ, x, ⟨m, hm, hmq, hx⟩, rfl⟩

end ModularCurve

end
