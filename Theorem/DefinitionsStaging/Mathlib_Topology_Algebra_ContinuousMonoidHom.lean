module

public import Mathlib
public import Def.Mathlib_Topology_Algebra_Module_Quotient
public import Def.Mathlib_Topology_Algebra_ContinuousMonoidHom

public section

section

theorem ContinuousMulEquiv.coe_toHomeomorph {M N : Type*} [TopologicalSpace M]
    [TopologicalSpace N] [CommMonoid M] [CommMonoid N]
    (f : M ≃ₜ* N) : f.toHomeomorph = ⇑f := rfl

end
