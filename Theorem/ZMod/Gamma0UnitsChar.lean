module

public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Def.Gamma0UnitsChar

public section

namespace Ihara


@[simp]
public theorem gamma0UnitsHom_coe (N : ℕ) (g : CongruenceSubgroup.Gamma0 N) :
    (gamma0UnitsHom N g : ZMod N) = CongruenceSubgroup.Gamma0Map N g :=
  rfl


@[simp]
public theorem gamma0UnitsChar_apply (N : ℕ) (g : Additive (CongruenceSubgroup.Gamma0 N)) :
    gamma0UnitsChar N g = Additive.ofMul (gamma0UnitsHom N g.toMul) :=
  rfl

end Ihara
