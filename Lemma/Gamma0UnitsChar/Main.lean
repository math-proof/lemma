import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Def.Gamma0UnitsChar

namespace Ihara


@[simp]
theorem gamma0UnitsHom_coe (N : ℕ) (g : CongruenceSubgroup.Gamma0 N) :
    (gamma0UnitsHom N g : ZMod N) = CongruenceSubgroup.Gamma0Map N g :=
  rfl


@[simp]
theorem gamma0UnitsChar_apply (N : ℕ) (g : Additive (CongruenceSubgroup.Gamma0 N)) :
    gamma0UnitsChar N g = Additive.ofMul (gamma0UnitsHom N g.toMul) :=
  rfl

end Ihara
