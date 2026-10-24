import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

namespace Ihara

def gamma0UnitsHom (N : ℕ) : CongruenceSubgroup.Gamma0 N →* (ZMod N)ˣ :=
  (CongruenceSubgroup.Gamma0Map N).toHomUnits

@[simp]
theorem gamma0UnitsHom_coe (N : ℕ) (g : CongruenceSubgroup.Gamma0 N) :
    (gamma0UnitsHom N g : ZMod N) = CongruenceSubgroup.Gamma0Map N g :=
  rfl

def gamma0UnitsChar (N : ℕ) :
    Additive (CongruenceSubgroup.Gamma0 N) →+ Additive (ZMod N)ˣ :=
  MonoidHom.toAdditive (gamma0UnitsHom N)

@[simp]
theorem gamma0UnitsChar_apply (N : ℕ) (g : Additive (CongruenceSubgroup.Gamma0 N)) :
    gamma0UnitsChar N g = Additive.ofMul (gamma0UnitsHom N g.toMul) :=
  rfl

end Ihara
