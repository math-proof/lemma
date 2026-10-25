import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

namespace Ihara

def gamma0UnitsHom (N : ℕ) : CongruenceSubgroup.Gamma0 N →* (ZMod N)ˣ :=
  (CongruenceSubgroup.Gamma0Map N).toHomUnits


def gamma0UnitsChar (N : ℕ) :
    Additive (CongruenceSubgroup.Gamma0 N) →+ Additive (ZMod N)ˣ :=
  MonoidHom.toAdditive (gamma0UnitsHom N)

end Ihara
