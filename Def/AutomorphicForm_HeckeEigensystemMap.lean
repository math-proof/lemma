import Def.AutomorphicForm_HeckeEigensystem

open IsDedekindDomain NumberField

namespace AutomorphicForm

namespace HeckeEigensystem

variable {F : Type*} [Field F] [NumberField F] {R : Type*} [CommRing R]
  {S : Type*} [CommRing S]

def map (ι : R →+* S) (Φ : HeckeEigensystem F R) : HeckeEigensystem F S where
  level := Φ.level
  level_ne_bot := Φ.level_ne_bot
  a := fun v => ι (Φ.a v)
  b := fun v => ι (Φ.b v)

end HeckeEigensystem

end AutomorphicForm
