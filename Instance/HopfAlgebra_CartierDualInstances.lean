-- Carved from Lemma/Definitions/Def_HopfAlgebra_CartierDualInstances.lean: instance decls only.
import Mathlib
set_option autoImplicit false

namespace CartierDual

universe u v

section
variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Bialgebra R A] [Module.Finite R A] [Module.Free R A]

instance instIsCocommViaBialgebra :
    @Coalgebra.IsCocomm R (CartierDual R A) _ _ _ (@Bialgebra.toCoalgebra R (CartierDual R A) _ _ (instBialgebra R A)) :=
  instIsCocomm R A

instance instModuleFiniteViaBialgebra :
    @Module.Finite R (CartierDual R A) _ _ (@Algebra.toModule R (CartierDual R A) _ _ (@Bialgebra.toAlgebra R (CartierDual R A) _ _ (instBialgebra R A))) :=
  instModuleFinite R A

instance instModuleFreeViaBialgebra :
    @Module.Free R (CartierDual R A) _ _ (@Algebra.toModule R (CartierDual R A) _ _ (@Bialgebra.toAlgebra R (CartierDual R A) _ _ (instBialgebra R A))) :=
  instModuleFree R A

end


end CartierDual
