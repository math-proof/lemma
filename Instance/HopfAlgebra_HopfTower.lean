-- Carved from Lemma/Definitions/Def_HopfAlgebra_HopfTower.lean: instance decls only.
import Mathlib
import Instance.HopfAlgebra_HopfKerHopf
import Class.HopfAlgebra_HopfTower

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped TensorProduct
open Coalgebra WithConv

universe u v w x

namespace HopfAlgebra

namespace IsHopfTower

variable (k : Type u) (A : Type v) (C : Type w) [CommRing k] [CommRing A] [CommRing C]

instance refl : IsHopfTower k C C where
  comul_algebraMap c := by
    rw [Algebra.algebraMap_self, RingHom.id_apply]
    conv_lhs => rw [← (ℛ k c).eq]
    rw [← (ℛ k c).eq, map_sum]
    simp
  counit_algebraMap c := by simp

variable [IsHopfTower k A C]

end IsHopfTower


end HopfAlgebra
