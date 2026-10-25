-- Carved from Lemma/Definitions/Def_AlgebraicGeometry_DoubleComplex.lean: instance decls only.
import Mathlib
import Def.AlgebraicGeometry_DoubleComplex

set_option autoImplicit false

noncomputable section

universe u

namespace DoubleComplex


section E2

variable {R : Type u} [CommRing R] (D : Bounded R)

instance (p q : ℕ) : AddCommGroup (E₂I D p q) :=
  inferInstanceAs (AddCommGroup (_ ⧸ _))
instance (p q : ℕ) : Module R (E₂I D p q) :=
  inferInstanceAs (Module R (_ ⧸ _))
instance (p q : ℕ) : AddCommGroup (E₂II D p q) :=
  inferInstanceAs (AddCommGroup (_ ⧸ _))
instance (p q : ℕ) : Module R (E₂II D p q) :=
  inferInstanceAs (Module R (_ ⧸ _))

end E2

end DoubleComplex

end
