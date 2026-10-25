-- Carved from Lemma/Definitions/Def_Mathlib_LinearAlgebra_Countable.lean: instance decls only.
import Mathlib

section


instance (K : Type*) [Field K] [NumberField K] : Countable K :=
  Countable.of_module_finite ℚ K

end
