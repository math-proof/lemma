-- Carved from Lemma/Definitions/Def_LanglandsTunnell_CubicInduction_IotaTorus.lean: instance decls only.
import Lemma.LanglandsTunnell.CubicInduction_Carrier

set_option autoImplicit false

open IsDedekindDomain NumberField Matrix

noncomputable section

namespace LanglandsTunnell.CubicInduction


section Countable

variable (K : Type*) [Field K] [Countable K]

instance countable_GL2 : Countable (GL (Fin 2) K) :=
  haveI : Countable (Matrix (Fin 2) (Fin 2) K) := inferInstanceAs (Countable (Fin 2 → Fin 2 → K))
  Function.Injective.countable fun _ _ h => Units.ext h

instance countable_mirabolicIndex : Countable (MirabolicIndex K) := by
  unfold MirabolicIndex
  infer_instance

end Countable

end LanglandsTunnell.CubicInduction
end
