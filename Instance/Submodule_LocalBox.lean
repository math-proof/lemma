-- Carved from Lemma/Definitions/Def_Submodule_LocalBox.lean: instance decls only.
import Mathlib
import Lemma.Submodule.FiniteAdeleBox
import Def.QuaternionAlgebra_Order_FiniteIdele

set_option autoImplicit false

open scoped TensorProduct Pointwise Quaternion
open IsDedekindDomain NumberField

noncomputable section

namespace IsDedekindDomain.HeightOneSpectrum

instance instAlgebraRatAdicCompletion (v : HeightOneSpectrum (𝓞 ℚ)) : Algebra ℚ (v.adicCompletion ℚ) :=
  HeightOneSpectrum.instAlgebraAdicCompletion (𝓞 ℚ) ℚ v

instance instModuleRatAdicCompletion (v : HeightOneSpectrum (𝓞 ℚ)) : Module ℚ (v.adicCompletion ℚ) :=
  Algebra.toModule

end IsDedekindDomain.HeightOneSpectrum


end
