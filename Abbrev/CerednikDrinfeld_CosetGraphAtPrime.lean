import Instance.Submodule_LocalBox
import Class.CerednikDrinfeld_MumfordPeriod

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

noncomputable section

namespace CerednikDrinfeld.CosetGraph

variable {a b : ℚ}

abbrev Loc (a b : ℚ) (v : HeightOneSpectrum (𝓞 ℚ)) : Type := ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ

end CerednikDrinfeld.CosetGraph

end
