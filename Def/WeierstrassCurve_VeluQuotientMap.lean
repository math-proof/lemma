import Mathlib
import Def.WeierstrassCurve_Velu

open Polynomial

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)


section QuotientMap

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

noncomputable def veluX (S : Finset (F × F)) (x : F) : F :=
  x + ∑ Q ∈ S, (W.veluT Q.1 Q.2 / (x - Q.1) + W.veluU Q.1 Q.2 / (x - Q.1) ^ 2)

end QuotientMap

end WeierstrassCurve
