-- Carved from Lemma/Definitions/Def_Dieudonne_WittVectorHom.lean: instance decls only.
import Mathlib
import Lemma.Dieudonne.DatumAndHonda

set_option autoImplicit false

open Function

universe u v w

namespace Deformation

namespace TruncWitt

variable {p : ℕ} [hp : Fact p.Prime] {n : ℕ}
variable {R : Type u} {S : Type v} {T : Type w} [CommRing R] [CommRing S] [CommRing T]

instance instSubsingleton [Subsingleton R] : Subsingleton (TruncatedWittVector p n R) :=
  ⟨fun _ _ => TruncatedWittVector.ext fun _ => Subsingleton.elim _ _⟩

end TruncWitt


end Deformation
