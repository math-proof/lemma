import Mathlib
import Structure.Dieudonne_DatumAndHonda
import Instance.Dieudonne_WittVectorHom

set_option autoImplicit false

open Function

universe u v w

namespace Deformation

namespace TruncWitt

variable {p : ℕ} [hp : Fact p.Prime] {n : ℕ}
variable {R : Type u} {S : Type v} {T : Type w} [CommRing R] [CommRing S] [CommRing T]

end TruncWitt

section WittHom

variable (R : Type u) [CommRing R] (p : ℕ) [hp : Fact p.Prime] (n : ℕ)
variable (A : Type v) [CommRing A] [Bialgebra R A]

open TruncWitt

noncomputable abbrev comulRingHom : A →+* TensorProduct R A A :=
  (Bialgebra.comulAlgHom R A).toRingHom

section Map

variable {B : Type w} [CommRing B] [Bialgebra R B]

end Map

section CharP

variable [CharP R p]

end CharP

end WittHom

end Deformation
