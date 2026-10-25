-- Carved from Lemma/Definitions/Def_Dieudonne_WittHomColimit.lean: instance decls only.
import Mathlib
import Lemma.Dieudonne.DatumAndHonda
import Instance.Dieudonne_WittVectorHom
import Lemma.Dieudonne.WittHomColimit

set_option autoImplicit false

open Function

universe u v w

namespace Deformation


section WittHom

variable {R : Type u} [CommRing R] {p : ℕ} [hp : Fact p.Prime] {n m l : ℕ}
variable {A : Type v} [CommRing A] [Bialgebra R A]

open TruncWitt

instance wittHomShiftLE_directedSystem :
    DirectedSystem (fun n => ↥(wittHom R p n A)) fun _ _ h => wittHomShiftLE R p A h where
  map_self _ x := wittHomShiftLE_refl x
  map_map _ _ _ h₁ h₂ x := wittHomShiftLE_shiftLE h₁ h₂ x

end WittHom

section Colimit

variable (R : Type u) [CommRing R] (p : ℕ) [hp : Fact p.Prime]
variable (A : Type v) [CommRing A] [Bialgebra R A]

namespace DieudonneModule

noncomputable instance instAddCommGroup : AddCommGroup (DieudonneModule R p A) :=
  inferInstanceAs (AddCommGroup
    (AddCommGroup.DirectLimit (fun n => ↥(wittHom R p n A)) fun _ _ h => wittHomShiftLE R p A h))

noncomputable instance instInhabited : Inhabited (DieudonneModule R p A) := ⟨0⟩

variable {R p A}
variable {n m : ℕ}


end DieudonneModule

end Colimit


end Deformation
