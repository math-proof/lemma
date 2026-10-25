-- Carved from Lemma/Definitions/Def_Dieudonne_UnipotentWittCovector.lean: instance decls only.
import Mathlib
import Lemma.Dieudonne.DatumAndHonda
import Instance.Dieudonne_WittVectorHom
import Instance.Dieudonne_WittHomColimit
import Lemma.Dieudonne.FontaineHodge
import Lemma.Dieudonne.UnipotentWittCovector

set_option autoImplicit false

open Function

universe u v w u' v'

namespace Deformation

namespace TruncWitt

variable {p : ℕ} [hp : Fact p.Prime] {S : Type v} [CommRing S]

instance shiftLE_directedSystem :
    DirectedSystem (fun n => TruncatedWittVector p n S)
      fun _ _ h => (shiftLE (p := p) (R := S) h) where
  map_self _ x := shiftLE_refl x
  map_map _ _ _ h₁ h₂ x := shiftLE_shiftLE h₁ h₂ x

end TruncWitt

namespace UnipotentWittCovector

section Basic

variable (p : ℕ) [hp : Fact p.Prime] (S : Type v) [CommRing S]

noncomputable instance instAddCommGroup : AddCommGroup (UnipotentWittCovector p S) :=
  inferInstanceAs (AddCommGroup
    (AddCommGroup.DirectLimit (fun n => TruncatedWittVector p n S) fun _ _ h => TruncWitt.shiftLE h))

noncomputable instance instInhabited : Inhabited (UnipotentWittCovector p S) := ⟨0⟩

variable {p S}
variable {n m : ℕ}


end Basic


end UnipotentWittCovector


end Deformation
