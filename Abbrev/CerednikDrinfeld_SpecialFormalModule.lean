import Mathlib
import Instance.MvFormalGroup_NegV2
import Structure.CerednikDrinfeld_SpecialFormalModule

set_option autoImplicit false

noncomputable section

universe u v

namespace CerednikDrinfeld

open MvPowerSeries (subst HasSubst hasSubst_of_constantCoeff_zero constantCoeff coeff
  subst_comp_subst_apply subst_X map_subst constantCoeff_X constantCoeff_subst_eq_zero)

variable (p : ℕ) [Fact p.Prime]

abbrev Zp2 : Type := WittVector p (GaloisField p 2)

namespace SpecialFormal

variable {p}
variable {B : Type u} [CommRing B] {B' : Type v} [CommRing B']


namespace IsLawHom

variable {F G H : MvFormalGroup 2 B} {φ ψ : Series B}

end IsLawHom


end SpecialFormal

open SpecialFormal


namespace FormalODModule


variable {p}
variable {B : Type u} [CommRing B] {B' : Type v} [CommRing B']


namespace IsODHom

variable {X Y Z : FormalODModule p B} {φ ψ : Series B}


end IsODHom

namespace Hom

variable {X Y Z : FormalODModule p B}

end Hom


end FormalODModule


namespace SpecialFormal


variable {p}


namespace Rigidified

variable {O : Type v} [CommRing O] {Φ : FormalODModule p (O ⧸ pIdeal p O)}
variable {B B' B'' : Type u} [CommRing B] [CommRing B'] [CommRing B'']

end Rigidified


namespace ModuliPackage

variable {O : Type v} [CommRing O]

end ModuliPackage

end SpecialFormal

end CerednikDrinfeld

end
