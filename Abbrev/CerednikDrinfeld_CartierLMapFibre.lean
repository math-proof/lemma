import Mathlib
import Instance.MvFormalGroup_NegV2
import Instance.MvFormalGroup_CartierModule
import Lemma.MvFormalGroup.CartierModuleHomothety
import Structure.CerednikDrinfeld_SpecialFormalModule
import Instance.MvFormalGroup_CartierModuleWittAction
import Instance.MvFormalGroup_CartierModuleBaseChange
import Def.CerednikDrinfeld_CartierGradedPiece
import Abbrev.CerednikDrinfeld_CriticalIndexChart
import Lemma.CerednikDrinfeld.CartierNModule
import Structure.CerednikDrinfeld_CartierLMapFibre

set_option autoImplicit false

noncomputable section

universe u

namespace CerednikDrinfeld

namespace FormalODModule

open MvFormalGroup MvFormalGroup.CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {B : Type u} [CommRing B]

abbrev piOp (X : FormalODModule p B) : CartierModule p X.F →+ CartierModule p X.F :=
  CartierModule.map X.varpiEnd


abbrev NMod [CharP B p] (X : FormalODModule p B) : Type u :=
  CartierN.NMod (CartierModule.verschiebung (p := p) (Φ := X.F)) X.piOp


abbrev NPiece [CharP B p] (X : FormalODModule p B) (j : Zp2 p →+* B) (n : ℕ) : AddSubgroup X.NMod :=
  CartierN.piece CartierModule.verschiebung X.piOp (X.gradedPiece j n) (X.gradedPiece j n)


namespace IsLMap

variable [CharP B p] {X : FormalODModule p B} {j : Zp2 p →+* B} {L : CartierModule p X.F →+ X.NMod}


end IsLMap

end FormalODModule

end CerednikDrinfeld

end

set_option autoImplicit false

noncomputable section

universe u

namespace CerednikDrinfeld

namespace FormalODModule

open MvFormalGroup MvFormalGroup.CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {B : Type u} [CommRing B]


namespace IsLMap

variable [CharP B p] {X : FormalODModule p B} {j : Zp2 p →+* B} {L : CartierModule p X.F →+ X.NMod}

abbrev phi (h : X.IsLMap j L) : X.NMod →+ X.NMod :=
  CartierN.phi CartierModule.verschiebung X.piOp L h.comp_verschiebung

abbrev eta (h : X.IsLMap j L) : AddSubgroup X.NMod :=
  CartierN.eta CartierModule.verschiebung X.piOp L h.comp_verschiebung

abbrev u (h : X.IsLMap j L) :
    h.eta →+ CartierModule p X.F ⧸ (CartierModule.verschiebung (p := p) (Φ := X.F)).range :=
  CartierN.u CartierModule.verschiebung X.piOp L h.comp_verschiebung

end IsLMap

end FormalODModule

end CerednikDrinfeld

end
