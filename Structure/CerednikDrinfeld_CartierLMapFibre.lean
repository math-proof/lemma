import Mathlib
import Instance.MvFormalGroup_NegV2
import Instance.MvFormalGroup_CartierModule
import Lemma.MvFormalGroup.CartierModuleHomothety
import Structure.CerednikDrinfeld_SpecialFormalModule
import Instance.MvFormalGroup_CartierModuleWittAction
import Instance.MvFormalGroup_CartierModuleBaseChange
import Def.CerednikDrinfeld_CartierGradedPiece
import Lemma.CerednikDrinfeld.CriticalIndexChart
import Lemma.CerednikDrinfeld.CartierNModule
import Abbrev.CerednikDrinfeld_CartierLMapFibre
import Def.CerednikDrinfeld_CartierLMapFibre

set_option autoImplicit false

noncomputable section

universe u

namespace CerednikDrinfeld

namespace FormalODModule

open MvFormalGroup MvFormalGroup.CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {B : Type u} [CommRing B]


theorem piOp_comp_verschiebung [CharP B p] (X : FormalODModule p B) :
    X.piOp.comp CartierModule.verschiebung = CartierModule.verschiebung.comp X.piOp :=
  AddMonoidHom.ext fun f => CartierModule.map_verschiebung X.varpiEnd f


abbrev lambdaN [CharP B p] (X : FormalODModule p B) : X.NMod →+ CartierModule p X.F :=
  CartierN.lambda CartierModule.verschiebung X.piOp X.piOp_comp_verschiebung


structure IsLMap [CharP B p] (X : FormalODModule p B) (j : Zp2 p →+* B)
    (L : CartierModule p X.F →+ X.NMod) : Prop where

  lambdaN_comp : X.lambdaN.comp L = CartierModule.frobenius

  comp_verschiebung :
    L.comp CartierModule.verschiebung = (CartierN.inl CartierModule.verschiebung X.piOp).comp X.piOp

  mem_nPiece : ∀ (n : ℕ), ∀ f ∈ X.gradedPiece j n, L f ∈ X.NPiece j n

  eq_inl_of_isCritical : ∀ (n : ℕ), CritChart.IsCritical X j n → ∀ f ∈ X.gradedPiece j n,
    ∀ g : CartierModule p X.F, CartierModule.verschiebung g = X.piOp f →
      L f = CartierN.inl CartierModule.verschiebung X.piOp g

namespace IsLMap

variable [CharP B p] {X : FormalODModule p B} {j : Zp2 p →+* B} {L : CartierModule p X.F →+ X.NMod}


end IsLMap

end FormalODModule

end CerednikDrinfeld

end
