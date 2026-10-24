import Mathlib
import Lemma.Definitions.Def_MvFormalGroup_NegV2
import Lemma.Definitions.Def_MvFormalGroup_CartierModule
import Lemma.Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Lemma.Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Lemma.Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Lemma.Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Lemma.Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Lemma.Definitions.Def_CerednikDrinfeld_CriticalIndexChart
import Lemma.Definitions.Def_CerednikDrinfeld_CartierNModule

set_option autoImplicit false

noncomputable section

universe u

namespace CerednikDrinfeld

namespace FormalODModule

open MvFormalGroup MvFormalGroup.CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {B : Type u} [CommRing B]

abbrev piOp (X : FormalODModule p B) : CartierModule p X.F →+ CartierModule p X.F :=
  CartierModule.map X.varpiEnd

theorem piOp_apply (X : FormalODModule p B) (f : CartierModule p X.F) :
    X.piOp f = CartierModule.endAct X.varpiEnd f := rfl

theorem piOp_comp_verschiebung [CharP B p] (X : FormalODModule p B) :
    X.piOp.comp CartierModule.verschiebung = CartierModule.verschiebung.comp X.piOp :=
  AddMonoidHom.ext fun f => CartierModule.map_verschiebung X.varpiEnd f

abbrev NMod [CharP B p] (X : FormalODModule p B) : Type u :=
  CartierN.NMod (CartierModule.verschiebung (p := p) (Φ := X.F)) X.piOp

abbrev lambdaN [CharP B p] (X : FormalODModule p B) : X.NMod →+ CartierModule p X.F :=
  CartierN.lambda CartierModule.verschiebung X.piOp X.piOp_comp_verschiebung

abbrev NPiece [CharP B p] (X : FormalODModule p B) (j : Zp2 p →+* B) (n : ℕ) : AddSubgroup X.NMod :=
  CartierN.piece CartierModule.verschiebung X.piOp (X.gradedPiece j n) (X.gradedPiece j n)

theorem critChart_isCritical_iff [CharP B p] (X : FormalODModule p B) (j : Zp2 p →+* B) (n : ℕ) :
    CritChart.IsCritical X j n ↔
      ∀ f ∈ X.gradedPiece j n, ∃ g : CartierModule p X.F, X.piOp f = CartierModule.verschiebung g :=
  forall₂_congr fun _ _ => exists_congr fun _ => eq_comm

theorem mem_critChart_invariants_iff [CharP B p] (X : FormalODModule p B) (j : Zp2 p →+* B) (n : ℕ)
    (m : CartierModule p X.F) :
    m ∈ CritChart.invariants X j n ↔ m ∈ X.gradedPiece j n ∧ X.piOp m = CartierModule.verschiebung m :=
  Iff.rfl

def IsPiBijective [CharP B p] (X : FormalODModule p B) (j : Zp2 p →+* B) (n : ℕ) : Prop :=
  (∀ f ∈ X.gradedPiece j n, (∃ g : CartierModule p X.F, CartierModule.verschiebung g = X.piOp f) →
      ∃ g : CartierModule p X.F, CartierModule.verschiebung g = f) ∧
    ∀ h ∈ X.gradedPiece j (n + 1), ∃ f ∈ X.gradedPiece j n, ∃ g : CartierModule p X.F,
      h = X.piOp f + CartierModule.verschiebung g

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
