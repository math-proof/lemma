import Mathlib
import Instance.MvFormalGroup_CartierModuleBaseChange
import Lemma.CerednikDrinfeld.CartierStructureConstants
import Lemma.CerednikDrinfeld.CartierModuleModel
import Instance.CerednikDrinfeld_GradedCartierNModule
import Structure.CerednikDrinfeld_DrinfeldQuadruple

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace CerednikDrinfeld

namespace FormalODModule

variable {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B]


end FormalODModule

namespace SpecialFormal

namespace Rigidified

open FormalODModule FormalOmega MvFormalGroup MvFormalGroup.CartierModule GradedCartierModuleData

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O]

abbrev jbar (ι : Zp2 p →+* O) : Zp2 p →+* O ⧸ pIdeal p O :=
  (Ideal.Quotient.mk (pIdeal p O)).comp ι

variable {Φ : FormalODModule p (O ⧸ pIdeal p O)} {B : Type} [CommRing B]

section Over

variable {S : Type} [CommRing S]

abbrev XS (t : Rigidified p Φ B) (g : B →+* S) : FormalODModule p S := t.X.map g

abbrev XbarS (t : Rigidified p Φ B) (g : B →+* S) : FormalODModule p (S ⧸ pIdeal p S) :=
  t.Xbar.map (reduceMap g)

abbrev PhibarS (ψ : O →+* B) (g : B →+* S) : FormalODModule p (S ⧸ pIdeal p S) :=
  (Φ.map (residueMap ψ)).map (reduceMap g)


abbrev bcPhi (ψ : O →+* B) (g : B →+* S) :
    CartierModule p Φ.F →+ CartierModule p (PhibarS (Φ := Φ) ψ g).F :=
  (baseChange (Φ := (Φ.map (residueMap ψ)).F) (reduceMap g)).comp
    (baseChange (Φ := Φ.F) (residueMap ψ))

abbrev rhoC (ψ : O →+* B) (t : Rigidified p Φ B)
    (hρ : IsLawHom (Φ.map (residueMap ψ)).F t.Xbar.F t.ρ) (g : B →+* S) :
    CartierModule p (PhibarS (Φ := Φ) ψ g).F →+ CartierModule p (t.XbarS g).F :=
  CartierModule.map
    ((hρ.map (reduceMap g)).toHom : MvFormalGroup.Hom (PhibarS (Φ := Φ) ψ g).F (t.XbarS g).F)


abbrev jS (ι : Zp2 p →+* O) (ψ : O →+* B) (g : B →+* S) : Zp2 p →+* S :=
  g.comp (structureMap ι ψ)

abbrev jSbar (ι : Zp2 p →+* O) (ψ : O →+* B) (g : B →+* S) : Zp2 p →+* S ⧸ pIdeal p S :=
  (reduceMap g).comp ((Ideal.Quotient.mk (pIdeal p B)).comp (structureMap ι ψ))

abbrev jPhiS (ι : Zp2 p →+* O) (ψ : O →+* B) (g : B →+* S) : Zp2 p →+* S ⧸ pIdeal p S :=
  (reduceMap g).comp ((residueMap ψ).comp (jbar ι))

abbrev IsGradedS (ι : Zp2 p →+* O) (ψ : O →+* B) (t : Rigidified p Φ B) (g : B →+* S) : Prop :=
  IsCompl ((t.XS g).gradedPiece (jS ι ψ g) 0) ((t.XS g).gradedPiece (jS ι ψ g) 1)

abbrev IsGradedSbar (ι : Zp2 p →+* O) (ψ : O →+* B) (t : Rigidified p Φ B) (g : B →+* S) :
    Prop :=
  IsCompl ((t.XbarS g).gradedPiece (jSbar ι ψ g) 0) ((t.XbarS g).gradedPiece (jSbar ι ψ g) 1)

abbrev IsGradedPhiS (ι : Zp2 p →+* O) (ψ : O →+* B) (g : B →+* S) : Prop :=
  IsCompl ((PhibarS (Φ := Φ) ψ g).gradedPiece (jPhiS ι ψ g) 0)
    ((PhibarS (Φ := Φ) ψ g).gradedPiece (jPhiS ι ψ g) 1)


end Over

abbrev Bloc (x : PrimeSpectrum B) : Type := Localization.AtPrime x.asIdeal

abbrev locHom (x : PrimeSpectrum B) : B →+* Bloc x := algebraMap B (Bloc x)

abbrev Baway (f : B) : Type := Localization (Submonoid.powers f)

abbrev awayHom (f : B) : B →+* Baway f := algebraMap B (Baway f)


end Rigidified

end SpecialFormal

end CerednikDrinfeld

end
