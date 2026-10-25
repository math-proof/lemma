import Mathlib
import Instance.MvFormalGroup_NegV2
import Instance.MvFormalGroup_CartierModule
import Lemma.MvFormalGroup.CartierModuleHomothety
import Lemma.CerednikDrinfeld.SpecialFormalModule
import Instance.MvFormalGroup_CartierModuleWittAction
import Instance.MvFormalGroup_CartierModuleBaseChange
import Def.CerednikDrinfeld_CartierGradedPiece
import Lemma.CerednikDrinfeld.CriticalIndexChart
import Lemma.CerednikDrinfeld.CartierNModule
import Abbrev.CerednikDrinfeld_CartierLMapFibre

set_option autoImplicit false

noncomputable section

universe u

namespace CerednikDrinfeld

namespace FormalODModule

open MvFormalGroup MvFormalGroup.CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {B : Type u} [CommRing B]


def IsPiBijective [CharP B p] (X : FormalODModule p B) (j : Zp2 p →+* B) (n : ℕ) : Prop :=
  (∀ f ∈ X.gradedPiece j n, (∃ g : CartierModule p X.F, CartierModule.verschiebung g = X.piOp f) →
      ∃ g : CartierModule p X.F, CartierModule.verschiebung g = f) ∧
    ∀ h ∈ X.gradedPiece j (n + 1), ∃ f ∈ X.gradedPiece j n, ∃ g : CartierModule p X.F,
      h = X.piOp f + CartierModule.verschiebung g

end FormalODModule

end CerednikDrinfeld

end
