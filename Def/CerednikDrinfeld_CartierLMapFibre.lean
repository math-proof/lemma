module

public import Mathlib
public import Instance.MvFormalGroup_NegV2
public import Instance.MvFormalGroup_CartierModule
public import Theorem.PowerSeries.CartierModuleHomothety
public import Theorem.MvPowerSeries.SpecialFormalModule
public import Instance.MvFormalGroup_CartierModuleWittAction
public import Instance.MvFormalGroup_CartierModuleBaseChange
public import Def.CerednikDrinfeld_CartierGradedPiece
public import Theorem.FormalGroup.CriticalIndexChart
public import Theorem.Int.CartierNModule
public import Abbrev.CerednikDrinfeld_CartierLMapFibre

@[expose] public section

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
