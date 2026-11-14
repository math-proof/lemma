import Mathlib
import Lemma.MvPowerSeries.NegV2
import Lemma.MvPowerSeries.CartierModule
import Lemma.PowerSeries.CartierModuleHomothety
import Lemma.MvPowerSeries.SpecialFormalModule
import Lemma.MvPowerSeries.CartierModuleWittAction
import Lemma.MvPowerSeries.CartierModuleBaseChange
import Lemma.FormalGroup.CartierGradedPiece
import Lemma.FormalGroup.CriticalIndexChart
import Lemma.Int.CartierNModule
import Abbrev.CerednikDrinfeld_CartierLMapFibre
import Def.CerednikDrinfeld_CartierLMapFibre
import Structure.CerednikDrinfeld_CartierLMapFibre

set_option autoImplicit false

noncomputable section

universe u

namespace CerednikDrinfeld

namespace FormalODModule

open MvFormalGroup MvPowerSeries.CartierModule MvPowerSeries PowerSeries

variable {p : ℕ} [hp : Fact p.Prime] {B : Type u} [CommRing B]


theorem piOp_apply (X : FormalODModule p B) (f : CartierModule p X.F) :
    X.piOp f = CartierModule.endAct X.varpiEnd f := rfl


theorem critChart_isCritical_iff [CharP B p] (X : FormalODModule p B) (j : Zp2 p →+* B) (n : ℕ) :
    CritChart.IsCritical X j n ↔
      ∀ f ∈ X.gradedPiece j n, ∃ g : CartierModule p X.F, X.piOp f = CartierModule.verschiebung g :=
  forall₂_congr fun _ _ => exists_congr fun _ => eq_comm

theorem mem_critChart_invariants_iff [CharP B p] (X : FormalODModule p B) (j : Zp2 p →+* B) (n : ℕ)
    (m : CartierModule p X.F) :
    m ∈ CritChart.invariants X j n ↔ m ∈ X.gradedPiece j n ∧ X.piOp m = CartierModule.verschiebung m :=
  Iff.rfl


namespace IsLMap

variable [CharP B p] {X : FormalODModule p B} {j : Zp2 p →+* B} {L : CartierModule p X.F →+ X.NMod}

end IsLMap

end FormalODModule

end CerednikDrinfeld

end
