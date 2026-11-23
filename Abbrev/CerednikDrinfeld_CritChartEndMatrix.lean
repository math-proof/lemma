module

public import Mathlib
public import Instance.MvFormalGroup_NegV2
public import Instance.MvFormalGroup_CartierModule
public import Theorem.PowerSeries.CartierModuleHomothety
public import Instance.MvFormalGroup_CartierModuleWittAction
public import Instance.MvFormalGroup_CartierModuleBaseChange
public import Structure.CerednikDrinfeld_SpecialFormalModule
public import Def.CerednikDrinfeld_CartierGradedPiece
public import Abbrev.CerednikDrinfeld_CriticalIndexChart

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace MvFormalGroup

namespace CartierModule

variable (p : ℕ) [hp : Fact p.Prime] (R : Type u) [CommRing R] [CharP R p]

end CartierModule

end MvFormalGroup

namespace CerednikDrinfeld

namespace FormalODModule

open MvFormalGroup MvFormalGroup.CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {B : Type u} [CommRing B]

abbrev endOD (X : FormalODModule p B) : Subring (MvFormalGroup.End X.F) :=
  Subring.centralizer (Set.range X.actEnd ∪ {X.varpiEnd})

namespace CritChart

end CritChart

end FormalODModule

end CerednikDrinfeld

end
