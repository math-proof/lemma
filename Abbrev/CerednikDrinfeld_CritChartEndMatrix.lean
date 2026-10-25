import Mathlib
import Instance.MvFormalGroup_NegV2
import Instance.MvFormalGroup_CartierModule
import Lemma.MvFormalGroup.CartierModuleHomothety
import Instance.MvFormalGroup_CartierModuleWittAction
import Instance.MvFormalGroup_CartierModuleBaseChange
import Structure.CerednikDrinfeld_SpecialFormalModule
import Def.CerednikDrinfeld_CartierGradedPiece
import Abbrev.CerednikDrinfeld_CriticalIndexChart

set_option autoImplicit false

noncomputable section

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
