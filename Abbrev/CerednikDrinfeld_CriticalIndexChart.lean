import Mathlib
import Instance.MvFormalGroup_NegV2
import Instance.MvFormalGroup_CartierModule
import Lemma.MvFormalGroup.CartierModuleHomothety
import Instance.MvFormalGroup_CartierModuleWittAction
import Instance.MvFormalGroup_CartierModuleBaseChange
import Structure.CerednikDrinfeld_SpecialFormalModule
import Def.CerednikDrinfeld_CartierGradedPiece
import Lemma.CerednikDrinfeld.CartierStructureConstants

set_option autoImplicit false

noncomputable section

universe u v w

namespace CerednikDrinfeld

namespace FormalODModule

open MvFormalGroup MvFormalGroup.CartierModule

section BaseChange

variable {p : ℕ} [hp : Fact p.Prime] {B : Type u} [CommRing B] {B' : Type v} [CommRing B']
  {B'' : Type w} [CommRing B'']

end BaseChange

namespace CritChart

variable {p : ℕ} [hp : Fact p.Prime] {B : Type u} [CommRing B]

section OneBase

variable [CharP B p]

end OneBase

section Functor

variable {B₀ : Type u} [CommRing B₀]

abbrev cartierObj (X : FormalODModule p B₀) (B' : Type v) [CommRing B'] [Algebra B₀ B'] : Type v :=
  CartierModule p (X.map (algebraMap B₀ B')).F

end Functor

section Transition

variable [CharP B p]

end Transition

end CritChart

end FormalODModule

end CerednikDrinfeld

end
