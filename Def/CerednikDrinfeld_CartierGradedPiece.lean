import Mathlib
import Instance.MvFormalGroup_NegV2
import Instance.MvFormalGroup_CartierModule
import Lemma.MvFormalGroup.CartierModuleHomothety
import Lemma.CerednikDrinfeld.SpecialFormalModule

set_option autoImplicit false

noncomputable section

universe u

namespace CerednikDrinfeld

namespace FormalODModule

open MvFormalGroup MvFormalGroup.CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {B : Type u} [CommRing B]

def gradedPiece (X : FormalODModule p B) (j : Zp2 p →+* B) (n : ℕ) :
    AddSubgroup (CartierModule p X.F) where
  carrier := {f | ∀ c : GaloisField p 2,
    endAct (X.actEnd (WittVector.teichmuller p c)) f =
      homothety (j (WittVector.teichmuller p c) ^ p ^ n) f}
  zero_mem' := fun c => by simp only [map_zero]
  add_mem' := fun {f g} hf hg c => by simp only [map_add, hf c, hg c]
  neg_mem' := fun {f} hf c => by simp only [map_neg, hf c]

end FormalODModule

end CerednikDrinfeld

end
