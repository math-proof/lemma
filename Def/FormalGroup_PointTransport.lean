import Mathlib
import Lemma.FormalGroup.NSeries
import Structure.FormalGroup_PointTransport

set_option autoImplicit false

noncomputable section

namespace FormalGroup

variable {R : Type*} [CommRing R]


namespace LawHom

variable {F G : FormalGroup R}

def app {A : Type*} [CommRing A] [UniformSpace A] [Algebra R A] (φ : LawHom F G) (x : A) : A :=
  FormalGroup.evalSeries φ.series x

def appAdic {A : Type*} [CommRing A] [Algebra R A] (φ : LawHom F G) (I : Ideal A) (x : A) : A :=
  letI : WithIdeal A := ⟨I⟩
  φ.app x

end LawHom

def IsBaseChange (F : FormalGroup R) {S : Type*} [CommRing S] (f : R →+* S) (G : FormalGroup S) : Prop :=
  G.toPowerSeries = MvPowerSeries.map f F.toPowerSeries

end FormalGroup

end
