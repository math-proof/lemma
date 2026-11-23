module

public import Theorem.Scheme.RelativeGroupLaw
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Abbrev.GoodReductionJacobian_RelativeGroupLawKernel

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra Scheme

namespace GoodReductionJacobian
namespace RelativeGroupLaw

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

def nsmul (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (n : ℕ) (x : SchemeHomOver t f) : SchemeHomOver t f :=
  Nat.rec (G.one t) (fun _ ih => G.mul t ih x) n

def IsTorsionPoint (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f) : Prop :=
  G.nsmul t n x = G.one t

def torsionSubset (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) : Set (SchemeHomOver t f) :=
  {x | G.IsTorsionPoint t n x}

def schemeNsmul (G : RelativeGroupLaw R f) (n : ℕ) : A ⟶ A :=
  (G.nsmul f n idPoint).1

abbrev schemeKer (G : RelativeGroupLaw R f) (n : ℕ) : Scheme.{u} :=
  pullback (G.schemeNsmul n) (G.one (𝟙 (Spec (CommRingCat.of R)))).1

abbrev schemeKerStr (G : RelativeGroupLaw R f) (n : ℕ) :
    G.schemeKer n ⟶ Spec (CommRingCat.of R) :=
  pullback.snd (G.schemeNsmul n) (G.one (𝟙 (Spec (CommRingCat.of R)))).1

end RelativeGroupLaw

end GoodReductionJacobian

end
