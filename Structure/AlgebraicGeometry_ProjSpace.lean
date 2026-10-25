import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Ideal
import Instance.AlgebraicGeometry_ProjSpace

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace MvPolynomial HomogeneousLocalization

namespace AlgebraicGeometry


namespace ProjSpace

section PnSetup

variable (R : Type u) [CommRing R] (n : ℕ)


end PnSetup

section StdCover

open MvPolynomial AlgebraicGeometry.Proj

variable (R : Type u) [CommRing R] (n : ℕ)


end StdCover

section Setup

variable (R : Type u) [CommRing R] (n : ℕ)


end Setup

section StdCover

variable (R : Type u) [CommRing R] (n : ℕ)


end StdCover

section AdjoinRatio

variable (R : Type u) [CommRing R] (n : ℕ)


end AdjoinRatio

section ProdOver

variable (R : Type u) [CommRing R]

def prodOverAux :
    ∀ {m : ℕ}, (Fin m → ℕ) → Σ (P : Scheme.{u}), P ⟶ Spec (.of R)
  | 0, _ => ⟨Spec (.of R), 𝟙 _⟩
  | m + 1, e =>
    let prev := @prodOverAux m (e ∘ Fin.succ)
    ⟨pullback (π R (e 0)) prev.2,
     pullback.fst _ _ ≫ π R (e 0)⟩

abbrev prodOver {m : ℕ} (e : Fin m → ℕ) : Scheme.{u} :=
  (prodOverAux R e).1

abbrev prodOverπ {m : ℕ} (e : Fin m → ℕ) :
    prodOver R e ⟶ Spec (.of R) :=
  (prodOverAux R e).2


end ProdOver

section MapGraded

variable (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A] (n : ℕ)


end MapGraded

end ProjSpace

section Carrier

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R))

structure ChowDatum where

  m : ℕ

  e : Fin m → ℕ

  V' : Scheme.{u}

  p : V' ⟶ V

  ι : V' ⟶ ProjSpace.prodOver R e

  hp_proper : IsProper p

  hι_closed : IsClosedImmersion ι

  hover : ι ≫ ProjSpace.prodOverπ R e = p ≫ π

  U : V.Opens

  hU_dense : Dense (U : Set V)

  hp_isoU : IsIso (pullback.snd p U.ι)

attribute [instance] ChowDatum.hp_proper ChowDatum.hι_closed ChowDatum.hp_isoU

end Carrier

section CarrierProj

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R))

structure ChowDatumProj where

  Nd : ℕ

  V' : Scheme.{u}

  p : V' ⟶ V

  ιN : V' ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (Nd + 1)) R)

  hp_proper : IsProper p

  hιN_closed : IsClosedImmersion ιN

  hoverN : ιN ≫ ProjSpace.π R Nd = p ≫ π

  U : V.Opens

  hU_dense : Dense (U : Set V)

  hp_isoU : IsIso (pullback.snd p U.ι)

attribute [instance] ChowDatumProj.hp_proper ChowDatumProj.hιN_closed
  ChowDatumProj.hp_isoU

end CarrierProj

end AlgebraicGeometry

end
