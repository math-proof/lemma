import Mathlib
import Lemma.Definitions.Def_WeierstrassCurve_ProjModel
import Lemma.Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Lemma.Definitions.Def_WeierstrassCurve_SectionAtOrigin

set_option autoImplicit false

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassProjModel MvPolynomial HomogeneousLocalization
open HomogeneousIdealQuotientGrading

attribute [local instance] MvPolynomial.gradedAlgebra

namespace WeierstrassCurve.DrinfeldGlobal

variable {T : Type u} [CommRing T] (W : WeierstrassCurve.Projective T)

abbrev ZChartRing : Type u := Away (projModelGradingCR W) (coord W 2)

abbrev zChartι : Spec (CommRingCat.of (ZChartRing W)) ⟶ projModelCR W :=
  Proj.awayι (projModelGradingCR W) (coord W 2) (coord_mem W 2) one_pos

def xOverZ : ZChartRing W :=
  Away.mk (projModelGradingCR W) (coord_mem W 2) 1 (coord W 0) (by simpa using coord_mem W 0)

def yOverZ : ZChartRing W :=
  Away.mk (projModelGradingCR W) (coord_mem W 2) 1 (coord W 1) (by simpa using coord_mem W 1)

variable {W}

def IsZChartSection (S : Section W) (χ : ZChartRing W →+* T) : Prop :=
  S.1 = Spec.map (CommRingCat.ofHom χ) ≫ zChartι W

def affX (χ : ZChartRing W →+* T) : T := χ (xOverZ W)

def affY (χ : ZChartRing W →+* T) : T := χ (yOverZ W)

def IsSectionThrough (S : Section W) (x y : T) : Prop :=
  ∃ χ : ZChartRing W →+* T, IsZChartSection S χ ∧ affX χ = x ∧ affY χ = y

end WeierstrassCurve.DrinfeldGlobal

end
