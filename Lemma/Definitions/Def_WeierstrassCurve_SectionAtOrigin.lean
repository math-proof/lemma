import Mathlib
import Lemma.Definitions.Def_WeierstrassCurve_ProjModel
import Lemma.Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal

set_option autoImplicit false

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory WeierstrassProjModel MvPolynomial HomogeneousLocalization
open HomogeneousIdealQuotientGrading

attribute [local instance] MvPolynomial.gradedAlgebra

namespace WeierstrassCurve.DrinfeldGlobal

variable {T : Type u} [CommRing T] (W : WeierstrassCurve.Projective T)

abbrev coord (i : Fin 3) : ProjModelRingCR W :=
  Ideal.Quotient.mk (projModelHomogeneousIdealCR W).toIdeal (X i)

theorem coord_mem (i : Fin 3) : coord W i ∈ projModelGradingCR W 1 :=
  mk_mem_quotGradingSubmodule _ _ (isHomogeneous_X T i)

abbrev OriginChartRing : Type u := Away (projModelGradingCR W) (coord W 1)

abbrev originChartι : Spec (CommRingCat.of (OriginChartRing W)) ⟶ projModelCR W :=
  Proj.awayι (projModelGradingCR W) (coord W 1) (coord_mem W 1) one_pos

def xOverY : OriginChartRing W :=
  Away.mk (projModelGradingCR W) (coord_mem W 1) 1 (coord W 0) (by simpa using coord_mem W 0)

def zOverY : OriginChartRing W :=
  Away.mk (projModelGradingCR W) (coord_mem W 1) 1 (coord W 2) (by simpa using coord_mem W 2)

variable {W}

def IsOriginChartSection (P : Section W) (χ : OriginChartRing W →+* T) : Prop :=
  P.1 = Spec.map (CommRingCat.ofHom χ) ≫ originChartι W

def originParam (χ : OriginChartRing W →+* T) : T := - χ (xOverY W)

def originW (χ : OriginChartRing W →+* T) : T := - χ (zOverY W)

def ReducesToOrigin (P : Section W) (χ : OriginChartRing W →+* T) (I : Ideal T) : Prop :=
  IsOriginChartSection P χ ∧ originParam χ ∈ I ∧ originW χ ∈ I

end WeierstrassCurve.DrinfeldGlobal

end
