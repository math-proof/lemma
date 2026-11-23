module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.Polynomial.ScaleRoots
public import Mathlib.Algebra.Polynomial.Lifts

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial

namespace AlgebraicCurve

namespace TwoChartIntegralModel

variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]

variable {F} in
def chartAlg (S : Set F) : Subalgebra R F where
  carrier := {x | IsIntegral (Algebra.adjoin R S) x}
  mul_mem' ha hb := ha.mul hb
  one_mem' := isIntegral_one
  add_mem' ha hb := ha.add hb
  zero_mem' := isIntegral_zero
  algebraMap_mem' a := by
    have : IsIntegral (Algebra.adjoin R S)
        (algebraMap (Algebra.adjoin R S) F (algebraMap R (Algebra.adjoin R S) a)) :=
      isIntegral_algebraMap
    simpa [← IsScalarTower.algebraMap_apply] using this

abbrev chartIncl {S S' : Set F} (h : S ⊆ S') : chartAlg R F S →ₐ[R] chartAlg R F S' :=
  Subalgebra.inclusion (chartAlg_mono R F h)

variable {R F j}

variable (R F j)

omit [Fact (j ≠ 0)] in
abbrev chartAlgFin : Subalgebra R F := chartAlg R F {j}

abbrev chartAlgInf : Subalgebra R F := chartAlg R F {j⁻¹}

abbrev chartAlgMid : Subalgebra R F := chartAlg R F {j, j⁻¹}

def jChartFin : chartAlgFin R F j := ⟨j, subset_chartAlg R F _ rfl⟩

def jInvChartInf : chartAlgInf R F j := ⟨j⁻¹, subset_chartAlg R F _ rfl⟩

omit [Fact (j ≠ 0)] in
abbrev inclFin : chartAlgFin R F j →ₐ[R] chartAlgMid R F j := chartIncl R F (sFin_subset F j)

abbrev inclInf : chartAlgInf R F j →ₐ[R] chartAlgMid R F j := chartIncl R F (sInf_subset F j)

abbrev XFin : Scheme.{u} := Spec (CommRingCat.of (chartAlgFin R F j))

abbrev XInf : Scheme.{u} := Spec (CommRingCat.of (chartAlgInf R F j))

abbrev XMid : Scheme.{u} := Spec (CommRingCat.of (chartAlgMid R F j))

abbrev fFin : XMid R F j ⟶ XFin R F j := Spec.map (CommRingCat.ofHom (inclFin R F j).toRingHom)

abbrev fInf : XMid R F j ⟶ XInf R F j := Spec.map (CommRingCat.ofHom (inclInf R F j).toRingHom)

def _root_.AlgebraicCurve.TwoChartIntegralModel : Scheme.{u} :=
  haveI := hasPushout_fFin_fInf R F j
  pushout (fFin R F j) (fInf R F j)

def ιFin : XFin R F j ⟶ AlgebraicCurve.TwoChartIntegralModel R F j :=
  haveI := hasPushout_fFin_fInf R F j
  pushout.inl (fFin R F j) (fInf R F j)

def ιInf : XInf R F j ⟶ AlgebraicCurve.TwoChartIntegralModel R F j :=
  haveI := hasPushout_fFin_fInf R F j
  pushout.inr (fFin R F j) (fInf R F j)

def toBase : AlgebraicCurve.TwoChartIntegralModel R F j ⟶ Spec (CommRingCat.of R) :=
  haveI := hasPushout_fFin_fInf R F j
  pushout.desc (Spec.map (CommRingCat.ofHom (algebraMap R (chartAlgFin R F j))))
    (Spec.map (CommRingCat.ofHom (algebraMap R (chartAlgInf R F j))))
    (fFin_toBase_eq_fInf_toBase R F j)

def chartFinOpen : (AlgebraicCurve.TwoChartIntegralModel R F j).Opens :=
  haveI := ιFin_isOpenImmersion R F j
  (ιFin R F j).opensRange

def chartInfOpen : (AlgebraicCurve.TwoChartIntegralModel R F j).Opens :=
  haveI := ιInf_isOpenImmersion R F j
  (ιInf R F j).opensRange

def polynomialToChartFin : Polynomial R →ₐ[R] chartAlgFin R F j := Polynomial.aeval (jChartFin R F j)

def polynomialToChartInf : Polynomial R →ₐ[R] chartAlgInf R F j := Polynomial.aeval (jInvChartInf R F j)

omit [Fact (j ≠ 0)] in
def baseChange (S : Type u) [CommRing S] [Algebra R S] : Scheme.{u} :=
  pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R S)))

def baseChangeι (S : Type u) [CommRing S] [Algebra R S] :
    baseChange R F j S ⟶ AlgebraicCurve.TwoChartIntegralModel R F j := pullback.fst _ _

def baseChangeToBase (S : Type u) [CommRing S] [Algebra R S] :
    baseChange R F j S ⟶ Spec (CommRingCat.of S) := pullback.snd _ _

abbrev fibre (I : Ideal R) : Scheme.{u} := baseChange R F j (R ⧸ I)

abbrev fibreι (I : Ideal R) : fibre R F j I ⟶ AlgebraicCurve.TwoChartIntegralModel R F j :=
  baseChangeι R F j (R ⧸ I)

abbrev fibreToBase (I : Ideal R) : fibre R F j I ⟶ Spec (CommRingCat.of (R ⧸ I)) :=
  baseChangeToBase R F j (R ⧸ I)

section BaseChange

variable (R' : Type u) [CommRing R'] [Algebra R R'] [Algebra R' F] [IsScalarTower R R' F]

def chartBaseChange (S : Set F) : chartAlg R F S →+* chartAlg R' F S :=
  (Subalgebra.inclusion (chartAlg_le_restrictScalars R F R' S)).toRingHom

end BaseChange

end TwoChartIntegralModel

end AlgebraicCurve

end

end
