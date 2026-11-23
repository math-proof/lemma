module

public import Theorem.Ideal.HomogeneousIdealQuotientGradingInfra
public import Theorem.WeierstrassCurve.ProjectiveWeierstrassPolynomialPrime
public import Theorem.Scheme.NeronModelPropertyBundleCarrier
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Structure.WeierstrassCurve_ProjModel
public import Abbrev.WeierstrassCurve_ProjModel

public noncomputable section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Ideal Scheme WeierstrassCurve

namespace WeierstrassProjModel

public theorem ext_of_isSchemeTheoreticallyDominant_of_isSeparated {W X Y Z : Scheme.{u}}
    {f g : X ⟶ Y} (s : Y ⟶ Z) [IsSeparated s] (h : f ≫ s = g ≫ s)
    (ι : W ⟶ X) [IsSchemeTheoreticallyDominant ι] (hU : ι ≫ f = ι ≫ g) : f = g := by
  let X' : Over Z := Over.mk (f ≫ s)
  let Y' : Over Z := Over.mk s
  let U' : Over Z := Over.mk (ι ≫ f ≫ s)
  let f' : X' ⟶ Y' := Over.homMk f
  let g' : X' ⟶ Y' := Over.homMk g h.symm
  let ι' : U' ⟶ X' := Over.homMk ι
  have : IsSeparated Y'.hom := ‹_›

  have hcond : ι' ≫ f' = ι' ≫ g' := by ext1; exact hU

  have hker : (equalizer.ι f' g').left.ker = ⊥ := by
    have h1 : (equalizer.ι f' g').left.ker ≤
        ((equalizer.lift ι' hcond ≫ equalizer.ι f' g').left).ker := by
      rw [Over.comp_left]
      exact Scheme.Hom.le_ker_comp _ _
    rw [equalizer.lift_ι] at h1
    have h2 : (ι'.left).ker = ⊥ := Scheme.Hom.ker_eq_bot ι
    exact le_bot_iff.mp (h1.trans (le_of_eq h2))

  haveI : IsClosedImmersion (equalizer.ι f' g').left := inferInstance
  haveI : IsIso (equalizer.ι f' g').left := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hker
  exact (cancel_epi (equalizer.ι f' g').left).mp congr($(equalizer.condition f' g').left)

end WeierstrassProjModel

namespace WeierstrassProjModel

open NeronModelInfra


public theorem schemeHomOverComp_coe {B T' T A : Scheme.{u}} {t : T ⟶ B} {t' : T' ⟶ B} {f : A ⟶ B}
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    (schemeHomOverComp ψ hψ x).1 = ψ ≫ x.1 :=
  rfl


namespace RelativeGroupLaw

variable {R : Type u} [CommRing R]
variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}


@[simp]
public theorem nsmul_zero (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    G.nsmul t 0 x = G.one t :=
  rfl


@[simp]
public theorem nsmul_succ (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f) :
    G.nsmul t (n + 1) x = G.mul t (G.nsmul t n x) x :=
  rfl


public theorem nsmul_one_apply (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    G.nsmul t 1 x = x := by
  show G.mul t (G.one t) x = x
  exact G.one_mul t x


public theorem nsmul_unit (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) :
    G.nsmul t n (G.one t) = G.one t := by
  induction n with
  | zero => rfl
  | succ n ih => rw [nsmul_succ, ih, G.mul_one]


public theorem one_natural (G : RelativeGroupLaw R f) {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') :
    schemeHomOverComp ψ hψ (G.one t) = G.one t' := by
  have h : G.mul t' (schemeHomOverComp ψ hψ (G.one t)) (schemeHomOverComp ψ hψ (G.one t)) =
      schemeHomOverComp ψ hψ (G.one t) := by
    rw [← G.mul_natural t t' ψ hψ, G.one_mul]
  calc schemeHomOverComp ψ hψ (G.one t)
      = G.mul t' (G.one t') (schemeHomOverComp ψ hψ (G.one t)) := (G.one_mul t' _).symm
    _ = G.mul t' (G.mul t' (G.inv t' (schemeHomOverComp ψ hψ (G.one t)))
          (schemeHomOverComp ψ hψ (G.one t))) (schemeHomOverComp ψ hψ (G.one t)) := by
        rw [G.inv_mul_cancel]
    _ = G.mul t' (G.inv t' (schemeHomOverComp ψ hψ (G.one t)))
          (G.mul t' (schemeHomOverComp ψ hψ (G.one t)) (schemeHomOverComp ψ hψ (G.one t))) := by
        rw [G.mul_assoc]
    _ = G.mul t' (G.inv t' (schemeHomOverComp ψ hψ (G.one t)))
          (schemeHomOverComp ψ hψ (G.one t)) := by rw [h]
    _ = G.one t' := G.inv_mul_cancel t' _


public theorem nsmul_natural (G : RelativeGroupLaw R f) {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (n : ℕ) (x : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (G.nsmul t n x) = G.nsmul t' n (schemeHomOverComp ψ hψ x) := by
  induction n with
  | zero =>
      show schemeHomOverComp ψ hψ (G.one t) = G.one t'
      exact G.one_natural t t' ψ hψ
  | succ n ih =>
      calc schemeHomOverComp ψ hψ (G.nsmul t (n + 1) x)
          = schemeHomOverComp ψ hψ (G.mul t (G.nsmul t n x) x) := rfl
        _ = G.mul t' (schemeHomOverComp ψ hψ (G.nsmul t n x)) (schemeHomOverComp ψ hψ x) :=
            G.mul_natural t t' ψ hψ _ _
        _ = G.mul t' (G.nsmul t' n (schemeHomOverComp ψ hψ x)) (schemeHomOverComp ψ hψ x) := by
            rw [ih]
        _ = G.nsmul t' (n + 1) (schemeHomOverComp ψ hψ x) := rfl


public theorem isTorsionPoint_def (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f) :
    G.IsTorsionPoint t n x ↔ G.nsmul t n x = G.one t :=
  Iff.rfl


@[simp]
public theorem mem_torsionSubset (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f) :
    x ∈ G.torsionSubset t n ↔ G.IsTorsionPoint t n x :=
  Iff.rfl


public theorem isTorsionPoint_unit (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) :
    G.IsTorsionPoint t n (G.one t) :=
  G.nsmul_unit t n


public theorem isTorsionPoint_one_iff (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    G.IsTorsionPoint t 1 x ↔ x = G.one t := by
  show G.nsmul t 1 x = G.one t ↔ x = G.one t
  rw [G.nsmul_one_apply]


public theorem isTorsionPoint_schemeHomOverComp (G : RelativeGroupLaw R f) {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (n : ℕ) {x : SchemeHomOver t f}
    (hx : G.IsTorsionPoint t n x) :
    G.IsTorsionPoint t' n (schemeHomOverComp ψ hψ x) := by
  show G.nsmul t' n (schemeHomOverComp ψ hψ x) = G.one t'
  rw [← G.nsmul_natural t t' ψ hψ n x, hx]
  exact G.one_natural t t' ψ hψ


public theorem mapsTo_torsionSubset_schemeHomOverComp (G : RelativeGroupLaw R f) {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (n : ℕ) :
    Set.MapsTo (schemeHomOverComp ψ hψ) (G.torsionSubset t n) (G.torsionSubset t' n) :=
  fun _ hx => G.isTorsionPoint_schemeHomOverComp t t' ψ hψ n hx

end RelativeGroupLaw

end WeierstrassProjModel
end

set_option autoImplicit false

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra Ideal Scheme WeierstrassCurve

namespace WeierstrassProjModel

namespace RelativeGroupLaw

variable {R : Type u} [CommRing R]
variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}


public theorem schemeNsmul_over (G : RelativeGroupLaw R f) (n : ℕ) :
    G.schemeNsmul n ≫ f = f :=
  (G.nsmul f n idPoint).2


public theorem span_polynomial_isHomogeneousCR (V : WeierstrassCurve.Projective R) :
    (Ideal.span {V.polynomial}).IsHomogeneous (homogeneousSubmodule (Fin 3) R) := by
  refine Ideal.homogeneous_span _ _ ?_
  rintro p hp
  rcases Set.mem_singleton_iff.mp hp with rfl
  exact ⟨3, (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_polynomial V)⟩


@[simp]
public theorem projModelHomogeneousIdealCR_toIdeal (V : WeierstrassCurve.Projective R) :
    (projModelHomogeneousIdealCR V).toIdeal = Ideal.span {V.polynomial} := rfl

