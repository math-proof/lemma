import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.EllipticCurves.code.Isogenies
open Polynomial ProjectiveCurve WeierstrassCurve WeierstrassCurve.Affine Isogeny IsogenyStandardForm IsogenyStandardForm.WithCurveData
open scoped Polynomial.Bivariate
open MvPolynomial


namespace ProjectiveCurve

/--
[dehomogenize_X_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Isogenies.lean)
-/
@[path]
lemma dehomogenize_X_zero
  {k : Type u}
  [CommRing k] :
-- imply
  dehomogenize (MvPolynomial.X (R := k) (0 : Fin 3)) = Polynomial.C Polynomial.X := by
-- proof
  simp [dehomogenize, dehomogenizeHom, MvPolynomial.eval₂Hom_X']

end ProjectiveCurve

namespace ProjectiveCurve

/--
[dehomogenize_X_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Isogenies.lean)
-/
@[path]
lemma dehomogenize_X_one
  {k : Type u}
  [CommRing k] :
-- imply
  dehomogenize (MvPolynomial.X (R := k) (1 : Fin 3)) = (Polynomial.X : k[X][Y]) := by
-- proof
  simp [dehomogenize, dehomogenizeHom, MvPolynomial.eval₂Hom_X']

end ProjectiveCurve

namespace ProjectiveCurve

/--
[dehomogenize_X_two](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Isogenies.lean)
-/
@[path]
lemma dehomogenize_X_two
  {k : Type u}
  [CommRing k] :
-- imply
  dehomogenize (MvPolynomial.X (R := k) (2 : Fin 3)) = (1 : k[X][Y]) := by
-- proof
  simp [dehomogenize, dehomogenizeHom, MvPolynomial.eval₂Hom_X']

end ProjectiveCurve

namespace ProjectiveCurve

/--
[dehomogenize_C](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Isogenies.lean)
-/
@[path]
lemma dehomogenize_C
  {k : Type u}
  [CommRing k]
  {a : k} :
-- imply
  dehomogenize (MvPolynomial.C a : MvPolynomial (Fin 3) k) = Polynomial.C (Polynomial.C a) := by
-- proof
  simp [dehomogenize, dehomogenizeHom]

end ProjectiveCurve

namespace ProjectiveCurve

/--
[AffinePointOver.evalRingHom_mk](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Isogenies.lean)
-/
@[path]
lemma AffinePointOver.evalRingHom_mk
  {k : Type u}
  [CommRing k]
  {f₀ : k[X][Y]}
  {L : Type v}
  [CommRing L]
  [Algebra k L]
  {P : AffinePointOver f₀ L}
  {p : k[X][Y]} :
-- imply
  P.evalRingHom (AdjoinRoot.mk f₀ p) = Polynomial.eval₂ (Polynomial.eval₂RingHom (algebraMap k L) P.x) P.y p :=
-- proof
  AdjoinRoot.lift_mk P.on_curve p

end ProjectiveCurve

namespace ProjectiveCurve

/--
[AffinePoint.evalRingHom_mk](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Isogenies.lean)
-/
@[path]
lemma AffinePoint.evalRingHom_mk
  {k : Type u}
  [CommRing k]
  {f₀ : k[X][Y]}
  {P : AffinePoint f₀}
  {p : k[X][Y]} :
-- imply
  P.evalRingHom (AdjoinRoot.mk f₀ p) = Polynomial.eval₂ (Polynomial.evalRingHom P.x) P.y p :=
-- proof
  AdjoinRoot.lift_mk P.on_curve p

end ProjectiveCurve

namespace ProjectiveCurve

variable {k : Type u} [CommRing k]
variables by setting the third coordinate to `1`, sending `X₀ ↦ X`, `X₁ ↦ Y`,
variable) to `1`. -/
/--
[eval₂RingHom_algebraMap_self](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Isogenies.lean)
-/
@[path]
with `Polynomial.evalRingHom a`, since `algebraMap k k = id`. -/
lemma eval₂RingHom_algebraMap_self (a : k) :
  Polynomial.eval₂RingHom (algebraMap k k) a = Polynomial.evalRingHom a := by
  ext p
  · simp [eval₂_C]
  · simp [eval₂_X]

end ProjectiveCurve

namespace ProjectiveCurve

/--
[Morphism.isMorphism](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Isogenies.lean)
-/
@[path]
lemma Morphism.isMorphism
  {k : Type u}
  [CommRing k]
  {f₁ f₂ : k[X][Y]}
  [IsDomain (CoordinateRing f₁)]
  {φ : Morphism f₁ f₂} :
-- imply
  φ.toRationalMap.IsMorphism :=
-- proof
  φ.regular_everywhere

end ProjectiveCurve

namespace ProjectiveCurve

/--
[mem_projectiveCurvePoints_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Isogenies.lean)
-/
@[path]
lemma mem_projectiveCurvePoints_iff
  {k : Type u}
  [CommRing k]
  {f : MvPolynomial (Fin 3) k}
  [Field L]
  [Algebra k L]
  {P : ProjectivePlane L} :
-- imply
  P ∈ ProjectiveCurvePoints f L ↔ MvPolynomial.aeval P.rep f = 0 :=
-- proof
  Iff.rfl

end ProjectiveCurve

namespace WeierstrassCurve.Affine

/--
[coordinateRing_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Isogenies.lean)
-/
@[path]
lemma coordinateRing_eq
  {F : Type u}
  [Field F]
  {W : WeierstrassCurve.Affine F} :
-- imply
  W.CoordinateRing = ProjectiveCurve.CoordinateRing W.polynomial :=
-- proof
  rfl

end WeierstrassCurve.Affine

namespace Isogeny

/--
[map_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Isogenies.lean)
-/
@[path]
lemma map_add
  {F : Type u}
  [Field F]
  [DecidableEq F]
  {E₁ E₂ E₃ : WeierstrassCurve.Affine F}
  {φ : Isogeny E₁ E₂}
  {P Q : E₁.Point} :
-- imply
  φ (P + Q) = φ P + φ Q :=
-- proof
  φ.toAddMonoidHom.map_add P Q

end Isogeny

namespace Isogeny

/--
[map_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Isogenies.lean)
-/
@[path]
lemma map_zero
  {F : Type u}
  [Field F]
  [DecidableEq F]
  {E₁ E₂ E₃ : WeierstrassCurve.Affine F}
  {φ : Isogeny E₁ E₂} :
-- imply
  φ (0 : E₁.Point) = 0 :=
-- proof
  φ.toAddMonoidHom.map_zero

end Isogeny

namespace Isogeny

/--
[map_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Isogenies.lean)
-/
@[path]
lemma map_neg
  {F : Type u}
  [Field F]
  [DecidableEq F]
  {E₁ E₂ E₃ : WeierstrassCurve.Affine F}
  {φ : Isogeny E₁ E₂}
  {P : E₁.Point} :
-- imply
  φ (-P) = -φ P :=
-- proof
  φ.toAddMonoidHom.map_neg P

end Isogeny

namespace Isogeny

/--
[comp_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Isogenies.lean)
-/
@[path]
lemma comp_apply
  {F : Type u}
  [Field F]
  [DecidableEq F]
  {E₁ E₂ E₃ : WeierstrassCurve.Affine F}
  {ψ : Isogeny E₂ E₃}
  {φ : Isogeny E₁ E₂}
  {P : E₁.Point} :
-- imply
  (comp ψ φ) P = ψ (φ P) :=
-- proof
  rfl

end Isogeny

namespace Isogeny

/--
[id_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Isogenies.lean)
-/
@[path]
lemma id_apply
  {F : Type u}
  [Field F]
  [DecidableEq F]
  {E₁ E₂ E₃ : WeierstrassCurve.Affine F}
  {E : WeierstrassCurve.Affine F}
  {P : E.Point} :
-- imply
  (Isogeny.id E) P = P :=
-- proof
  rfl

end Isogeny

namespace IsogenyStandardForm.WithCurveData

/--
[v_cube_dvd_t_sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Isogenies.lean)
-/
@[path]
lemma v_cube_dvd_t_sq
  {F : Type u}
  [Field F]
  {α : WithCurveData F} :
-- imply
  α.v ^ 3 ∣ α.t ^ 2 := by
-- proof
  have hvw : IsCoprime (α.v ^ 3) α.w := α.coprime_vw.pow_left
  have hdvd : α.v ^ 3 ∣ α.t ^ 2 * α.w := ⟨α.s ^ 2 * α.f₁, α.identity.symm⟩
  exact hvw.dvd_of_dvd_mul_right hdvd

end IsogenyStandardForm.WithCurveData

namespace IsogenyStandardForm.WithCurveData

variable {F : Type u} [Field F]
variable (α : WithCurveData F)
/--
[t_sq_dvd_v_cube_f₁](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Isogenies.lean)
-/
@[path]
`t² ∣ v³·f₁`. -/
lemma t_sq_dvd_v_cube_f₁ : α.t ^ 2 ∣ α.v ^ 3 * α.f₁ := by
  have hst : IsCoprime (α.t ^ 2) (α.s ^ 2) := α.coprime_st.symm.pow
  have h1 : α.t ^ 2 ∣ α.v ^ 3 * α.f₁ * α.s ^ 2 := by
    rw [show α.v ^ 3 * α.f₁ * α.s ^ 2 = α.v ^ 3 * (α.s ^ 2 * α.f₁) from by ring]
    exact ⟨α.w, α.identity⟩
  exact hst.dvd_of_dvd_mul_right h1

end IsogenyStandardForm.WithCurveData

namespace IsogenyStandardForm.WithCurveData

/--
[isRoot_t_of_isRoot_v](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Isogenies.lean)
-/
@[path]
lemma isRoot_t_of_isRoot_v
  {F : Type u}
  [Field F]
  {α : WithCurveData F}
  {x₀ : F}
-- given
  (hv : Polynomial.IsRoot α.v x₀) :
-- imply
  Polynomial.IsRoot α.t x₀ := by
-- proof
  rw [← Polynomial.dvd_iff_isRoot] at hv ⊢
  have hprime : Prime (Polynomial.X - Polynomial.C x₀) :=
    Polynomial.prime_X_sub_C x₀
  have h1 : (Polynomial.X - Polynomial.C x₀) ^ 3 ∣ α.t ^ 2 :=
    dvd_trans (pow_dvd_pow_of_dvd hv 3) α.v_cube_dvd_t_sq
  have h2 : (Polynomial.X - Polynomial.C x₀) ∣ α.t ^ 2 :=
    dvd_trans (dvd_pow_self _ (by norm_num : 3 ≠ 0)) h1
  exact hprime.dvd_of_dvd_pow h2

end IsogenyStandardForm.WithCurveData

namespace IsogenyStandardForm.WithCurveData

/--
[isRoot_v_of_isRoot_t](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Isogenies.lean)
-/
@[path]
lemma isRoot_v_of_isRoot_t
  {F : Type u}
  [Field F]
  {α : WithCurveData F}
  {x₀ : F}
-- given
  (ht : Polynomial.IsRoot α.t x₀) :
-- imply
  Polynomial.IsRoot α.v x₀ := by
-- proof
  rw [← Polynomial.dvd_iff_isRoot] at ht ⊢
  set p := Polynomial.X - Polynomial.C x₀ with hp_def
  have hprime : Prime p := Polynomial.prime_X_sub_C x₀
  have hpne : p ≠ 0 := Polynomial.X_sub_C_ne_zero x₀
  have h1 : p ^ 2 ∣ α.v ^ 3 * α.f₁ :=
    dvd_trans (pow_dvd_pow_of_dvd ht 2) α.t_sq_dvd_v_cube_f₁
  have h2 : p ∣ α.v ^ 3 * α.f₁ :=
    dvd_trans (dvd_pow_self _ (by norm_num : 2 ≠ 0)) h1
  obtain h3 | h3 := hprime.dvd_or_dvd h2
  ·
    exact hprime.dvd_of_dvd_pow h3
  ·
    obtain ⟨g, hg⟩ := h3
    have h1' : p ^ 2 ∣ α.v ^ 3 * (p * g) := hg ▸ h1
    have h1'' : p ^ 2 ∣ p * (α.v ^ 3 * g) := by rwa [show α.v ^ 3 * (p * g) = p * (α.v ^ 3 * g) from by ring] at h1'
    have h4 : p ∣ α.v ^ 3 * g := by
      rw [pow_succ, pow_one] at h1''
      exact (mul_dvd_mul_iff_left hpne).mp h1''
    obtain h5 | h5 := hprime.dvd_or_dvd h4
    · exact hprime.dvd_of_dvd_pow h5
    · exfalso
      have hsq : p * p ∣ α.f₁ := hg ▸ mul_dvd_mul_left _ h5
      exact Polynomial.not_isUnit_X_sub_C x₀ (α.squarefree_f₁ _ hsq)

end IsogenyStandardForm.WithCurveData

namespace IsogenyStandardForm.WithCurveData

/--
[isRoot_v_iff_isRoot_t](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Isogenies.lean)
-/
@[path]
lemma isRoot_v_iff_isRoot_t
  {F : Type u}
  [Field F]
  {α : WithCurveData F}
  {x₀ : F} :
-- imply
  Polynomial.IsRoot α.v x₀ ↔ Polynomial.IsRoot α.t x₀ :=
-- proof
  ⟨α.isRoot_t_of_isRoot_v, α.isRoot_v_of_isRoot_t⟩
namespace ProjectiveCurve
open MvPolynomial

end IsogenyStandardForm.WithCurveData

namespace Isogeny

/--
[not_in_kernel_of_v_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Isogenies.lean)
-/
@[path]
lemma not_in_kernel_of_v_ne_zero
  {E}
  {F : Type u}
  [Field F]
  [DecidableEq F]
  {E₁ E₂ : WeierstrassCurve.Affine F}
  {α : Isogeny E₁ E₂}
  {rep : IsogenyRepresentation E₁ E₂ α}
  {x₀ y₀ : F}
-- given
  (_hE₁ : E₁.IsShortWeierstrass)
  (_hE₂ : E₂.IsShortWeierstrass)
  (h₁ : E₁.Nonsingular x₀ y₀)
  (hv : eval x₀ rep.v ≠ 0) :
-- imply
  α (WeierstrassCurve.Affine.Point.some x₀ y₀ h₁) ≠ 0 := by
-- proof
  obtain ⟨h₂, hrep⟩ := rep.represents x₀ y₀ h₁ hv
  show α.toAddMonoidHom (WeierstrassCurve.Affine.Point.some x₀ y₀ h₁) ≠ 0
  rw [hrep]
  exact WeierstrassCurve.Affine.Point.some_ne_zero h₂

end Isogeny

namespace Isogeny

/--
[in_kernel_of_v_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Isogenies.lean)
-/
@[path]
lemma in_kernel_of_v_eq_zero
  {E}
  {F : Type u}
  [Field F]
  [DecidableEq F]
  {E₁ E₂ : WeierstrassCurve.Affine F}
  {F : Type u}
  [Field F]
  [DecidableEq F]
  {E₁ E₂ : WeierstrassCurve.Affine F}
  {α : Isogeny E₁ E₂}
  {rep : IsogenyRepresentation E₁ E₂ α}
  {x₀ y₀ : F}
-- given
  (_hE₁ : E₁.IsShortWeierstrass)
  (_hE₂ : E₂.IsShortWeierstrass)
  (h₁ : E₁.Nonsingular x₀ y₀)
  (hv : eval x₀ rep.v = 0) :
-- imply
  α (WeierstrassCurve.Affine.Point.some x₀ y₀ h₁) = 0 := by
-- proof
  have hu : eval x₀ rep.u ≠ 0 := by
    intro hu_eq
    have hdvd_u : (Polynomial.X - Polynomial.C x₀) ∣ rep.u :=
      Polynomial.dvd_iff_isRoot.mpr hu_eq
    have hdvd_v : (Polynomial.X - Polynomial.C x₀) ∣ rep.v :=
      Polynomial.dvd_iff_isRoot.mpr hv
    exact (Polynomial.irreducible_X_sub_C x₀).not_isUnit
      (rep.coprime_uv.isUnit_of_dvd' hdvd_u hdvd_v)
  exact rep.maps_poles_to_zero x₀ y₀ h₁ hv hu

end Isogeny

namespace Isogeny

/--
[kernel_iff_v_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Isogenies.lean)
-/
@[path]
lemma kernel_iff_v_eq_zero
  {E}
  {F : Type u}
  [Field F]
  [DecidableEq F]
  {E₁ E₂ : WeierstrassCurve.Affine F}
  {α : Isogeny E₁ E₂}
  {rep : IsogenyRepresentation E₁ E₂ α}
  {x₀ y₀ : F}
-- given
  (hE₁ : E₁.IsShortWeierstrass)
  (hE₂ : E₂.IsShortWeierstrass)
  (h₁ : E₁.Nonsingular x₀ y₀) :
-- imply
  α (WeierstrassCurve.Affine.Point.some x₀ y₀ h₁) = 0 ↔ eval x₀ rep.v = 0 := by
-- proof
  constructor
  ·
    intro hker
    by_contra hv
    exact not_in_kernel_of_v_ne_zero hE₁ hE₂ α rep x₀ y₀ h₁ hv hker
  ·
    exact in_kernel_of_v_eq_zero hE₁ hE₂ α rep x₀ y₀ h₁

end Isogeny

namespace Isogeny

/--
[finite_nonsingular_fibers](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Isogenies.lean)
-/
@[path]
lemma finite_nonsingular_fibers
  {E}
  {F : Type u}
  [Field F]
  [DecidableEq F]
  {E₁ E₂ : WeierstrassCurve.Affine F}
  {x₀ : F} :
-- imply
  Set.Finite {y : F | E₁.Nonsingular x₀ y} := by
-- proof
  have hmonic : (Polynomial.map (evalRingHom x₀) E₁.polynomial).Monic :=
    WeierstrassCurve.Affine.monic_polynomial.map _
  have hne : Polynomial.map (evalRingHom x₀) E₁.polynomial ≠ 0 := hmonic.ne_zero
  have hsub : {y : F | E₁.Nonsingular x₀ y} ⊆
    {y : F | (Polynomial.map (evalRingHom x₀) E₁.polynomial).IsRoot y} := by
    intro y hy
    simp only [Set.mem_setOf_eq, Polynomial.IsRoot] at hy ⊢
    rwa [Polynomial.map_evalRingHom_eval]
  exact (Polynomial.finite_setOf_isRoot hne).subset hsub

end Isogeny

namespace Isogeny

/--
[pointToCoords_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Isogenies.lean)
-/
@[path]
lemma pointToCoords_injective
  {E}
  {F : Type u}
  [Field F]
  [DecidableEq F]
  {E₁ E₂ : WeierstrassCurve.Affine F} :
-- imply
  Function.Injective (pointToCoords (E₁ := E₁)) := by
-- proof
  intro P Q h
  cases P with
  | zero => cases Q with
    | zero => rfl
    | some x y hxy => simp [pointToCoords] at h
  | some x y hxy => cases Q with
    | zero => simp [pointToCoords] at h
    | some x' y' hxy' =>
      simp [pointToCoords] at h
      obtain ⟨hx, hy⟩ := h
      subst hx; subst hy; rfl

end Isogeny

namespace Isogeny

/--
[isogeny_kernel_finite_of_rep](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Isogenies.lean)
-/
@[path]
lemma isogeny_kernel_finite_of_rep
  {E}
  {F : Type u}
  [Field F]
  [DecidableEq F]
  {E₁ E₂ : WeierstrassCurve.Affine F}
  {α : Isogeny E₁ E₂}
  {rep : IsogenyRepresentation E₁ E₂ α}
-- given
  (hE₁ : E₁.IsShortWeierstrass)
  (hE₂ : E₂.IsShortWeierstrass) :
-- imply
  Set.Finite {P : E₁.Point | α P = 0} := by
-- proof
  apply Set.Finite.of_finite_image (f := pointToCoords)
  ·
    apply Set.Finite.subset (s := {none} ∪
      Option.some '' (⋃ x₀ ∈ {x | rep.v.IsRoot x}, {x₀} ×ˢ {y | E₁.Nonsingular x₀ y}))
    ·
      apply Set.Finite.union
      · exact Set.finite_singleton none
      · apply Set.Finite.image
        exact (Polynomial.finite_setOf_isRoot rep.v_ne_zero).biUnion
          (fun x₀ _ => Set.Finite.prod (Set.finite_singleton x₀)
            (finite_nonsingular_fibers x₀))
    ·
      intro z hz
      obtain ⟨P, hP, rfl⟩ := hz
      simp only [Set.mem_setOf_eq] at hP
      cases P with
      | zero => exact Set.mem_union_left _ (Set.mem_singleton _)
      | some x₀ y₀ h₁ =>
        apply Set.mem_union_right
        refine ⟨(x₀, y₀), ?_, rfl⟩
        simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_prod, Set.mem_singleton_iff]
        exact ⟨x₀, (kernel_iff_v_eq_zero hE₁ hE₂ α rep x₀ y₀ h₁).mp hP, rfl, h₁⟩
  ·
    exact pointToCoords_injective.injOn
/-- Corollary: the kernel of any isogeny between short Weierstrass curves is a
finite set of points. Combined with `isogeny_standard_form`, this is a key
finiteness statement underlying the degree theory of isogenies. -/

end Isogeny

/--
[eval](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Isogenies.lean)
-/
@[path]
private lemma eval_eq
  {k : Type u}
  [CommRing k]
  {a : k} :
-- imply
  Polynomial.eval₂RingHom (algebraMap k k) a = Polynomial.evalRingHom a := by
-- proof
  apply ProjectiveCurve.eval a

/--
[t_sq_dvd_v_cube_f](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Isogenies.lean)
-/
@[path]
private lemma t_sq_dvd_v_cube_f_eq
  {F : Type u}
  [Field F]
  {α : WithCurveData F} :
-- imply
  α.t ^ 2 ∣ α.v ^ 3 * α.f₁ := by
-- proof
  apply IsogenyStandardForm.WithCurveData.t_sq_dvd_v_cube_f α

/--
[RationalMapTriple.isEquiv_refl](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Isogenies.lean)
-/
@[path]
private lemma isEquiv_refl_eq
  {k : Type u}
  [CommRing k]
  {f₁ f₂ : MvPolynomial (Fin 3) k}
  {t : RationalMapTriple f₁ f₂} :
-- imply
  t.IsEquiv t := by
-- proof
  apply ProjectiveCurve.RationalMapTriple.isEquiv_refl t

/--
[RationalMapTriple.isEquiv_symm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Isogenies.lean)
-/
@[path]
private lemma isEquiv_symm_eq
  {k : Type u}
  [CommRing k]
  {f₁ f₂ : MvPolynomial (Fin 3) k}
  {t₁ t₂ : RationalMapTriple f₁ f₂}
-- given
  (h : t₁.IsEquiv t₂) :
-- imply
  t₂.IsEquiv t₁ := by
-- proof
  apply ProjectiveCurve.RationalMapTriple.isEquiv_symm h

/--
[RationalMapTriple.isEquiv_trans_of_prime](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Isogenies.lean)
-/
@[path]
private lemma isEquiv_trans_of_prime_eq
  {k : Type u}
  [CommRing k]
  {f₁ f₂ : MvPolynomial (Fin 3) k}
  {t₁ t₂ t₃ : RationalMapTriple f₁ f₂}
-- given
  (hprime : (Ideal.span ({f₁} : Set (MvPolynomial (Fin 3) k))).IsPrime)
  (h12 : t₁.IsEquiv t₂)
  (h23 : t₂.IsEquiv t₃) :
-- imply
  t₁.IsEquiv t₃ := by
-- proof
  apply ProjectiveCurve.RationalMapTriple.isEquiv_trans_of_prime hprime h12 h23


-- created on 2026-10-23
