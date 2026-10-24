import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.Divisors
open CurveDivisor ClosedPoint CurveWithOrd CurveWithConstants CurveMorphismData ArithmeticGeometry
open CurveWithOrd
open CurveWithOrd CurveDivisor
open CurveDivisor CurveWithConstants


namespace CurveDivisor

/--
[degree_single](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Divisors.lean)
-/
@[path]
lemma degree_single
  (C)
  {P : C}
  {n : ℤ} :
-- imply
  degree C (Finsupp.single P n) = n := by
-- proof
  simp [degree]

end CurveDivisor

namespace CurveDivisor

/--
[degree_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Divisors.lean)
-/
@[path]
lemma degree_zero
  (C) :
-- imply
  degree C (0 : CurveDivisor C) = 0 :=
-- proof
  map_zero _

end CurveDivisor

namespace CurveDivisor

/--
[degree_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Divisors.lean)
-/
@[path]
lemma degree_add
  (C)
  {D₁ D₂ : CurveDivisor C} :
-- imply
  degree C (D₁ + D₂) = degree C D₁ + degree C D₂ :=
-- proof
  map_add _ _ _

end CurveDivisor

namespace CurveDivisor

/--
[degree_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Divisors.lean)
-/
@[path]
lemma degree_neg
  (C)
  {D : CurveDivisor C} :
-- imply
  degree C (-D) = -(degree C D) :=
-- proof
  map_neg _ _

end CurveDivisor

namespace CurveDivisor

/--
[degree_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Divisors.lean)
-/
@[path]
lemma degree_sub
  (C)
  {D₁ D₂ : CurveDivisor C} :
-- imply
  degree C (D₁ - D₂) = degree C D₁ - degree C D₂ :=
-- proof
  map_sub _ _ _

end CurveDivisor

namespace CurveDivisor

/--
[degree_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Divisors.lean)
-/
@[path]
lemma degree_eq_sum
  (C)
  {D : CurveDivisor C} :
-- imply
  degree C D = D.sum (fun _ n => n) := by
-- proof
  simp [degree, Finsupp.liftAddHom_apply]
  rfl

end CurveDivisor

namespace CurveDivisor

/--
[degreeWeighted_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Divisors.lean)
-/
@[path]
lemma degreeWeighted_sub
  (C)
  {deg : C → ℕ}
  {D₁ D₂ : CurveDivisor C} :
-- imply
  degreeWeighted deg (D₁ - D₂) = degreeWeighted deg D₁ - degreeWeighted deg D₂ :=
-- proof
  map_sub _ _ _

end CurveDivisor

namespace CurveDivisor

/--
[degreeWeighted_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Divisors.lean)
-/
@[path]
lemma degreeWeighted_eq_sum
  (C)
  {deg : C → ℕ}
  {D : CurveDivisor C} :
-- imply
  degreeWeighted deg D = D.sum (fun p n => n * (deg p : ℤ)) := by
-- proof
  simp only [degreeWeighted, Finsupp.liftAddHom_apply, Finsupp.sum]
  congr 1
  ext p
  simp [mul_comm]

end CurveDivisor

namespace CurveDivisor

/--
[divZeros_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Divisors.lean)
-/
@[path]
lemma divZeros_apply
  (C)
  {D : CurveDivisor C}
  {P : C} :
-- imply
  divZeros D P = max (D P) 0 := by
-- proof
  simp [divZeros, Finsupp.sup_apply, Finsupp.coe_zero]

end CurveDivisor

namespace CurveDivisor

/--
[divPoles_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Divisors.lean)
-/
@[path]
lemma divPoles_apply
  (C)
  {D : CurveDivisor C}
  {P : C} :
-- imply
  divPoles D P = max (-(D P)) 0 := by
-- proof
  simp [divPoles, Finsupp.sup_apply, Finsupp.coe_zero, Finsupp.neg_apply]

end CurveDivisor

namespace CurveDivisor

/--
[divZeros_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Divisors.lean)
-/
@[path]
lemma divZeros_nonneg
  (C)
  {D : CurveDivisor C}
  {P : C} :
-- imply
  0 ≤ divZeros D P := by
-- proof
  simp

end CurveDivisor

namespace CurveDivisor

/--
[divPoles_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Divisors.lean)
-/
@[path]
lemma divPoles_nonneg
  (C)
  {D : CurveDivisor C}
  {P : C} :
-- imply
  0 ≤ divPoles D P := by
-- proof
  simp

end CurveDivisor

namespace CurveDivisor

/--
[eq_divZeros_sub_divPoles](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Divisors.lean)
-/
@[path]
lemma eq_divZeros_sub_divPoles
  (C)
  {D : CurveDivisor C} :
-- imply
  D = divZeros D - divPoles D := by
-- proof
  ext P
  simp [Finsupp.sub_apply]

end CurveDivisor

namespace ClosedPoint

/--
[mk_eq_mk_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Divisors.lean)
-/
@[path]
lemma mk_eq_mk_iff
  [Group G]
  [MulAction G C]
  {P Q : C} :
-- imply
  mk (G := G) P = mk Q ↔ P ∈ MulAction.orbit G Q := by
-- proof
  simp only [mk]
  constructor
  · intro h
    exact MulAction.orbitRel_apply.mp (Quotient.exact' h)
  · intro h
    exact Quotient.sound' (MulAction.orbitRel_apply.mpr h)

end ClosedPoint

namespace CurveWithOrd

/--
[isPrincipal_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Divisors.lean)
-/
@[path]
lemma isPrincipal_iff
  [Field F]
  [FunctionFieldCurve C F]
  {D : CurveDivisor C} :
-- imply
  IsPrincipal (F := F) D ↔ ∃ f : Fˣ, principalDivisor f = D := by
-- proof
  simp [IsPrincipal, principalDivisors, Set.mem_range]
end CurveWithOrd
namespace CurveWithOrd

end CurveWithOrd

namespace CurveWithOrd

/--
[exact_at_divisors](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Divisors.lean)
-/
@[path]
lemma exact_at_divisors
  [Field F]
  [FunctionFieldCurve C F] :
-- imply
  AddMonoidHom.range (divAddHom (C := C) (F := F)) = (toPicardGroup (C := C) (F := F)).ker := by
-- proof
  rw [toPicardGroup, QuotientAddGroup.ker_mk']
  ext D
  simp only [AddMonoidHom.mem_range, principalDivisors]
  constructor
  · rintro ⟨f, rfl⟩; exact ⟨Additive.toMul f, rfl⟩
  · rintro ⟨f, rfl⟩; exact ⟨Additive.ofMul f, rfl⟩

end CurveWithOrd

namespace CurveWithOrd

/--
[ker_toPicardGroup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Divisors.lean)
-/
@[path]
lemma ker_toPicardGroup
  [Field F]
  [FunctionFieldCurve C F] :
-- imply
  (toPicardGroup (C := C) (F := F)).ker = principalDivisors (F := F) :=
-- proof
  QuotientAddGroup.ker_mk' _

end CurveWithOrd

/--
[CurveWithConstants.ker_div_eq_constants](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Divisors.lean)
-/
@[path]
lemma CurveWithConstants.ker_div_eq_constants
  [Field k]
  [Field F]
  [Algebra k F]
  [inst : CurveWithConstants C k F]
  {f : Fˣ}
-- given
  (hf : ∀ P : C, CurveWithOrd.ord P f = 0) :
-- imply
  ∃ a : kˣ, Units.map (algebraMap k F).toMonoidHom a = f := by
-- proof
  have h_alg : IsAlgebraic k (f : F) := inst.ord_zero_algebraic f hf
  obtain ⟨a, ha⟩ := inst.algClosed_in_extension (f : F) h_alg
  have ha_ne : a ≠ 0 := by
    intro h
    rw [h, map_zero] at ha
    exact Units.ne_zero f ha.symm
  exact ⟨Units.mk0 a ha_ne, Units.ext (by simp [Units.coe_map, ha])⟩
namespace CurveWithConstants
variable {C : Type*} {k : Type*} {F : Type*} [Field k] [Field F]
  [Algebra k F] [CurveWithConstants C k F]
open CurveWithOrd

namespace CurveWithConstants

/--
[constantsEmb_def](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Divisors.lean)
-/
@[path]
lemma constantsEmb_def
  [Field k]
  [Field F]
  {a : kˣ} :
-- imply
  (constantsEmb (k := k) (F := F) a : Fˣ) = Units.map (algebraMap k F).toMonoidHom a :=
-- proof
  rfl

end CurveWithConstants

namespace CurveWithConstants

/--
[constantsEmb_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Divisors.lean)
-/
@[path]
lemma constantsEmb_injective
  [Field k]
  [Field F] :
-- imply
  Function.Injective (constantsEmb (k := k) (F := F)) := by
-- proof
  intro a b h
  ext
  have := congr_arg Units.val h
  simp only [constantsEmb, Units.coe_map] at this
  exact (algebraMap k F).injective this

end CurveWithConstants

namespace CurveWithConstants

/--
[principalDivisor_constant](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Divisors.lean)
-/
@[path]
lemma principalDivisor_constant
  [Field k]
  [Field F]
  {a : kˣ} :
-- imply
  principalDivisor (C := C) (constantsEmb (F := F) a) = 0 := by
-- proof
  ext P
  simp only [principalDivisor_apply, Finsupp.coe_zero, Pi.zero_apply,
    constantsEmb_def, ord_constant]

end CurveWithConstants

namespace CurveWithConstants

/--
[exact_at_functionField](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Divisors.lean)
-/
@[path]
lemma exact_at_functionField
  [Field k]
  [Field F]
  {f : Fˣ} :
-- imply
  principalDivisor (C := C) f = 0 ↔ ∃ a : kˣ, constantsEmb (F := F) a = f := by
-- proof
  constructor
  · intro hf
    have hord : ∀ P : C, ord P f = 0 := by
      intro P
      have := Finsupp.ext_iff.mp hf P
      simp at this
      exact this
    exact ker_div_eq_constants f hord
  · rintro ⟨a, rfl⟩
    exact principalDivisor_constant a
end CurveWithConstants
section TriangleEquality

end CurveWithConstants

/--
[triangle_equality_valuation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Divisors.lean)
-/
@[path]
lemma triangle_equality_valuation
  [Field F]
  [LinearOrderedAddCommMonoidWithTop Γ₀]
  {v : AddValuation F Γ₀}
  {x y : F}
-- given
  (h : v x ≠ v y) :
-- imply
  v (x + y) = min (v x) (v y) := by
-- proof
  obtain hlt | hlt := Ne.lt_or_gt h
  ·
    rw [min_eq_left hlt.le]
    have h_le : v x ≤ v (x + y) := by
      have := AddValuation.map_add v x y
      rwa [min_eq_left hlt.le] at this
    by_contra h_ne
    have h_strict : v x < v (x + y) := lt_of_le_of_ne h_le (Ne.symm h_ne)
    have key : min (v (x + y)) (v (-y)) ≤ v ((x + y) + (-y)) :=
      AddValuation.map_add v (x + y) (-y)
    rw [AddValuation.map_neg, show (x + y) + (-y) = x from by ring] at key
    exact absurd (lt_min h_strict hlt) (not_lt.mpr key)
  ·
    rw [add_comm, min_comm, min_eq_left hlt.le]
    have h_le : v y ≤ v (y + x) := by
      have := AddValuation.map_add v y x
      rwa [min_eq_left hlt.le] at this
    by_contra h_ne
    have h_strict : v y < v (y + x) := lt_of_le_of_ne h_le (Ne.symm h_ne)
    have key : min (v (y + x)) (v (-x)) ≤ v ((y + x) + (-x)) :=
      AddValuation.map_add v (y + x) (-x)
    rw [AddValuation.map_neg, show (y + x) + (-x) = y from by ring] at key
    exact absurd (lt_min h_strict hlt) (not_lt.mpr key)

namespace CurveWithConstants

/--
[divZeros_principalDivisor_constant](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Divisors.lean)
-/
@[path]
lemma divZeros_principalDivisor_constant
  [Field k]
  [Field F]
  {a : kˣ} :
-- imply
  divZeros (principalDivisor (C := C) (constantsEmb (F := F) a)) = 0 := by
-- proof
  have h := principalDivisor_constant (C := C) (F := F) (k := k) a
  rw [h]
  ext P
  simp [divZeros]

end CurveWithConstants

namespace CurveWithConstants

/--
[divPoles_principalDivisor_constant](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Divisors.lean)
-/
@[path]
lemma divPoles_principalDivisor_constant
  [Field k]
  [Field F]
  {a : kˣ} :
-- imply
  divPoles (principalDivisor (C := C) (constantsEmb (F := F) a)) = 0 := by
-- proof
  have h := principalDivisor_constant (C := C) (F := F) (k := k) a
  rw [h]
  ext P
  simp [divPoles]

end CurveWithConstants

namespace CurveWithConstants

/--
[degree_divZeros_principalDivisor_constant](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Divisors.lean)
-/
@[path]
lemma degree_divZeros_principalDivisor_constant
  [Field k]
  [Field F]
  {a : kˣ} :
-- imply
  degree C (divZeros (principalDivisor (C := C) (constantsEmb (F := F) a))) = 0 := by
-- proof
  rwa [divZeros_principalDivisor_constant a]

end CurveWithConstants

namespace CurveWithConstants

/--
[degree_divPoles_principalDivisor_constant](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Divisors.lean)
-/
@[path]
lemma degree_divPoles_principalDivisor_constant
  [Field k]
  [Field F]
  {a : kˣ} :
-- imply
  degree C (divPoles (principalDivisor (C := C) (constantsEmb (F := F) a))) = 0 := by
-- proof
  rwa [divPoles_principalDivisor_constant a]

end CurveWithConstants

namespace CurveWithConstants

/--
[degree_divZeros_principalDivisor_eq_sum_ord](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Divisors.lean)
-/
@[path]
lemma degree_divZeros_principalDivisor_eq_sum_ord
  [Field k]
  [Field F]
  {f : Fˣ} :
-- imply
  degree C (divZeros (principalDivisor (C := C) f)) = (divZeros (principalDivisor (C := C) f)).support.sum (fun P => ord P f) := by
-- proof
  simp only [degree, Finsupp.liftAddHom_apply]
  rw [Finsupp.sum]
  apply Finset.sum_congr rfl
  intro P hP
  have hne : (divZeros (principalDivisor (C := C) f)) P ≠ 0 :=
    Finsupp.mem_support_iff.mp hP
  simp only [divZeros_apply, principalDivisor_apply, AddMonoidHom.id_apply] at hne ⊢
  omega

end CurveWithConstants

namespace CurveWithConstants

/--
[nonconstant_transcendental](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Divisors.lean)
-/
@[path]
lemma nonconstant_transcendental
  [Field k]
  [Field F]
  [Field k]
  [Field F]
  [Algebra k F]
  [CurveWithConstants C k F]
  {f : Fˣ}
-- given
  (hf : ¬ ∃ a : kˣ, constantsEmb (F := F) a = f) :
-- imply
  Transcendental k (f : F) := by
-- proof
  intro h_alg
  apply hf
  obtain ⟨a, ha⟩ := algClosed_in_extension C (f : F) h_alg
  have ha_ne : a ≠ 0 := by
    intro h; rw [h, map_zero] at ha; exact Units.ne_zero f ha.symm
  exact ⟨Units.mk0 a ha_ne, Units.ext (by simp [constantsEmb, Units.coe_map, ha])⟩

end CurveWithConstants

namespace CurveWithConstants

/--
[divPoles_eq_divZeros_inv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Divisors.lean)
-/
@[path]
lemma divPoles_eq_divZeros_inv
  [Field k]
  [Field F]
  {f : Fˣ} :
-- imply
  divPoles (principalDivisor (C := C) f) = divZeros (principalDivisor (C := C) f⁻¹) := by
-- proof
  rw [principalDivisor_inv]
  rfl

end CurveWithConstants

namespace CurveWithConstants

/--
[not_constant_inv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Divisors.lean)
-/
@[path]
lemma not_constant_inv
  [Field k]
  [Field F]
  {f : Fˣ}
-- given
  (hf : ¬ ∃ a : kˣ, constantsEmb (F := F) a = f) :
-- imply
  ¬ ∃ a : kˣ, constantsEmb (F := F) a = f⁻¹ := by
-- proof
  intro ⟨a, ha⟩
  apply hf
  exact ⟨a⁻¹, by
    have : constantsEmb (F := F) a⁻¹ = (constantsEmb (F := F) a)⁻¹ :=
      map_inv (constantsEmb (F := F)) a
    rw [this, ha, inv_inv]⟩

end CurveWithConstants

namespace CurveWithConstants

/--
[adjoin_inv_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Divisors.lean)
-/
@[path]
lemma adjoin_inv_eq
  [Field k]
  [Field F]
  {f : Fˣ} :
-- imply
  IntermediateField.adjoin k ({((f⁻¹ : Fˣ) : F)} : Set F) = IntermediateField.adjoin k ({(f : F)} : Set F) := by
-- proof
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    rw [hx, Units.val_inv_eq_inv_val]
    exact (IntermediateField.adjoin k ({(f : F)} : Set F)).inv_mem
      (IntermediateField.subset_adjoin k _ (Set.mem_singleton _))
  · rw [IntermediateField.adjoin_le_iff]
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    rw [hx]
    have : ((f⁻¹ : Fˣ) : F)⁻¹ = (f : F) := by
      rw [Units.val_inv_eq_inv_val, inv_inv]
    rw [← this]
    exact (IntermediateField.adjoin k ({((f⁻¹ : Fˣ) : F)} : Set F)).inv_mem
      (IntermediateField.subset_adjoin k _ (Set.mem_singleton _))
end CurveWithConstants
namespace CurveWithOrd
variable {C : Type*} {k : Type*} {F : Type*} [Field k] [Field F]
  [Algebra k F] [CurveWithConstants C k F]
open CurveDivisor CurveWithConstants
end CurveWithOrd


namespace CurveMorphismData

/--
[pushforward_single](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Divisors.lean)
-/
@[path]
lemma pushforward_single
  {φ : CurveMorphismData C₁ C₂}
  {P : C₁}
  {n : ℤ} :
-- imply
  φ.pushforward (Finsupp.single P n) = Finsupp.single (φ.toFun P) n := by
-- proof
  simp [pushforward]

end CurveMorphismData

namespace ArithmeticGeometry

/--
[Pic0_trivial_imp_iso_P1_of_two_rational_points](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Divisors.lean)
-/
@[path]
lemma Pic0_trivial_imp_iso_P1_of_two_rational_points
  [Field k]
  {C : SmoothProjectiveCurve k}
  {P Q : C.RatPoint}
-- given
  (htriv : C.Pic0IsTrivial)
  (hPQ : P ≠ Q) :
-- imply
  C.IsIsomorphicToP1 := by
-- proof
  obtain ⟨f, hf_ne, hf_div⟩ := principal_of_Pic0_trivial C htriv P Q
  exact degree_one_morphism_is_iso C hPQ hf_ne hf_div

end ArithmeticGeometry

namespace ArithmeticGeometry

/--
[iso_P1_iff_Pic0_trivial_of_two_rational_points](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Divisors.lean)
-/
@[path]
lemma iso_P1_iff_Pic0_trivial_of_two_rational_points
  [Field k]
  {C : SmoothProjectiveCurve k}
-- given
  (hpts : ∃ P Q : C.RatPoint, P ≠ Q) :
-- imply
  C.IsIsomorphicToP1 ↔ C.Pic0IsTrivial := by
-- proof
  constructor
  · exact P1_Pic0_trivial C
  · intro htriv
    obtain ⟨P, Q, hPQ⟩ := hpts
    exact Pic0_trivial_imp_iso_P1_of_two_rational_points C htriv hPQ

end ArithmeticGeometry

/--
[FunctionFieldCurve.coordRing_finite_support](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Divisors.lean)
-/
@[path]
private lemma coordRing_finite_support_eq
  [Field F]
  [inst : FunctionFieldCurve C F]
  {f : Fˣ}
-- given
  (hf : inst.isCoordRingElem f) :
-- imply
  (Function.support (fun P => CurveWithOrd.ord (C := C) (F := F) P f)).Finite := by
-- proof
  apply FunctionFieldCurve.coordRing_finite_support f hf

/--
[ord_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Divisors.lean)
-/
@[path]
private lemma ord_one_eq
  [Field F]
  [CurveWithOrd C F]
  {P : C} :
-- imply
  ord (F := F) P 1 = 0 := by
-- proof
  apply CurveWithOrd.ord_one P

/--
[ord_inv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Divisors.lean)
-/
@[path]
private lemma ord_inv_eq
  [Field F]
  [CurveWithOrd C F]
  {P : C}
  {f : Fˣ} :
-- imply
  ord (F := F) P f⁻¹ = -ord P f := by
-- proof
  apply CurveWithOrd.ord_inv P f

/--
[ord_finite_support](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Divisors.lean)
-/
@[path]
private lemma ord_finite_support_eq
  [Field F]
  [FunctionFieldCurve C F]
  {f : Fˣ} :
-- imply
  (Function.support (fun P => CurveWithOrd.ord (C := C) (F := F) P f)).Finite := by
-- proof
  apply ord_finite_support f

/--
[principalDivisor_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Divisors.lean)
-/
@[path]
private lemma principalDivisor_apply_eq
  [Field F]
  [FunctionFieldCurve C F]
  {f : Fˣ}
  {P : C} :
-- imply
  (principalDivisor f : CurveDivisor C) P = ord P f := by
-- proof
  apply CurveWithOrd.principalDivisor_apply f P

/--
[principalDivisor_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Divisors.lean)
-/
@[path]
private lemma principalDivisor_one_eq
  [Field F]
  [FunctionFieldCurve C F] :
-- imply
  principalDivisor (C := C) (F := F) (1 : Fˣ) = 0 := by
-- proof
  apply CurveWithOrd.principalDivisor_one

/--
[principalDivisor_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Divisors.lean)
-/
@[path]
private lemma principalDivisor_mul_eq
  [Field F]
  [FunctionFieldCurve C F]
  {f g : Fˣ} :
-- imply
  principalDivisor (C := C) (f * g) = principalDivisor f + principalDivisor g := by
-- proof
  apply CurveWithOrd.principalDivisor_mul f g

/--
[principalDivisor_inv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Divisors.lean)
-/
@[path]
private lemma principalDivisor_inv_eq
  [Field F]
  [FunctionFieldCurve C F]
  {f : Fˣ} :
-- imply
  principalDivisor (C := C) f⁻¹ = -principalDivisor f := by
-- proof
  apply CurveWithOrd.principalDivisor_inv f

/--
[CurveWithConstants.ord_constant](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Divisors.lean)
-/
@[path]
private lemma ord_constant_eq
  [Field k]
  [Field F]
  [Algebra k F]
  [inst : CurveWithConstants C k F]
  {P : C}
  {a : kˣ} :
-- imply
  CurveWithOrd.ord P (Units.map (algebraMap k F).toMonoidHom a) = 0 := by
-- proof
  apply CurveWithConstants.ord_constant P a


-- created on 2026-10-23
