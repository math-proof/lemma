module

public import Mathlib
public import Theorem.WeierstrassCurve.KatzLevelP
public import Instance.ModularCurve_KatzLevelPUniversal

public noncomputable section

set_option autoImplicit false

universe u

noncomputable section

open WeierstrassCurve Polynomial

namespace ModularCurve

namespace LevelP

public theorem preΨ_eval_map {S S' : Type*} [CommRing S] [CommRing S'] (f : S →+* S')
    (W : WeierstrassCurve S) (n : ℤ) (x : S) :
    ((W.map f).preΨ n).eval (f x) = f ((W.preΨ n).eval x) := by
  rw [WeierstrassCurve.map_preΨ, Polynomial.eval_map, Polynomial.eval₂_at_apply]


public theorem equation_map {S S' : Type*} [CommRing S] [CommRing S'] (f : S →+* S')
    {W : WeierstrassCurve S} {x y : S} (h : W.toAffine.Equation x y) :
    (W.map f).toAffine.Equation (f x) (f y) :=
  h.map f

section TorsionPoint

variable {B : Type u} [CommRing B] (W : WeierstrassCurve B) (p : ℕ)


public theorem PsiRoot.algebraMap_eq : algebraMap B (PsiRoot W p) = PsiRoot.ofBase W p :=
  AdjoinRoot.algebraMap_eq _


public theorem preΨ_eval₂_psiRootX : (W.preΨ p).eval₂ (PsiRoot.ofBase W p) (psiRootX W p) = 0 :=
  AdjoinRoot.eval₂_root (W.preΨ p)


public theorem TorsionPointRing.algebraMap_psiRoot_eq :
    algebraMap (PsiRoot W p) (TorsionPointRing W p) = TorsionPointRing.ofPsiRoot W p :=
  AdjoinRoot.algebraMap_eq _


public theorem TorsionPointRing.algebraMap_eq :
    algebraMap B (TorsionPointRing W p) = TorsionPointRing.ofBase W p := by
  rw [IsScalarTower.algebraMap_eq B (PsiRoot W p) (TorsionPointRing W p),
    TorsionPointRing.algebraMap_psiRoot_eq, PsiRoot.algebraMap_eq, TorsionPointRing.ofBase]


public theorem torsionQuadratic_eval₂_torsionPtY :
    (torsionQuadratic W p).eval₂ (TorsionPointRing.ofPsiRoot W p) (torsionPtY W p) = 0 :=
  AdjoinRoot.eval₂_root (torsionQuadratic W p)


public theorem equation_torsionPt :
    (torsionPtCurve W p).toAffine.Equation (torsionPtX W p) (torsionPtY W p) := by
  have h := torsionQuadratic_eval₂_torsionPtY W p
  rw [torsionQuadratic, eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C, eval₂_C,
    map_add, map_mul, map_add, map_add, map_add, map_mul, map_mul, map_pow, map_pow] at h
  rw [WeierstrassCurve.Affine.equation_iff, torsionPtCurve, WeierstrassCurve.map_a₁,
    WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄,
    WeierstrassCurve.map_a₆, TorsionPointRing.ofBase, RingHom.comp_apply, RingHom.comp_apply,
    RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, torsionPtX]
  linear_combination h


public theorem preΨ_torsionPt : ((torsionPtCurve W p).preΨ p).eval (torsionPtX W p) = 0 := by
  rw [torsionPtCurve, TorsionPointRing.ofBase, ← WeierstrassCurve.map_map, torsionPtX,
    preΨ_eval_map, WeierstrassCurve.map_preΨ, Polynomial.eval_map, preΨ_eval₂_psiRootX, map_zero]

end TorsionPoint

section TwoPoints

variable {B : Type u} [CommRing B] (W : WeierstrassCurve B) (p : ℕ)


public theorem TwoPointRing.algebraMap_eq : algebraMap B (TwoPointRing W p) = TwoPointRing.ofBase W p :=
  rfl


public theorem TwoPointRing.algebraMap_onePoint_eq :
    algebraMap (TorsionPointRing W p) (TwoPointRing W p) = TwoPointRing.ofOnePoint W p :=
  TorsionPointRing.algebraMap_eq _ _


public theorem equation_P_twoPointRing :
    (twoPointCurve W p).toAffine.Equation (TwoPointRing.xP W p) (TwoPointRing.yP W p) :=
  equation_map _ (equation_torsionPt W p)


public theorem equation_Q_twoPointRing :
    (twoPointCurve W p).toAffine.Equation (TwoPointRing.xQ W p) (TwoPointRing.yQ W p) :=
  equation_torsionPt (torsionPtCurve W p) p


public theorem preΨ_P_twoPointRing : ((twoPointCurve W p).preΨ p).eval (TwoPointRing.xP W p) = 0 := by
  have h := congrArg (TwoPointRing.ofOnePoint W p) (preΨ_torsionPt W p)
  rw [map_zero, ← preΨ_eval_map] at h
  exact h


public theorem preΨ_Q_twoPointRing : ((twoPointCurve W p).preΨ p).eval (TwoPointRing.xQ W p) = 0 :=
  preΨ_torsionPt (torsionPtCurve W p) p


public theorem BasisRing.algebraMap_eq : algebraMap B (BasisRing W p) = BasisRing.ofBase W p := rfl


public theorem BasisRing.algebraMap_twoPoint_eq :
    algebraMap (TwoPointRing W p) (BasisRing W p) = BasisRing.ofTwoPoint W p := rfl


public theorem isUnit_indepDenom : IsUnit (BasisRing.ofTwoPoint W p (indepDenom W p)) :=
  IsLocalization.Away.algebraMap_isUnit (S := BasisRing W p) (indepDenom W p)


public theorem basisCurve_eq_map_twoPointCurve :
    basisCurve W p = (twoPointCurve W p).map (BasisRing.ofTwoPoint W p) := by
  ext <;> rfl


public theorem isUnit_Δ_basisCurve (hW : IsUnit W.Δ) : IsUnit (basisCurve W p).Δ := by
  rw [basisCurve, WeierstrassCurve.map_Δ]
  exact hW.map _


public theorem isLevelPStructure_basisData : IsLevelPStructure (basisCurve W p) p (basisData W p) := by
  rw [basisCurve_eq_map_twoPointCurve]
  exact
  { equation_P := equation_map _ (equation_P_twoPointRing W p)
    equation_Q := equation_map _ (equation_Q_twoPointRing W p)
    preΨ_P := by
      show (((twoPointCurve W p).map (BasisRing.ofTwoPoint W p)).preΨ p).eval
        (BasisRing.ofTwoPoint W p (TwoPointRing.xP W p)) = 0
      rw [preΨ_eval_map, preΨ_P_twoPointRing, map_zero]
    preΨ_Q := by
      show (((twoPointCurve W p).map (BasisRing.ofTwoPoint W p)).preΨ p).eval
        (BasisRing.ofTwoPoint W p (TwoPointRing.xQ W p)) = 0
      rw [preΨ_eval_map, preΨ_Q_twoPointRing, map_zero]
    isUnit_indepElt_PQ := by
      show IsUnit (indepElt ((twoPointCurve W p).map (BasisRing.ofTwoPoint W p)) p
        (BasisRing.ofTwoPoint W p (TwoPointRing.xP W p))
        (BasisRing.ofTwoPoint W p (TwoPointRing.xQ W p)))
      rw [indepElt_map]
      have h := isUnit_indepDenom W p
      rw [indepDenom, map_mul] at h
      exact isUnit_of_mul_isUnit_left h
    isUnit_indepElt_QP := by
      show IsUnit (indepElt ((twoPointCurve W p).map (BasisRing.ofTwoPoint W p)) p
        (BasisRing.ofTwoPoint W p (TwoPointRing.xQ W p))
        (BasisRing.ofTwoPoint W p (TwoPointRing.xP W p)))
      rw [indepElt_map]
      have h := isUnit_indepDenom W p
      rw [indepDenom, map_mul] at h
      exact isUnit_of_mul_isUnit_right h }

end TwoPoints


public theorem isUnit_natCast_mul_Δ_univCurve : IsUnit ((p : UnivBase p) * (univCurve p).Δ) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := UnivBase p) (pDelta p)
  rwa [pDelta, map_mul, map_natCast, univCurve, WeierstrassCurve.map_Δ] at *


public theorem isUnit_Δ_univCurve : IsUnit (univCurve p).Δ :=
  isUnit_of_mul_isUnit_right (isUnit_natCast_mul_Δ_univCurve p)


public theorem isUnit_natCast_univBase : IsUnit (p : UnivBase p) :=
  isUnit_of_mul_isUnit_left (isUnit_natCast_mul_Δ_univCurve p)


public theorem isLevelPStructure_univData : IsLevelPStructure (univCurveT p) p (univData p) :=
  isLevelPStructure_basisData (univCurve p) p


public theorem isUnit_Δ_univCurveT : IsUnit (univCurveT p).Δ :=
  isUnit_Δ_basisCurve (univCurve p) p (isUnit_Δ_univCurve p)


public theorem isUnit_natCast_univBasisRing : IsUnit (p : UnivBasisRing p) := by
  have h := (isUnit_natCast_univBase p).map (UnivBasisRing.ofBase p)
  rwa [map_natCast] at h

end LevelP

namespace KatzLevelPForm

open scoped TensorProduct

variable {R : Type u} [CommRing R] {p : ℕ} {k : ℤ}


public theorem isUnit_Δ_univCurveOver (R : Type u) [CommRing R] (p : ℕ) :
    IsUnit (univCurveOver R p).Δ := by
  rw [univCurveOver, WeierstrassCurve.map_Δ]
  exact (LevelP.isUnit_Δ_univCurveT p).map _


public theorem isLevelPStructure_univDataOver (R : Type u) [CommRing R] (p : ℕ) :
    IsLevelPStructure (univCurveOver R p) p (univDataOver R p) :=
  (LevelP.isLevelPStructure_univData p).map _


@[simp] public theorem evalUniv_zero : (0 : KatzLevelPForm R p k).evalUniv = 0 := rfl


@[simp] public theorem evalUniv_add (F G : KatzLevelPForm R p k) :
    (F + G).evalUniv = F.evalUniv + G.evalUniv := rfl


@[simp] public theorem evalUniv_neg (F : KatzLevelPForm R p k) : (-F).evalUniv = -F.evalUniv := rfl


@[simp] public theorem evalUniv_sub (F G : KatzLevelPForm R p k) :
    (F - G).evalUniv = F.evalUniv - G.evalUniv := rfl


@[simp] public theorem evalUniv_mul {l : ℤ} (F : KatzLevelPForm R p k) (G : KatzLevelPForm R p l) :
    (F.mul G).evalUniv = F.evalUniv * G.evalUniv := rfl

end KatzLevelPForm

end ModularCurve

end
