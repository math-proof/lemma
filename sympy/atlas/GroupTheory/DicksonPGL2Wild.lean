/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/DicksonPGL2Wild.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import sympy.atlas.GroupTheory.DicksonPGL2Tame
import Lemma.Nat.Card_Stabilizer
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Algebra.Group.IsCommutative
import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Separable
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

/-!
# Dickson's classification in the wild case

This file classifies finite subgroups of `PGL₂` over an algebraic closure of an odd finite
field when the characteristic divides the group order. It also supplies the projective linear
group order formulas and characteristic-order element facts used by the classification.
-/

namespace MetaMathlibExt

namespace Dickson

open scoped BigOperators Pointwise Polynomial

private noncomputable def dicksonWild_projectiveSpecialLinearGroup_congr
    {n R S : Type*} [Fintype n] [DecidableEq n] [CommRing R] [CommRing S]
    (e : R ≃+* S) :
    Matrix.ProjectiveSpecialLinearGroup n R ≃*
      Matrix.ProjectiveSpecialLinearGroup n S := by
  let f := Matrix.SpecialLinearGroup.map (n := n) e.toRingHom
  let g := Matrix.SpecialLinearGroup.map (n := n) e.symm.toRingHom
  have hgf (x : Matrix.SpecialLinearGroup n R) : g (f x) = x := by
    ext i k
    exact e.symm_apply_apply (x i k)
  have hfg (x : Matrix.SpecialLinearGroup n S) : f (g x) = x := by
    ext i k
    exact e.apply_symm_apply (x i k)
  have hfSurj : Function.Surjective f := fun y ↦ ⟨g y, hfg y⟩
  have hgSurj : Function.Surjective g := fun x ↦ ⟨f x, hgf x⟩
  have hfCenter : Subgroup.center (Matrix.SpecialLinearGroup n R) ≤
      Subgroup.comap f (Subgroup.center (Matrix.SpecialLinearGroup n S)) := by
    intro x hx
    rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
    intro y
    obtain ⟨z, rfl⟩ := hfSurj y
    simpa only [map_mul] using congrArg f ((Subgroup.mem_center_iff.mp hx) z)
  have hgCenter : Subgroup.center (Matrix.SpecialLinearGroup n S) ≤
      Subgroup.comap g (Subgroup.center (Matrix.SpecialLinearGroup n R)) := by
    intro x hx
    rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
    intro y
    obtain ⟨z, rfl⟩ := hgSurj y
    simpa only [map_mul] using congrArg g ((Subgroup.mem_center_iff.mp hx) z)
  let qf := QuotientGroup.map (Subgroup.center (Matrix.SpecialLinearGroup n R))
    (Subgroup.center (Matrix.SpecialLinearGroup n S)) f hfCenter
  let qg := QuotientGroup.map (Subgroup.center (Matrix.SpecialLinearGroup n S))
    (Subgroup.center (Matrix.SpecialLinearGroup n R)) g hgCenter
  have hqgf (x : Matrix.ProjectiveSpecialLinearGroup n R) : qg (qf x) = x := by
    exact QuotientGroup.induction_on x fun z ↦ by
      rw [QuotientGroup.map_mk, QuotientGroup.map_mk, hgf]
  have hqfg (x : Matrix.ProjectiveSpecialLinearGroup n S) : qf (qg x) = x := by
    exact QuotientGroup.induction_on x fun z ↦ by
      rw [QuotientGroup.map_mk, QuotientGroup.map_mk, hfg]
  exact MulEquiv.ofBijective qf ⟨
    fun x y hxy ↦ by rw [← hqgf x, ← hqgf y, hxy],
    fun y ↦ ⟨qg y, hqfg y⟩⟩

private noncomputable def dicksonWild_projGenLinGroup_congr
    {n R S : Type*} [Fintype n] [DecidableEq n] [CommRing R] [CommRing S]
    (e : R ≃+* S) :
    Matrix.ProjGenLinGroup n R ≃* Matrix.ProjGenLinGroup n S := by
  let f := Matrix.ProjGenLinGroup.map (n := n) e.toRingHom
  let g := Matrix.ProjGenLinGroup.map (n := n) e.symm.toRingHom
  apply MonoidHom.toMulEquiv f g
  · apply MonoidHom.ext
    intro x
    obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective x
    rw [MonoidHom.comp_apply, Matrix.ProjGenLinGroup.map_mk,
      Matrix.ProjGenLinGroup.map_mk]
    have hA : Matrix.GeneralLinearGroup.map e.symm.toRingHom
        (Matrix.GeneralLinearGroup.map e.toRingHom A) = A := by
      apply Units.ext
      ext i k
      exact e.symm_apply_apply (A i k)
    rw [hA]
    rfl
  · apply MonoidHom.ext
    intro x
    obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective x
    rw [MonoidHom.comp_apply, Matrix.ProjGenLinGroup.map_mk,
      Matrix.ProjGenLinGroup.map_mk]
    have hA : Matrix.GeneralLinearGroup.map e.toRingHom
        (Matrix.GeneralLinearGroup.map e.symm.toRingHom A) = A := by
      apply Units.ext
      ext i k
      exact e.apply_symm_apply (A i k)
    rw [hA]
    rfl

private def dicksonWildExceptional (G X : Type*) [Group G] [MulAction G X] :=
  {x : X // ∃ g : G, g ≠ 1 ∧ g • x = x}

private instance dicksonWildExceptionalAction (G X : Type*) [Group G] [MulAction G X] :
    MulAction G (dicksonWildExceptional G X) where
  smul g x := ⟨g • x.1, by
    obtain ⟨h, hh, hx⟩ := x.2
    refine ⟨g * h * g⁻¹, ?_, ?_⟩
    · intro hgh
      apply hh
      calc
        h = g⁻¹ * (g * h * g⁻¹) * g := by group
        _ = 1 := by rw [hgh]; simp
    · simp only [mul_smul, inv_smul_smul, hx]⟩
  one_smul x := Subtype.ext (one_smul G x.1)
  mul_smul g h x := Subtype.ext (mul_smul g h x.1)

private def dicksonWild_fixedByExceptionalEquiv
    {G X : Type*} [Group G] [MulAction G X] (g : G) (hg : g ≠ 1) :
    MulAction.fixedBy (dicksonWildExceptional G X) g ≃ MulAction.fixedBy X g where
  toFun x := ⟨x.1.1, congrArg Subtype.val x.2⟩
  invFun x := ⟨⟨x.1, ⟨g, hg, x.2⟩⟩, Subtype.ext x.2⟩
  left_inv x := by ext; rfl
  right_inv x := by ext; rfl

namespace DicksonWildAffine
private def unitAction (F : Type*) [Field F] : Fˣ →* MulAut (Multiplicative F) where
  toFun u := (DistribMulAction.toAddEquiv F u).toMultiplicative
  map_one' := by
    ext x
    change (1 : F) * x.toAdd = x.toAdd
    simp
  map_mul' u v := by
    ext x
    change ((u * v : Fˣ) : F) * x.toAdd = (u : F) * ((v : F) * x.toAdd)
    simp [mul_assoc]

private abbrev Aff (F : Type*) [Field F] :=
  Multiplicative F ⋊[unitAction F] Fˣ

private noncomputable def infinity (F : Type*) [Field F] :
    Projectivization F (Fin 2 → F) := by
  classical
  exact OnePoint.equivProjectivization F OnePoint.infty

private noncomputable def borel (F : Type*) [Field F] :
    Subgroup (Matrix.ProjGenLinGroup (Fin 2) F) := by
  classical
  exact MulAction.stabilizer (Matrix.ProjGenLinGroup (Fin 2) F) (infinity F)

private noncomputable def lift {F : Type*} [Field F]
    (g : Matrix.ProjGenLinGroup (Fin 2) F) : GL (Fin 2) F :=
  Classical.choose (Matrix.ProjGenLinGroup.mk_surjective g)

private lemma mk_lift {F : Type*} [Field F]
    (g : Matrix.ProjGenLinGroup (Fin 2) F) :
    Matrix.ProjGenLinGroup.mk (lift g) = g :=
  Classical.choose_spec (Matrix.ProjGenLinGroup.mk_surjective g)

private lemma lift_lowerLeft_eq_zero {F : Type*} [Field F] (g : borel F) :
    (lift g.1 : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  classical
  have hg : g.1 • infinity F = infinity F :=
    MulAction.mem_stabilizer_iff.mp g.2
  have hA : lift g.1 • (OnePoint.infty : OnePoint F) = OnePoint.infty := by
    apply (OnePoint.equivProjectivization F).injective
    rw [OnePoint.equivProjectivization_smul]
    rw [← mk_lift g.1] at hg
    simpa [infinity] using hg
  exact OnePoint.smul_infty_eq_self_iff.mp hA

private lemma lift_lowerRight_ne_zero {F : Type*} [Field F] (g : borel F) :
    (lift g.1 : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := by
  intro h
  apply (lift g.1).det_ne_zero
  rw [Matrix.det_fin_two, lift_lowerLeft_eq_zero g, h]
  ring

private lemma lift_upperLeft_ne_zero {F : Type*} [Field F] (g : borel F) :
    (lift g.1 : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
  intro h
  apply (lift g.1).det_ne_zero
  rw [Matrix.det_fin_two, lift_lowerLeft_eq_zero g, h]
  ring

private noncomputable def lambda {F : Type*} [Field F] (g : borel F) : Fˣ :=
  Units.mk0 ((lift g.1 : Matrix (Fin 2) (Fin 2) F) 0 0 / lift g.1 1 1)
    (div_ne_zero (lift_upperLeft_ne_zero g) (lift_lowerRight_ne_zero g))

private noncomputable def gamma {F : Type*} [Field F] (g : borel F) : F :=
  (lift g.1 : Matrix (Fin 2) (Fin 2) F) 0 1 / lift g.1 1 1

private lemma ratios_eq_of_mk_eq {F : Type*} [Field F] (A B : GL (Fin 2) F)
    (h : Matrix.ProjGenLinGroup.mk A = Matrix.ProjGenLinGroup.mk B)
    (hA11 : (A : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0)
    (hB11 : (B : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0) :
    (A 0 0 / A 1 1 = B 0 0 / B 1 1) ∧
      (A 0 1 / A 1 1 = B 0 1 / B 1 1) := by
  obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp h
  have hentry (i j : Fin 2) : A i j * (u : F) = B i j := by
    have hij := congrArg (fun M : GL (Fin 2) F ↦
      (M : Matrix (Fin 2) (Fin 2) F) i j) hu
    fin_cases i <;> fin_cases j <;>
      simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply] using hij
  constructor
  · apply (div_eq_div_iff hA11 hB11).2
    rw [← hentry 1 1, ← hentry 0 0]
    ring
  · apply (div_eq_div_iff hA11 hB11).2
    rw [← hentry 1 1, ← hentry 0 1]
    ring

private lemma lambda_mul {F : Type*} [Field F] (g h : borel F) :
    lambda (g * h) = lambda g * lambda h := by
  classical
  let A := lift g.1
  let B := lift h.1
  let C := lift (g * h).1
  have hmk : Matrix.ProjGenLinGroup.mk C = Matrix.ProjGenLinGroup.mk (A * B) := by
    dsimp [A, B, C]
    rw [mk_lift, map_mul, mk_lift, mk_lift]
  have hAB11 : ((A * B : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := by
    have hvalue : ((A * B : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 1 =
        A 1 1 * B 1 1 := by
      simp [Matrix.mul_apply, Fin.sum_univ_two, A, B,
        lift_lowerLeft_eq_zero g]
    rw [hvalue]
    exact mul_ne_zero (lift_lowerRight_ne_zero g) (lift_lowerRight_ne_zero h)
  have hrat := ratios_eq_of_mk_eq C (A * B) hmk
    (lift_lowerRight_ne_zero (g * h)) hAB11
  apply Units.ext
  change C 0 0 / C 1 1 = (A 0 0 / A 1 1) * (B 0 0 / B 1 1)
  rw [hrat.1]
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  rw [show A 1 0 = 0 by exact lift_lowerLeft_eq_zero g,
    show B 1 0 = 0 by exact lift_lowerLeft_eq_zero h]
  simp only [zero_mul, zero_add]
  field_simp [lift_lowerRight_ne_zero g, lift_lowerRight_ne_zero h]
  ring

private lemma gamma_mul {F : Type*} [Field F] (g h : borel F) :
    gamma (g * h) = gamma g + (lambda g : F) * gamma h := by
  classical
  let A := lift g.1
  let B := lift h.1
  let C := lift (g * h).1
  have hmk : Matrix.ProjGenLinGroup.mk C = Matrix.ProjGenLinGroup.mk (A * B) := by
    dsimp [A, B, C]
    rw [mk_lift, map_mul, mk_lift, mk_lift]
  have hAB11 : ((A * B : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := by
    have hvalue : ((A * B : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 1 =
        A 1 1 * B 1 1 := by
      simp [Matrix.mul_apply, Fin.sum_univ_two, A, B,
        lift_lowerLeft_eq_zero g]
    rw [hvalue]
    exact mul_ne_zero (lift_lowerRight_ne_zero g) (lift_lowerRight_ne_zero h)
  have hrat := ratios_eq_of_mk_eq C (A * B) hmk
    (lift_lowerRight_ne_zero (g * h)) hAB11
  change C 0 1 / C 1 1 = A 0 1 / A 1 1 + (A 0 0 / A 1 1) * (B 0 1 / B 1 1)
  rw [hrat.2]
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  rw [show A 1 0 = 0 by exact lift_lowerLeft_eq_zero g]
  simp only [zero_mul, zero_add]
  have hA11 : A 1 1 ≠ 0 := lift_lowerRight_ne_zero g
  have hB11 : B 1 1 ≠ 0 := lift_lowerRight_ne_zero h
  field_simp [hA11, hB11]
  ring

private lemma lambda_one {F : Type*} [Field F] : lambda (1 : borel F) = 1 := by
  have h := lambda_mul (1 : borel F) 1
  rw [one_mul] at h
  calc
    lambda (1 : borel F) = (lambda (1 : borel F))⁻¹ *
        (lambda (1 : borel F) * lambda (1 : borel F)) := by group
    _ = (lambda (1 : borel F))⁻¹ * lambda (1 : borel F) := by rw [← h]
    _ = 1 := by simp

private lemma gamma_one {F : Type*} [Field F] : gamma (1 : borel F) = 0 := by
  have h := gamma_mul (1 : borel F) 1
  rw [one_mul, lambda_one] at h
  simp only [Units.val_one, one_mul] at h
  linear_combination -h

private noncomputable def toAff {F : Type*} [Field F] : borel F →* Aff F where
  toFun g := ⟨Multiplicative.ofAdd (gamma g), lambda g⟩
  map_one' := by
    ext
    · exact gamma_one (F := F)
    · exact congrArg Units.val (lambda_one (F := F))
  map_mul' g h := by
    ext
    · exact gamma_mul g h
    · exact congrArg Units.val (lambda_mul g h)

private noncomputable def affineGL {F : Type*} [Field F] (a : F) (u : Fˣ) : GL (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(u : F), a; 0, 1] (by
    simp [Matrix.det_fin_two, Units.ne_zero])

private lemma mk_affineGL_gamma_lambda {F : Type*} [Field F] (g : borel F) :
    Matrix.ProjGenLinGroup.mk (affineGL (gamma g) (lambda g)) = g.1 := by
  classical
  let A := lift g.1
  have hA11 : A 1 1 ≠ 0 := lift_lowerRight_ne_zero g
  let u : Fˣ := Units.mk0 (A 1 1)⁻¹ (inv_ne_zero hA11)
  rw [← mk_lift g.1]
  symm
  apply Matrix.ProjGenLinGroup.mk_eq_mk_iff.mpr
  refine ⟨u, ?_⟩
  have hu : A * Matrix.GeneralLinearGroup.scalar (Fin 2) u =
      affineGL (gamma g) (lambda g) := by
    apply Units.ext
    simp only [Units.val_mul]
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply, affineGL, u,
        gamma, lambda, A, lift_lowerLeft_eq_zero g, hA11, div_eq_mul_inv]
  exact hu

private lemma toAff_injective {F : Type*} [Field F] : Function.Injective (toAff (F := F)) := by
  intro g h heq
  apply Subtype.ext
  rw [← mk_affineGL_gamma_lambda g, ← mk_affineGL_gamma_lambda h]
  have hgamma := congrArg (fun z : Aff F ↦ z.left.toAdd) heq
  have hlambda := congrArg (fun z : Aff F ↦ z.right) heq
  change gamma g = gamma h at hgamma
  change lambda g = lambda h at hlambda
  rw [hgamma, hlambda]

private lemma toAff_surjective {F : Type*} [Field F] : Function.Surjective (toAff (F := F)) := by
  classical
  rintro ⟨a, u⟩
  let M := affineGL a.toAdd u
  have hMfix : M • (OnePoint.infty : OnePoint F) = OnePoint.infty := by
    apply OnePoint.smul_infty_eq_self_iff.mpr
    simp [M, affineGL]
  have hmem : Matrix.ProjGenLinGroup.mk M ∈ borel F := by
    apply MulAction.mem_stabilizer_iff.mpr
    have h := congrArg (OnePoint.equivProjectivization F) hMfix
    rw [OnePoint.equivProjectivization_smul] at h
    simpa [infinity] using h
  let g : borel F := ⟨Matrix.ProjGenLinGroup.mk M, hmem⟩
  refine ⟨g, ?_⟩
  have hmk : Matrix.ProjGenLinGroup.mk (lift g.1) = Matrix.ProjGenLinGroup.mk M := by
    exact mk_lift g.1
  have hM11 : (M : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := by
    simp [M, affineGL]
  have hrat := ratios_eq_of_mk_eq (lift g.1) M hmk
    (lift_lowerRight_ne_zero g) hM11
  apply SemidirectProduct.ext
  · change gamma g = a.toAdd
    rw [show gamma g = (lift g.1 : Matrix (Fin 2) (Fin 2) F) 0 1 /
      lift g.1 1 1 by rfl, hrat.2]
    simp [M, affineGL]
  · apply Units.ext
    change (lambda g : F) = (u : F)
    rw [show (lambda g : F) = (lift g.1 : Matrix (Fin 2) (Fin 2) F) 0 0 /
      lift g.1 1 1 by rfl, hrat.1]
    simp [M, affineGL]

private noncomputable def borelMulEquivAffine {F : Type*} [Field F] : borel F ≃* Aff F :=
  MulEquiv.ofBijective toAff ⟨toAff_injective, toAff_surjective⟩

private def rightRestrict {F : Type*} [Field F] (H : Subgroup (Aff F)) : H →* Fˣ :=
  SemidirectProduct.rightHom.comp H.subtype

private def kernelLeft {F : Type*} [Field F] (H : Subgroup (Aff F)) :
    (rightRestrict H).ker →* Multiplicative F where
  toFun z := (z.1.1 : Aff F).left
  map_one' := rfl
  map_mul' x y := by
    change (x.1.1 * y.1.1 : Aff F).left =
      (x.1.1 : Aff F).left * (y.1.1 : Aff F).left
    rw [SemidirectProduct.mul_left]
    have hx : (x.1.1 : Aff F).right = 1 := x.2
    simp [hx, unitAction]

private def kernelGamma {F : Type*} [Field F] (H : Subgroup (Aff F)) :
    Additive (rightRestrict H).ker →+ F :=
  (AddEquiv.additiveMultiplicative F).toAddMonoidHom.comp
    (kernelLeft H).toAdditive

private def translationAddSubgroup {F : Type*} [Field F]
    (H : Subgroup (Aff F)) : AddSubgroup F :=
  (kernelGamma H).range

private noncomputable def multiplierSubfield {F : Type*} [Field F]
    (Γ : AddSubgroup F) [Finite Γ] : Subfield F where
  carrier := {a | ∀ x ∈ Γ, a * x ∈ Γ}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb x hx
    rw [add_mul]
    exact Γ.add_mem (ha x hx) (hb x hx)
  mul_mem' := by
    intro a b ha hb x hx
    rw [mul_assoc]
    exact ha _ (hb x hx)
  neg_mem' := by
    intro a ha x hx
    rw [neg_mul]
    exact Γ.neg_mem (ha x hx)
  inv_mem' := by
    intro a ha
    by_cases ha0 : a = 0
    · subst a
      simp
    · intro x hx
      let f : Γ → Γ := fun y ↦ ⟨a * y.1, ha y.1 y.2⟩
      have hf : Function.Injective f := by
        intro y z hyz
        apply Subtype.ext
        apply mul_left_cancel₀ ha0
        exact congrArg Subtype.val hyz
      obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.mp hf) ⟨x, hx⟩
      have hyval : a * y.1 = x := congrArg Subtype.val hy
      rw [← hyval]
      simp [ha0, y.2]

private noncomputable instance translationAddSubgroup_finite
    {F : Type*} [Field F] (H : Subgroup (Aff F)) [Finite H] :
    Finite (translationAddSubgroup H) :=
  Finite.of_surjective (kernelGamma H).rangeRestrict
    (kernelGamma H).rangeRestrict_surjective

private lemma rightRestrict_range_mem_multiplierSubfield {F : Type*} [Field F]
    (H : Subgroup (Aff F)) [Finite H]
    (u : (rightRestrict H).range) :
    (u.1 : F) ∈ multiplierSubfield (translationAddSubgroup H) := by
  obtain ⟨h, hu⟩ := u.2
  rw [← hu]
  rintro x ⟨z, rfl⟩
  let w : (rightRestrict H).ker :=
    ⟨h * z.toMul.1 * h⁻¹, by
      change rightRestrict H (h * z.toMul.1 * h⁻¹) = 1
      rw [map_mul, map_mul, map_inv, z.toMul.2]
      simp⟩
  refine ⟨Additive.ofMul w, ?_⟩
  have hzright : (z.toMul.1.1 : Aff F).right = 1 := z.toMul.2
  change (((h.1 * z.toMul.1.1 * h.1⁻¹ : Aff F).left).toAdd) =
    (h.1 : Aff F).right * (z.toMul.1.1 : Aff F).left.toAdd
  simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, map_mul,
    SemidirectProduct.inv_left, map_inv, MulAut.inv_apply, MulAut.mul_apply,
    toAdd_mul, toAdd_inv]
  rw [hzright]
  dsimp [unitAction]
  simp only [AddEquiv.toMultiplicative_apply_apply,
    AddEquiv.toMultiplicative_apply_symm_apply,
    DistribMulAction.toAddEquiv_apply, DistribMulAction.toAddEquiv_symm_apply,
    toAdd_ofAdd, one_smul, Units.smul_def, smul_eq_mul,
    Units.val_inv_eq_inv_val]
  change (h.1 : Aff F).left.toAdd +
      ((h.1 : Aff F).right : F) * (z.toMul.1.1 : Aff F).left.toAdd +
        -(((h.1 : Aff F).right : F) *
          (((h.1 : Aff F).right : F)⁻¹ * (h.1 : Aff F).left.toAdd)) =
    ((h.1 : Aff F).right : F) * (z.toMul.1.1 : Aff F).left.toAdd
  field_simp
  abel

private noncomputable def multiplierRangeHom {F : Type*} [Field F]
    (H : Subgroup (Aff F)) [Finite H] :
    (rightRestrict H).range →* (multiplierSubfield (translationAddSubgroup H))ˣ where
  toFun u := Units.mk0
    (⟨(u.1 : F), rightRestrict_range_mem_multiplierSubfield H u⟩ :
      multiplierSubfield (translationAddSubgroup H)) (by
        intro h
        apply u.1.ne_zero
        exact congrArg Subtype.val h)
  map_one' := by
    apply Units.ext
    rfl
  map_mul' _ _ := by
    apply Units.ext
    rfl

private noncomputable def multiplierRange {F : Type*} [Field F]
    (H : Subgroup (Aff F)) [Finite H] :
    Subgroup (multiplierSubfield (translationAddSubgroup H))ˣ :=
  (multiplierRangeHom H).range

private lemma rightRestrict_range_card_add_one_le_multiplierSubfield
    {F : Type*} [Field F] (H : Subgroup (Aff F)) [Finite H]
    (hΓ : translationAddSubgroup H ≠ ⊥) :
    Nat.card (rightRestrict H).range + 1 ≤
      Nat.card (multiplierSubfield (translationAddSubgroup H)) := by
  let _ : Finite (rightRestrict H).range := Finite.of_surjective
    (rightRestrict H).rangeRestrict (rightRestrict H).rangeRestrict_surjective
  let _ : Finite (multiplierSubfield (translationAddSubgroup H)) :=
    multiplierSubfield_finite (translationAddSubgroup H) hΓ
  let toM : Option (rightRestrict H).range →
      multiplierSubfield (translationAddSubgroup H)
    | none => 0
    | some u => ⟨u.1, rightRestrict_range_mem_multiplierSubfield H u⟩
  have htoM : Function.Injective toM := by
    intro a b hab
    cases a with
    | none =>
        cases b with
        | none => rfl
        | some b =>
            exfalso
            have h := congrArg Subtype.val hab
            exact b.1.ne_zero (by simpa [toM] using h.symm)
    | some a =>
        cases b with
        | none =>
            exfalso
            have h := congrArg Subtype.val hab
            simp [toM] at h
        | some b =>
            congr 1
            apply Subtype.ext
            apply Units.ext
            exact congrArg Subtype.val hab
  let _ : Fintype (rightRestrict H).range := Fintype.ofFinite _
  let _ : Fintype (multiplierSubfield (translationAddSubgroup H)) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    ← Fintype.card_option]
  exact Fintype.card_le_of_injective toM htoM

private lemma multiplierSubfield_card_eq_pow
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    {F : Type*} [Field F] [CharP F p]
    (H : Subgroup (Aff F)) [Finite H] (m t : ℕ) (hm : 1 ≤ m)
    (hHcard : Nat.card H = p ^ m * t)
    (hrange : Nat.card (rightRestrict H).range = t)
    (hsandwich : p ^ m - 1 ≤ 2 * t) :
    Nat.card (multiplierSubfield (translationAddSubgroup H)) = p ^ m := by
  let Γ := translationAddSubgroup H
  have hΓcard : Nat.card Γ = p ^ m :=
    translationAddSubgroup_card_eq H (p ^ m) t hHcard hrange
  have hqone : 1 < p ^ m :=
    one_lt_pow₀ (Fact.out : p.Prime).one_lt (by omega)
  have hΓ : Γ ≠ ⊥ := by
    intro h
    rw [h] at hΓcard
    simp at hΓcard
    omega
  let M := multiplierSubfield Γ
  let _ : Finite M := multiplierSubfield_finite Γ hΓ
  let _ : Fintype M := Fintype.ofFinite M
  obtain ⟨ell, -, hMpow⟩ := FiniteField.card M p
  have hMpow' : Nat.card M = p ^ (ell : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hMpow
  have hMle : Nat.card M ≤ p ^ m := by
    rw [← hΓcard]
    exact multiplierSubfield_card_le Γ hΓ
  have hellm : (ell : ℕ) ≤ m := by
    apply (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp
    rwa [← hMpow']
  have htM : t + 1 ≤ Nat.card M := by
    have := rightRestrict_range_card_add_one_le_multiplierSubfield H hΓ
    rwa [hrange] at this
  have hell : (ell : ℕ) = m := by
    by_contra hne
    have hellsucc : (ell : ℕ) + 1 ≤ m := by omega
    have hpstep : p ^ ((ell : ℕ) + 1) ≤ p ^ m :=
      Nat.pow_le_pow_right (Fact.out : p.Prime).pos hellsucc
    have hp3 : 3 ≤ p := by
      have hpgt : 2 < p := Fact.out
      exact hpgt
    have hthree : 3 * Nat.card M ≤ p ^ m := by
      calc
        3 * Nat.card M = p ^ (ell : ℕ) * 3 := by rw [hMpow']; omega
        _ ≤ p ^ (ell : ℕ) * p := Nat.mul_le_mul_left _ hp3
        _ = p ^ ((ell : ℕ) + 1) := (pow_succ _ _).symm
        _ ≤ p ^ m := hpstep
    have hMpos : 0 < Nat.card M := Nat.card_pos
    omega
  rw [hMpow', hell]

private lemma exists_affine_normal_form
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    {F : Type*} [Field F] [CharP F p]
    (H : Subgroup (Aff F)) [Finite H] (m t : ℕ) (hm : 1 ≤ m)
    (hHcard : Nat.card H = p ^ m * t)
    (hrange : Nat.card (rightRestrict H).range = t)
    (hsandwich : p ^ m - 1 ≤ 2 * t) :
    ∃ (s : F) (γ : translationAddSubgroup H)
      (coord : H → multiplierSubfield (translationAddSubgroup H) × multiplierRange H),
      (γ : F) ≠ 0 ∧ Function.Bijective coord ∧
      ∀ h : H,
        (((coord h).1 : multiplierSubfield (translationAddSubgroup H)) : F) * γ.1 =
          ((SemidirectProduct.inl (Multiplicative.ofAdd s) * h.1 *
            (SemidirectProduct.inl (Multiplicative.ofAdd s) : Aff F)⁻¹).left).toAdd ∧
        (((((coord h).2.1 :
          (multiplierSubfield (translationAddSubgroup H))ˣ) :
            multiplierSubfield (translationAddSubgroup H)) : F)) =
          ((h.1 : Aff F).right : F) := by
  classical
  let Γ := translationAddSubgroup H
  let M := multiplierSubfield Γ
  let L := multiplierRange H
  have hΓcard : Nat.card Γ = p ^ m :=
    translationAddSubgroup_card_eq H (p ^ m) t hHcard hrange
  have hΓ : Γ ≠ ⊥ := by
    intro h
    rw [h] at hΓcard
    simp at hΓcard
    have hqone : 1 < p ^ m :=
      one_lt_pow₀ (Fact.out : p.Prime).one_lt (by omega)
    omega
  let _ : Finite M := multiplierSubfield_finite Γ hΓ
  let _ : Finite (rightRestrict H).range := Finite.of_surjective
    (rightRestrict H).rangeRestrict (rightRestrict H).rangeRestrict_surjective
  let _ : Finite L := Finite.of_surjective (multiplierRangeHom H).rangeRestrict
    (multiplierRangeHom H).rangeRestrict_surjective
  have hMcard : Nat.card M = p ^ m :=
    multiplierSubfield_card_eq_pow H m t hm hHcard hrange hsandwich
  have hLcard : Nat.card L = t := (multiplierRange_card H).trans hrange
  obtain ⟨γ, hγ⟩ := AddSubgroup.ne_bot_iff_exists_ne_zero.mp hΓ
  have hγval : (γ : F) ≠ 0 := by
    intro h
    exact hγ (Subtype.ext h)
  let toΓ : M → Γ := fun a ↦ ⟨a.1 * γ.1, a.2 γ.1 γ.2⟩
  have htoΓ : Function.Bijective toΓ :=
    multiplier_mul_bijective Γ hΓ γ hγval (hMcard.trans hΓcard.symm)
  let eΓ : M ≃ Γ := Equiv.ofBijective toΓ htoΓ
  obtain ⟨s, hs⟩ := exists_translation_conj_left_mem H
  let normLeft (h : H) : Γ := ⟨
    ((SemidirectProduct.inl (Multiplicative.ofAdd s) * h.1 *
      (SemidirectProduct.inl (Multiplicative.ofAdd s) : Aff F)⁻¹).left).toAdd,
    hs h⟩
  let rangeCoord (h : H) : (rightRestrict H).range :=
    ⟨rightRestrict H h, ⟨h, rfl⟩⟩
  let coord : H → M × L := fun h ↦
    (eΓ.symm (normLeft h),
      ⟨multiplierRangeHom H (rangeCoord h), ⟨rangeCoord h, rfl⟩⟩)
  have hcoordInj : Function.Injective coord := by
    intro h k hhk
    have hleftCoord := congrArg Prod.fst hhk
    have hrightCoord := congrArg Prod.snd hhk
    have hnorm : normLeft h = normLeft k := eΓ.symm.injective hleftCoord
    have hrangeCoord : rangeCoord h = rangeCoord k := by
      apply multiplierRangeHom_injective H
      exact congrArg Subtype.val hrightCoord
    have hright : (h.1 : Aff F).right = (k.1 : Aff F).right :=
      congrArg (fun u : (rightRestrict H).range ↦ u.1) hrangeCoord
    let T : Aff F := SemidirectProduct.inl (Multiplicative.ofAdd s)
    have hconj : T * h.1 * T⁻¹ = T * k.1 * T⁻¹ := by
      apply SemidirectProduct.ext
      · exact Multiplicative.ext (congrArg Subtype.val hnorm)
      · simp [T, SemidirectProduct.mul_right, SemidirectProduct.inv_right, hright]
    apply Subtype.ext
    exact (MulAut.conj T).injective hconj
  have hcoord : Function.Bijective coord := by
    let _ : Fintype H := Fintype.ofFinite H
    let _ : Fintype M := Fintype.ofFinite M
    let _ : Fintype L := Fintype.ofFinite L
    apply (Fintype.bijective_iff_injective_and_card coord).2
    refine ⟨hcoordInj, ?_⟩
    simp only [← Nat.card_eq_fintype_card, Nat.card_prod, hHcard, hMcard,
      hLcard]
  refine ⟨s, γ, coord, hγval, hcoord, ?_⟩
  intro h
  constructor
  · have he := eΓ.apply_symm_apply (normLeft h)
    exact congrArg Subtype.val he
  · rfl

private lemma exists_affine_matrix_normal_form
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    {F : Type*} [Field F] [CharP F p]
    (H : Subgroup (Aff F)) [Finite H] (m t : ℕ) (hm : 1 ≤ m)
    (hHcard : Nat.card H = p ^ m * t)
    (hrange : Nat.card (rightRestrict H).range = t)
    (hsandwich : p ^ m - 1 ≤ 2 * t) :
    ∃ (M : Subfield F) (c : GL (Fin 2) F) (L : Subgroup Mˣ)
      (coord : H → M × L),
      Finite M ∧ Nat.card M = p ^ m ∧ Nat.card L = t ∧
      Function.Bijective coord ∧
      (∀ A : GL (Fin 2) F, A 1 0 ≠ 0 →
        ((c * A * c⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0) ∧
      ∀ h : H,
        c * affineGL h.1.left.toAdd h.1.right * c⁻¹ =
          Matrix.GeneralLinearGroup.map M.subtype
            (affineGL (coord h).1 (coord h).2.1) := by
  classical
  let Γ := translationAddSubgroup H
  let M := multiplierSubfield Γ
  let L := multiplierRange H
  obtain ⟨s, γ, coord, hγ, hcoord, hform⟩ :=
    exists_affine_normal_form H m t hm hHcard hrange hsandwich
  let r : Fˣ := Units.mk0 (γ.1)⁻¹ (inv_ne_zero hγ)
  let T : GL (Fin 2) F := affineGL s 1
  let D : GL (Fin 2) F := affineGL 0 r
  let c : GL (Fin 2) F := D * T
  have hMfinite : Finite M := by
    apply multiplierSubfield_finite Γ
    intro hbot
    apply hγ
    have hmem : (γ : F) ∈ Γ := γ.2
    rw [hbot] at hmem
    exact hmem
  let _ : Finite M := hMfinite
  have hMcard : Nat.card M = p ^ m :=
    multiplierSubfield_card_eq_pow H m t hm hHcard hrange hsandwich
  have hLcard : Nat.card L = t := (multiplierRange_card H).trans hrange
  refine ⟨M, c, L, coord, hMfinite, hMcard, hLcard, hcoord, ?_, ?_⟩
  · intro A hA
    have hcshape : c = affineGL ((r : F) * s) r := by
      dsimp [c, D, T]
      rw [affineGL_mul]
      simp
    rw [hcshape, affineGL_conj_lowerLeft]
    exact mul_ne_zero hA (inv_ne_zero r.ne_zero)
  intro h
  have hformh := hform h
  rw [translation_conj_left] at hformh
  have hconj : c * affineGL h.1.left.toAdd h.1.right * c⁻¹ =
      D * (T * affineGL h.1.left.toAdd h.1.right * T⁻¹) * D⁻¹ := by
    dsimp [c]
    group
  rw [hconj]
  change D * (affineGL s 1 * affineGL h.1.left.toAdd h.1.right *
    (affineGL s 1)⁻¹) * D⁻¹ = _
  rw [affineGL_translation_conj]
  change affineGL 0 r *
      affineGL (h.1.left.toAdd + (1 - (h.1.right : F)) * s) h.1.right *
      (affineGL 0 r)⁻¹ = _
  rw [affineGL_conj, affineGL_map_subfield]
  congr 2
  · change (γ.1)⁻¹ *
        (h.1.left.toAdd + (1 - (h.1.right : F)) * s) = ((coord h).1 : F)
    rw [← hformh.1]
    field_simp
  · apply Units.ext
    exact hformh.2.symm

private lemma card_parabolic_borel_fiber_le_two {F : Type*} [Field F]
    (S : GL (Fin 2) F)
    (hS10 : (S : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0)
    (H : Subgroup (borel F)) [Finite H] (u : Fˣ) :
    Nat.card {h : H // lambda h.1 = u ∧
      (((S * affineGL (gamma h.1) (lambda h.1) : GL (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F)).IsParabolic} ≤ 2 := by
  classical
  let c : F := 4 * Matrix.det (S : Matrix (Fin 2) (Fin 2) F) * (u : F)
  let toRoot : {h : H // lambda h.1 = u ∧
      (((S * affineGL (gamma h.1) (lambda h.1) : GL (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F)).IsParabolic} →
      {x : F // x ^ 2 = c} := fun h ↦ ⟨
    Matrix.trace (((S * affineGL (gamma h.1.1) (lambda h.1.1) : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F)), by
      rw [h.2.1]
      have hdisc := h.2.2.2
      rw [Matrix.discr_fin_two, h.2.1] at hdisc
      have heq := sub_eq_zero.mp hdisc
      rw [det_mul_affineGL] at heq
      simpa [c, mul_assoc] using heq⟩
  have hinj : Function.Injective toRoot := by
    intro x y hxy
    have htrace := congrArg (fun z : {w : F // w ^ 2 = c} ↦ z.1) hxy
    change Matrix.trace (((S * affineGL (gamma x.1.1) (lambda x.1.1) :
        GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) =
      Matrix.trace (((S * affineGL (gamma y.1.1) (lambda y.1.1) :
        GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) at htrace
    rw [trace_mul_affineGL, trace_mul_affineGL, x.2.1, y.2.1] at htrace
    have hgamma : gamma x.1.1 = gamma y.1.1 := by
      apply mul_left_cancel₀ hS10
      linear_combination htrace
    apply Subtype.ext
    apply Subtype.ext
    apply toAff_injective
    apply SemidirectProduct.ext
    · exact hgamma
    · exact x.2.1.trans y.2.1.symm
  let q : F[X] := Polynomial.X ^ 2 - Polynomial.C c
  have hq0 : q ≠ 0 := Polynomial.X_pow_sub_C_ne_zero (by decide) c
  have hfinite : Set.Finite {x : F | x ^ 2 = c} := by
    apply (Finset.finite_toSet (q.map (algebraMap F F)).roots.toFinset).subset
    intro x hx
    rw [show (q.map (algebraMap F F)).roots.toFinset = q.rootSet F by rfl,
      Polynomial.mem_rootSet_of_ne hq0]
    change x ^ 2 = c at hx
    simpa [q] using sub_eq_zero.mpr hx
  let _ : Fintype {x : F // x ^ 2 = c} := hfinite.fintype
  exact (Nat.card_le_card_of_injective toRoot hinj).trans
    (card_quadraticFiber_le_two c)

private lemma card_parabolic_borel_le_twice_range {F : Type*} [Field F]
    (S : GL (Fin 2) F)
    (hS10 : (S : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0)
    (H : Subgroup (borel F)) [Finite H] :
    Nat.card {h : H //
      (((S * affineGL (gamma h.1) (lambda h.1) : GL (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F)).IsParabolic} ≤
      2 * Nat.card (SemidirectProduct.rightHom.comp
        (toAff.comp H.subtype)).range := by
  classical
  let rhoH : H →* Fˣ := SemidirectProduct.rightHom.comp (toAff.comp H.subtype)
  let E := {h : H //
    (((S * affineGL (gamma h.1) (lambda h.1) : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F)).IsParabolic}
  let toRange : E → rhoH.range := fun h ↦ ⟨rhoH h.1, ⟨h.1, rfl⟩⟩
  let _ : Finite rhoH.range := Finite.of_surjective rhoH.rangeRestrict
    rhoH.rangeRestrict_surjective
  have hfiber (u : rhoH.range) : Nat.card {h : E // toRange h = u} ≤ 2 := by
    let toFixed : {h : E // toRange h = u} →
        {h : H // lambda h.1 = u.1 ∧
          (((S * affineGL (gamma h.1) (lambda h.1) : GL (Fin 2) F) :
            Matrix (Fin 2) (Fin 2) F)).IsParabolic} := fun h ↦
      ⟨h.1.1, congrArg (fun z : rhoH.range ↦ z.1) h.2, h.1.2⟩
    have hinj : Function.Injective toFixed := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z ↦ z.1) hxy
    exact (Nat.card_le_card_of_injective toFixed hinj).trans
      (card_parabolic_borel_fiber_le_two S hS10 H u.1)
  simpa [E, rhoH] using card_le_mul_card_of_fiber_le toRange 2 hfiber

end DicksonWildAffine

private lemma dicksonWild_normalizer_borel_coordinates
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (hpG : p ∣ Nat.card G) (P : Sylow p G) :
    ∃ (a : MulAut (PGL p))
      (B : Subgroup (DicksonWildAffine.borel (K p)))
      (e : Subgroup.normalizer (P : Set G) ≃* B),
      (∀ n, ((e n).1 : PGL p) = a (n.1 : PGL p)) ∧
      ∀ g : G, g ∉ Subgroup.normalizer (P : Set G) →
        (DicksonWildAffine.lift (a (g : PGL p)) :
          Matrix (Fin 2) (Fin 2) (K p)) 1 0 ≠ 0 := by
  classical
  let N := Subgroup.normalizer (P : Set G)
  let Pbar : Subgroup (PGL p) := Subgroup.map G.subtype (P : Subgroup G)
  let eP : (P : Subgroup G) ≃* Pbar :=
    Subgroup.equivMapOfInjective (P : Subgroup G) G.subtype G.subtype_injective
  let _ : Finite Pbar := Finite.of_surjective eP eP.surjective
  have hPbar : IsPGroup p Pbar := P.isPGroup'.map G.subtype
  have hPbarNe : Pbar ≠ ⊥ := by
    change Subgroup.map G.subtype (P : Subgroup G) ≠ ⊥
    intro h
    apply dicksonWild_sylow_ne_bot_of_dvd_card P hpG
    exact (Subgroup.map_eq_bot_iff_of_injective (P : Subgroup G)
      G.subtype_injective).mp h
  obtain ⟨x, hx, hunique⟩ :=
    dicksonWild_existsUnique_fixedPoint_of_isPGroup Pbar hPbar hPbarNe
  have hPfix (z : P) : (z.1 : PGL p) • x = x := by
    change (eP z : PGL p) • x = x
    exact hx (eP z)
  have hPunique (y : Projectivization (K p) (Fin 2 → K p))
      (hy : ∀ z : P, (z.1 : PGL p) • y = y) : y = x := by
    apply hunique
    intro z
    obtain ⟨w, rfl⟩ := eP.surjective z
    exact hy w
  let c : OnePoint (K p) := (OnePoint.equivProjectivization (K p)).symm x
  obtain ⟨T, hT⟩ := dicksonWild_exists_smul_eq_infty c
  let τ : PGL p := Matrix.ProjGenLinGroup.mk T
  have hτx : τ • x = DicksonWildAffine.infinity (K p) := by
    have hc : OnePoint.equivProjectivization (K p) c = x := Equiv.apply_symm_apply _ _
    rw [← hc]
    change Matrix.ProjGenLinGroup.mk T • OnePoint.equivProjectivization (K p) c =
      OnePoint.equivProjectivization (K p) OnePoint.infty
    calc
      Matrix.ProjGenLinGroup.mk T • OnePoint.equivProjectivization (K p) c =
          OnePoint.equivProjectivization (K p) (T • c) :=
        (OnePoint.equivProjectivization_smul (g := T) c).symm
      _ = OnePoint.equivProjectivization (K p) OnePoint.infty :=
        congrArg (OnePoint.equivProjectivization (K p)) hT
  let a : MulAut (PGL p) := MulAut.conj τ
  let nToB : N →* DicksonWildAffine.borel (K p) :=
    { toFun := fun n ↦ ⟨a (n.1 : PGL p), by
        apply MulAction.mem_stabilizer_iff.mpr
        rw [← hτx]
        have hnfix : (n.1 : PGL p) • x = x :=
          (dicksonWild_mem_normalizer_iff_fixedPoint G P x hPfix hPunique n.1).mp n.2
        change (τ * (n.1 : PGL p) * τ⁻¹) • (τ • x) = τ • x
        simp only [mul_smul]
        rw [inv_smul_smul, hnfix]⟩
      map_one' := Subtype.ext (map_one a)
      map_mul' := fun n m ↦ Subtype.ext (map_mul a (n.1 : PGL p) (m.1 : PGL p)) }
  have hnToBInj : Function.Injective nToB := by
    intro n m hnm
    apply Subtype.ext
    apply G.subtype_injective
    apply a.injective
    exact congrArg (fun z : DicksonWildAffine.borel (K p) ↦ (z.1 : PGL p)) hnm
  let B : Subgroup (DicksonWildAffine.borel (K p)) := nToB.range
  let e : N ≃* B := MonoidHom.ofInjective hnToBInj
  refine ⟨a, B, e, fun n ↦ rfl, ?_⟩
  intro g hg hzero
  let A : GL (Fin 2) (K p) := DicksonWildAffine.lift (a (g : PGL p))
  have hAfix : A • (OnePoint.infty : OnePoint (K p)) = OnePoint.infty :=
    OnePoint.smul_infty_eq_self_iff.mpr hzero
  have hagfix : a (g : PGL p) • DicksonWildAffine.infinity (K p) =
      DicksonWildAffine.infinity (K p) := by
    have h := congrArg (OnePoint.equivProjectivization (K p)) hAfix
    rw [OnePoint.equivProjectivization_smul] at h
    rw [← DicksonWildAffine.mk_lift (a (g : PGL p))]
    simpa [A, DicksonWildAffine.infinity] using h
  have hconjfix : a (g : PGL p) • (τ • x) = τ • x := by
    rw [hτx]
    exact hagfix
  have hleft : τ • ((g : PGL p) • x) = τ • x := by
    calc
      τ • ((g : PGL p) • x) = a (g : PGL p) • (τ • x) := by
        change τ • ((g : PGL p) • x) =
          (τ * (g : PGL p) * τ⁻¹) • (τ • x)
        simp [mul_smul]
      _ = τ • x := hconjfix
  have hgfix : (g : PGL p) • x = x := smul_left_cancel τ hleft
  exact hg ((dicksonWild_mem_normalizer_iff_fixedPoint G P x hPfix hPunique g).mpr hgfix)

private lemma dicksonWild_card_order_char_in_normalizer_coset_le
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (hpG : p ∣ Nat.card G) (P : Sylow p G)
    (m t : ℕ) (htp : Nat.Coprime t p)
    (hNcard : Nat.card (Subgroup.normalizer (P : Set G)) = p ^ m * t)
    (g : G) (hg : g ∉ Subgroup.normalizer (P : Set G)) :
    Nat.card {n : Subgroup.normalizer (P : Set G) //
      (g * (n.1 : G)) ^ p = 1} ≤ 2 * t := by
  classical
  let N := Subgroup.normalizer (P : Set G)
  obtain ⟨a, B, e, he, hout⟩ := dicksonWild_normalizer_borel_coordinates G hpG P
  let _ : Finite B := Finite.of_surjective e e.surjective
  have hBcard : Nat.card B = p ^ m * t := by
    rw [← Nat.card_congr e.toEquiv]
    exact hNcard
  let S : GL (Fin 2) (K p) := DicksonWildAffine.lift (a (g : PGL p))
  have hS10 : (S : Matrix (Fin 2) (Fin 2) (K p)) 1 0 ≠ 0 := hout g hg
  let toParabolic : {n : N // (g * (n.1 : G)) ^ p = 1} →
      {b : B // (S * DicksonWildAffine.affineGL
        (DicksonWildAffine.gamma b.1) (DicksonWildAffine.lambda b.1)).IsParabolic} := fun n ↦
    ⟨e n.1, by
      let z : G := g * (n.1.1 : G)
      have hzNe : z ≠ 1 := by
        intro hz
        apply hg
        have hgn : g = (n.1.1 : G)⁻¹ := by
          change g * (n.1.1 : G) = 1 at hz
          exact eq_inv_of_mul_eq_one_left hz
        rw [hgn]
        exact N.inv_mem n.1.2
      have hzOrderG : orderOf z = p := orderOf_eq_prime n.2 hzNe
      have hzOrder : orderOf (z : PGL p) = p := by
        exact (orderOf_injective G.subtype G.subtype_injective z).trans hzOrderG
      have haOrder : orderOf (a (z : PGL p)) = p := by
        rw [MulEquiv.orderOf_eq]
        exact hzOrder
      have hmk : Matrix.ProjGenLinGroup.mk
          (S * DicksonWildAffine.affineGL
            (DicksonWildAffine.gamma (e n.1).1)
            (DicksonWildAffine.lambda (e n.1).1)) = a (z : PGL p) := by
        calc
          Matrix.ProjGenLinGroup.mk
              (S * DicksonWildAffine.affineGL
                (DicksonWildAffine.gamma (e n.1).1)
                (DicksonWildAffine.lambda (e n.1).1)) =
              Matrix.ProjGenLinGroup.mk S * (e n.1).1 := by
            rw [map_mul, DicksonWildAffine.mk_affineGL_gamma_lambda]
          _ = a (g : PGL p) * a (n.1.1 : PGL p) := by
            rw [DicksonWildAffine.mk_lift]
            congr 1
            exact he n.1
          _ = a (z : PGL p) := by
            exact (map_mul a (g : PGL p) (n.1.1 : PGL p)).symm
      apply dicksonWild_lift_isParabolic_of_order_eq_char
      rw [hmk]
      exact haOrder⟩
  have htoInj : Function.Injective toParabolic := by
    intro n r hnr
    apply Subtype.ext
    apply e.injective
    exact congrArg (fun z ↦ z.1) hnr
  calc
    Nat.card {n : N // (g * (n.1 : G)) ^ p = 1} ≤
        Nat.card {b : B // (S * DicksonWildAffine.affineGL
          (DicksonWildAffine.gamma b.1) (DicksonWildAffine.lambda b.1)).IsParabolic} :=
      Nat.card_le_card_of_injective toParabolic htoInj
    _ ≤ 2 * Nat.card (SemidirectProduct.rightHom.comp
        (DicksonWildAffine.toAff.comp B.subtype)).range :=
      DicksonWildAffine.card_parabolic_borel_le_twice_range S hS10 B
    _ = 2 * t := by
      rw [dicksonWild_borel_multiplier_range_card B m t htp hBcard]

private lemma dicksonWild_sandwich_bound
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (hpG : p ∣ Nat.card G) (P : Sylow p G)
    (m f t : ℕ) (hf : 0 < f) (htp : Nat.Coprime t p)
    (hPcard : Nat.card (P : Subgroup G) = p ^ m)
    (hNcard : Nat.card (Subgroup.normalizer (P : Set G)) = p ^ m * t)
    (hindex : (Subgroup.normalizer (P : Set G)).index = 1 + f * p ^ m)
    (hcount : Nat.card {g : G // g ≠ 1 ∧ g ^ p = 1} =
      (1 + f * p ^ m) * (p ^ m - 1)) :
    p ^ m - 1 ≤ 2 * t := by
  classical
  let N := Subgroup.normalizer (P : Set G)
  let O := {g : G // g ∉ N ∧ g ^ p = 1}
  let Q := G ⧸ N
  let q1 : Q := Quotient.mk'' (1 : G)
  let C := {q : Q // q ≠ q1}
  let coset : O → C := fun g ↦ ⟨Quotient.mk'' g.1, by
    intro hq
    have hrel : QuotientGroup.leftRel N g.1 1 := Quotient.exact hq
    have hginv : g.1⁻¹ ∈ N := by
      simpa using QuotientGroup.leftRel_apply.mp hrel
    exact g.2.1 (by simpa using N.inv_mem hginv)⟩
  have hfiber (c : C) : Nat.card {g : O // coset g = c} ≤ 2 * t := by
    let s : G := c.1.out
    have hsClass : Quotient.mk'' s = c.1 := Quotient.out_eq c.1
    have hs : s ∉ N := by
      intro hsN
      apply c.2
      rw [← hsClass]
      apply Quotient.sound
      apply QuotientGroup.leftRel_apply.mpr
      simpa using N.inv_mem hsN
    let toN : {g : O // coset g = c} →
        {n : N // (s * (n.1 : G)) ^ p = 1} := fun g ↦
      ⟨⟨s⁻¹ * g.1.1, by
        apply QuotientGroup.leftRel_apply.mp
        apply Quotient.exact
        exact hsClass.trans (congrArg (fun z : C ↦ z.1) g.2).symm⟩, by
        simpa [mul_assoc] using g.1.2.2⟩
    have htoN : Function.Injective toN := by
      intro g h hgh
      apply Subtype.ext
      apply Subtype.ext
      have hv := congrArg (fun z : {n : N // (s * (n.1 : G)) ^ p = 1} ↦
        (z.1 : G)) hgh
      change s⁻¹ * g.1.1 = s⁻¹ * h.1.1 at hv
      exact mul_left_cancel hv
    exact (Nat.card_le_card_of_injective toN htoN).trans
      (dicksonWild_card_order_char_in_normalizer_coset_le
        G hpG P m t htp hNcard s hs)
  have hupper : Nat.card O ≤ 2 * t * Nat.card C :=
    DicksonWildAffine.card_le_mul_card_of_fiber_le coset (2 * t) hfiber
  have hOcard : Nat.card O = f * p ^ m * (p ^ m - 1) :=
    dicksonWild_card_order_char_outside_normalizer G P m f hPcard hcount
  have hCcard : Nat.card C = f * p ^ m := by
    let _ : Fintype Q := Fintype.ofFinite Q
    let _ : Fintype C := Fintype.ofFinite C
    rw [Nat.card_eq_fintype_card]
    calc
      Fintype.card C = Fintype.card Q - 1 :=
        Fintype.card_subtype_compl (fun q : Q ↦ q = q1) |>.trans (by simp)
      _ = N.index - 1 := by
        rw [Subgroup.index_eq_card]
        exact congrArg (fun n ↦ n - 1) Nat.card_eq_fintype_card.symm
      _ = f * p ^ m := by rw [hindex]; omega
  rw [hOcard, hCcard] at hupper
  apply Nat.le_of_mul_le_mul_left (c := f * p ^ m)
  · simpa [mul_assoc, mul_left_comm, mul_comm] using hupper
  · exact mul_pos hf (pow_pos (Fact.out : p.Prime).pos m)

private lemma dicksonWild_card_order_char_in_normalizer_coset_eq
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (hpG : p ∣ Nat.card G) (P : Sylow p G)
    (m f t : ℕ) (htp : Nat.Coprime t p)
    (hPcard : Nat.card (P : Subgroup G) = p ^ m)
    (hNcard : Nat.card (Subgroup.normalizer (P : Set G)) = p ^ m * t)
    (hindex : (Subgroup.normalizer (P : Set G)).index = 1 + f * p ^ m)
    (hcount : Nat.card {g : G // g ≠ 1 ∧ g ^ p = 1} =
      (1 + f * p ^ m) * (p ^ m - 1))
    (hhalf : 2 * t = p ^ m - 1)
    (g : G) (hg : g ∉ Subgroup.normalizer (P : Set G)) :
    Nat.card {n : Subgroup.normalizer (P : Set G) //
      (g * (n.1 : G)) ^ p = 1} = 2 * t := by
  classical
  let N := Subgroup.normalizer (P : Set G)
  let O := {z : G // z ∉ N ∧ z ^ p = 1}
  let Q := G ⧸ N
  let q1 : Q := Quotient.mk'' (1 : G)
  let C := {q : Q // q ≠ q1}
  let coset : O → C := fun z ↦ ⟨Quotient.mk'' z.1, by
    intro hq
    have hrel : QuotientGroup.leftRel N z.1 1 := Quotient.exact hq
    have hzinv : z.1⁻¹ ∈ N := by
      simpa using QuotientGroup.leftRel_apply.mp hrel
    exact z.2.1 (by simpa using N.inv_mem hzinv)⟩
  have hfiber (c : C) : Nat.card {z : O // coset z = c} ≤ 2 * t := by
    let s : G := c.1.out
    have hsClass : Quotient.mk'' s = c.1 := Quotient.out_eq c.1
    have hs : s ∉ N := by
      intro hsN
      apply c.2
      rw [← hsClass]
      apply Quotient.sound
      apply QuotientGroup.leftRel_apply.mpr
      simpa using N.inv_mem hsN
    let toN : {z : O // coset z = c} →
        {n : N // (s * (n.1 : G)) ^ p = 1} := fun z ↦
      ⟨⟨s⁻¹ * z.1.1, by
        apply QuotientGroup.leftRel_apply.mp
        apply Quotient.exact
        exact hsClass.trans (congrArg (fun w : C ↦ w.1) z.2).symm⟩, by
        simpa [mul_assoc] using z.1.2.2⟩
    have htoN : Function.Injective toN := by
      intro z w hzw
      apply Subtype.ext
      apply Subtype.ext
      have hv := congrArg
        (fun n : {n : N // (s * (n.1 : G)) ^ p = 1} ↦ (n.1 : G)) hzw
      change s⁻¹ * z.1.1 = s⁻¹ * w.1.1 at hv
      exact mul_left_cancel hv
    exact (Nat.card_le_card_of_injective toN htoN).trans
      (dicksonWild_card_order_char_in_normalizer_coset_le
        G hpG P m t htp hNcard s hs)
  have hOcard : Nat.card O = f * p ^ m * (p ^ m - 1) :=
    dicksonWild_card_order_char_outside_normalizer G P m f hPcard hcount
  have hCcard : Nat.card C = f * p ^ m := by
    let _ : Fintype Q := Fintype.ofFinite Q
    let _ : Fintype C := Fintype.ofFinite C
    rw [Nat.card_eq_fintype_card]
    calc
      Fintype.card C = Fintype.card Q - 1 :=
        Fintype.card_subtype_compl (fun q : Q ↦ q = q1) |>.trans (by simp)
      _ = N.index - 1 := by
        rw [Subgroup.index_eq_card]
        exact congrArg (fun n ↦ n - 1) Nat.card_eq_fintype_card.symm
      _ = f * p ^ m := by rw [hindex]; omega
  have htotal : Nat.card O = 2 * t * Nat.card C := by
    rw [hOcard, hCcard, hhalf]
    ring
  have hfiberEq : ∀ c : C, Nat.card {z : O // coset z = c} = 2 * t :=
    DicksonWildAffine.card_fiber_eq_of_le_of_card_eq_mul coset (2 * t) hfiber htotal
  let cg : C := ⟨Quotient.mk'' g, by
    intro hq
    have hrel : QuotientGroup.leftRel N g 1 := Quotient.exact hq
    have hginv : g⁻¹ ∈ N := by simpa using QuotientGroup.leftRel_apply.mp hrel
    exact hg (by simpa using N.inv_mem hginv)⟩
  let toN : {z : O // coset z = cg} →
      {n : N // (g * (n.1 : G)) ^ p = 1} := fun z ↦
    ⟨⟨g⁻¹ * z.1.1, by
      apply QuotientGroup.leftRel_apply.mp
      apply Quotient.exact
      exact congrArg (fun w : C ↦ w.1) z.2 |>.symm⟩, by
      simpa [mul_assoc] using z.1.2.2⟩
  have htoN : Function.Injective toN := by
    intro z w hzw
    apply Subtype.ext
    apply Subtype.ext
    have hv := congrArg
      (fun n : {n : N // (g * (n.1 : G)) ^ p = 1} ↦ (n.1 : G)) hzw
    change g⁻¹ * z.1.1 = g⁻¹ * w.1.1 at hv
    exact mul_left_cancel hv
  have hlower : 2 * t ≤ Nat.card {n : N // (g * (n.1 : G)) ^ p = 1} := by
    rw [← hfiberEq cg]
    exact Nat.card_le_card_of_injective toN htoN
  exact Nat.le_antisymm
    (dicksonWild_card_order_char_in_normalizer_coset_le
      G hpG P m t htp hNcard g hg) hlower

private lemma dicksonWild_exists_matrix_normal_form
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (hpG : p ∣ Nat.card G) (P : Sylow p G)
    (m t : ℕ) (hm : 1 ≤ m) (htp : Nat.Coprime t p)
    (hNcard : Nat.card (Subgroup.normalizer (P : Set G)) = p ^ m * t)
    (hsandwich : p ^ m - 1 ≤ 2 * t) :
    ∃ (M : Subfield (K p)) (L : Subgroup Mˣ) (j : G →* PGL p)
      (coord : Subgroup.normalizer (P : Set G) → M × L),
      Finite M ∧ Nat.card M = p ^ m ∧ Nat.card L = t ∧
      Function.Injective j ∧ Function.Bijective coord ∧
      (∀ n : Subgroup.normalizer (P : Set G),
        j n.1 = Matrix.ProjGenLinGroup.map M.subtype
          (Matrix.ProjGenLinGroup.mk
            (DicksonWildAffine.affineGL (coord n).1 (coord n).2.1))) ∧
      ∀ g : G, g ∉ Subgroup.normalizer (P : Set G) →
        ∃ S : GL (Fin 2) (K p), Matrix.ProjGenLinGroup.mk S = j g ∧
          (S : Matrix (Fin 2) (Fin 2) (K p)) 1 0 ≠ 0 := by
  classical
  let N := Subgroup.normalizer (P : Set G)
  obtain ⟨a, B, e, he, hout⟩ := dicksonWild_normalizer_borel_coordinates G hpG P
  let _ : Finite B := Finite.of_surjective e e.surjective
  let H : Subgroup (DicksonWildAffine.Aff (K p)) := Subgroup.map
    DicksonWildAffine.borelMulEquivAffine.toMonoidHom B
  let eH : B ≃* H := DicksonWildAffine.borelMulEquivAffine.subgroupMap B
  let _ : Finite H := Finite.of_surjective eH eH.surjective
  have hHcard : Nat.card H = p ^ m * t := by
    rw [← Nat.card_congr eH.toEquiv, ← Nat.card_congr e.toEquiv]
    exact hNcard
  have hrange : Nat.card (DicksonWildAffine.rightRestrict H).range = t :=
    dicksonWild_affine_right_range_card H m t htp hHcard
  obtain ⟨M, c, L, coordH, hMfinite, hMcard, hLcard, hcoordH, hlower, hmatrix⟩ :=
    DicksonWildAffine.exists_affine_matrix_normal_form H m t hm hHcard hrange hsandwich
  let κ : PGL p := Matrix.ProjGenLinGroup.mk c
  let j : G →* PGL p :=
    (MulAut.conj κ).toMonoidHom.comp (a.toMonoidHom.comp G.subtype)
  let coord : N → M × L := fun n ↦ coordH (eH (e n))
  have hj : Function.Injective j :=
    (MulAut.conj κ).injective.comp (a.injective.comp G.subtype_injective)
  have hcoord : Function.Bijective coord :=
    hcoordH.comp (eH.bijective.comp e.bijective)
  refine ⟨M, L, j, coord, hMfinite, hMcard, hLcard, hj, hcoord, ?_, ?_⟩
  · intro n
    let b : B := e n
    let h : H := eH b
    have hmat := hmatrix h
    have hb : (b.1 : PGL p) = Matrix.ProjGenLinGroup.mk
        (DicksonWildAffine.affineGL h.1.left.toAdd h.1.right) := by
      calc
        (b.1 : PGL p) = Matrix.ProjGenLinGroup.mk
            (DicksonWildAffine.affineGL (DicksonWildAffine.gamma b.1)
              (DicksonWildAffine.lambda b.1)) :=
          (DicksonWildAffine.mk_affineGL_gamma_lambda b.1).symm
        _ = Matrix.ProjGenLinGroup.mk
            (DicksonWildAffine.affineGL h.1.left.toAdd h.1.right) := by rfl
    calc
      j n.1 = κ * a (n.1 : PGL p) * κ⁻¹ := rfl
      _ = Matrix.ProjGenLinGroup.mk c * b.1 *
          (Matrix.ProjGenLinGroup.mk c)⁻¹ := by rw [he n]
      _ = Matrix.ProjGenLinGroup.mk
          (c * DicksonWildAffine.affineGL h.1.left.toAdd h.1.right * c⁻¹) := by
        simp only [map_mul, map_inv]
        rw [hb]
      _ = Matrix.ProjGenLinGroup.mk
          (Matrix.GeneralLinearGroup.map M.subtype
            (DicksonWildAffine.affineGL (coord n).1 (coord n).2.1)) := by
        exact congrArg Matrix.ProjGenLinGroup.mk hmat
      _ = Matrix.ProjGenLinGroup.map M.subtype
          (Matrix.ProjGenLinGroup.mk
            (DicksonWildAffine.affineGL (coord n).1 (coord n).2.1)) := by
        rw [Matrix.ProjGenLinGroup.map_mk]
  · intro g hg
    let A : GL (Fin 2) (K p) := DicksonWildAffine.lift (a (g : PGL p))
    let S : GL (Fin 2) (K p) := c * A * c⁻¹
    refine ⟨S, ?_, hlower A (hout g hg)⟩
    calc
      Matrix.ProjGenLinGroup.mk S = Matrix.ProjGenLinGroup.mk c *
          Matrix.ProjGenLinGroup.mk A * (Matrix.ProjGenLinGroup.mk c)⁻¹ := by
        simp [S]
      _ = κ * a (g : PGL p) * κ⁻¹ := by
        rw [DicksonWildAffine.mk_lift]
      _ = j g := rfl

private noncomputable def dicksonWildPoint {F : Type*} [Field F] [DecidableEq F] (z : F) :
    Projectivization F (Fin 2 → F) :=
  OnePoint.equivProjectivization F (z : OnePoint F)

private lemma dicksonWild_card_order_char_with_multiplier_eq_two
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (hpG : p ∣ Nat.card G) (P : Sylow p G)
    (m f t : ℕ) (htp : Nat.Coprime t p)
    (hPcard : Nat.card (P : Subgroup G) = p ^ m)
    (hNcard : Nat.card (Subgroup.normalizer (P : Set G)) = p ^ m * t)
    (hindex : (Subgroup.normalizer (P : Set G)).index = 1 + f * p ^ m)
    (hcount : Nat.card {g : G // g ≠ 1 ∧ g ^ p = 1} =
      (1 + f * p ^ m) * (p ^ m - 1))
    (hhalf : 2 * t = p ^ m - 1)
    (M : Subfield (K p)) [Finite M] (L : Subgroup Mˣ)
    (hLcard : Nat.card L = t) (j : G →* PGL p) (hj : Function.Injective j)
    (coord : Subgroup.normalizer (P : Set G) → M × L)
    (hcoord : Function.Bijective coord)
    (hnormal : ∀ n : Subgroup.normalizer (P : Set G),
      j n.1 = Matrix.ProjGenLinGroup.map M.subtype
        (Matrix.ProjGenLinGroup.mk
          (DicksonWildAffine.affineGL (coord n).1 (coord n).2.1)))
    (hout : ∀ g : G, g ∉ Subgroup.normalizer (P : Set G) →
      ∃ S : GL (Fin 2) (K p), Matrix.ProjGenLinGroup.mk S = j g ∧
        (S : Matrix (Fin 2) (Fin 2) (K p)) 1 0 ≠ 0)
    (g : G) (hg : g ∉ Subgroup.normalizer (P : Set G)) (l : L) :
    Nat.card {n : {n : Subgroup.normalizer (P : Set G) //
      (g * (n.1 : G)) ^ p = 1} // (coord n.1).2 = l} = 2 := by
  classical
  let N := Subgroup.normalizer (P : Set G)
  let E := {n : N // (g * (n.1 : G)) ^ p = 1}
  let toL : E → L := fun n ↦ (coord n.1).2
  let A : N → GL (Fin 2) (K p) := fun n ↦
    Matrix.GeneralLinearGroup.map M.subtype
      (DicksonWildAffine.affineGL (coord n).1 (coord n).2.1)
  have hA (n : N) : A n = DicksonWildAffine.affineGL ((coord n).1 : K p)
      (Units.map M.subtype.toMonoidHom (coord n).2.1) :=
    DicksonWildAffine.affineGL_map_subfield M (coord n).1 (coord n).2.1
  have hnormal' (n : N) : j n.1 = Matrix.ProjGenLinGroup.mk (A n) := by
    rw [hnormal n, Matrix.ProjGenLinGroup.map_mk]
  obtain ⟨S, hS, hS10⟩ := hout g hg
  have hEcard : Nat.card E = 2 * t :=
    dicksonWild_card_order_char_in_normalizer_coset_eq G hpG P m f t htp
      hPcard hNcard hindex hcount hhalf g hg
  have hfiber (u : L) : Nat.card {n : E // toL n = u} ≤ 2 := by
    let uK : (K p)ˣ := Units.map M.subtype.toMonoidHom u.1
    let c : K p := 4 * Matrix.det (S : Matrix (Fin 2) (Fin 2) (K p)) * (uK : K p)
    let toRoot : {n : E // toL n = u} → {x : K p // x ^ 2 = c} := fun n ↦ ⟨
      Matrix.trace (((S * A n.1.1 : GL (Fin 2) (K p)) :
        Matrix (Fin 2) (Fin 2) (K p))), by
        have hnSecond : (coord n.1.1).2 = u := n.2
        have hgne : g * (n.1.1.1 : G) ≠ 1 := by
          intro hone
          apply hg
          have hgeq : g = (n.1.1.1 : G)⁻¹ := eq_inv_of_mul_eq_one_left hone
          rw [hgeq]
          exact N.inv_mem n.1.1.2
        have horderG : orderOf (g * (n.1.1.1 : G)) = p :=
          orderOf_eq_prime n.1.2 hgne
        have horderJ : orderOf (j (g * (n.1.1.1 : G))) = p :=
          (orderOf_injective j hj (g * (n.1.1.1 : G))).trans horderG
        have hmk : Matrix.ProjGenLinGroup.mk (S * A n.1.1) =
            j (g * (n.1.1.1 : G)) := by
          calc
            Matrix.ProjGenLinGroup.mk (S * A n.1.1) =
                Matrix.ProjGenLinGroup.mk S * Matrix.ProjGenLinGroup.mk (A n.1.1) :=
              map_mul Matrix.ProjGenLinGroup.mk S (A n.1.1)
            _ = j g * j n.1.1.1 := by rw [hS, hnormal' n.1.1]
            _ = j (g * (n.1.1.1 : G)) := (map_mul j g n.1.1.1).symm
        have hpar : ((S * A n.1.1 : GL (Fin 2) (K p)) :
            Matrix (Fin 2) (Fin 2) (K p)).IsParabolic := by
          apply dicksonWild_lift_isParabolic_of_order_eq_char
          rw [hmk]
          exact horderJ
        have hdisc := hpar.2
        rw [Matrix.discr_fin_two] at hdisc
        have heq := sub_eq_zero.mp hdisc
        rw [hA n.1.1, hnSecond, DicksonWildAffine.det_mul_affineGL] at heq
        rw [hA n.1.1, hnSecond]
        simpa [c, uK, mul_assoc] using heq⟩
    have htoRoot : Function.Injective toRoot := by
      intro x y hxy
      have hxSecond : (coord x.1.1).2 = u := x.2
      have hySecond : (coord y.1.1).2 = u := y.2
      have htrace := congrArg (fun z : {w : K p // w ^ 2 = c} ↦ z.1) hxy
      change Matrix.trace (((S * A x.1.1 : GL (Fin 2) (K p)) :
          Matrix (Fin 2) (Fin 2) (K p))) =
        Matrix.trace (((S * A y.1.1 : GL (Fin 2) (K p)) :
          Matrix (Fin 2) (Fin 2) (K p))) at htrace
      rw [hA x.1.1, hA y.1.1, hxSecond, hySecond,
        DicksonWildAffine.trace_mul_affineGL,
        DicksonWildAffine.trace_mul_affineGL] at htrace
      have hfirst : (coord x.1.1).1 = (coord y.1.1).1 := by
        apply Subtype.ext
        apply mul_left_cancel₀ hS10
        linear_combination htrace
      have hcoordEq : coord x.1.1 = coord y.1.1 := by
        apply Prod.ext hfirst
        exact hxSecond.trans hySecond.symm
      have hn : x.1.1 = y.1.1 := hcoord.1 hcoordEq
      apply Subtype.ext
      apply Subtype.ext
      exact hn
    let q : (K p)[X] := Polynomial.X ^ 2 - Polynomial.C c
    have hq0 : q ≠ 0 := Polynomial.X_pow_sub_C_ne_zero (by decide) c
    have hfinite : Set.Finite {x : K p | x ^ 2 = c} := by
      apply (Finset.finite_toSet (q.map (algebraMap (K p) (K p))).roots.toFinset).subset
      intro x hx
      rw [show (q.map (algebraMap (K p) (K p))).roots.toFinset = q.rootSet (K p) by rfl,
        Polynomial.mem_rootSet_of_ne hq0]
      change x ^ 2 = c at hx
      simpa [q] using sub_eq_zero.mpr hx
    let _ : Fintype {x : K p // x ^ 2 = c} := hfinite.fintype
    exact (Nat.card_le_card_of_injective toRoot htoRoot).trans
      (DicksonWildAffine.card_quadraticFiber_le_two c)
  have htotal : Nat.card E = 2 * Nat.card L := by rw [hEcard, hLcard]
  have hfiberEq : ∀ u : L, Nat.card {n : E // toL n = u} = 2 :=
    DicksonWildAffine.card_fiber_eq_of_le_of_card_eq_mul toL 2 hfiber htotal
  exact hfiberEq l

set_option maxHeartbeats 800000 in
-- The trace-fiber argument expands several nested finite subtypes.
private lemma dicksonWild_exists_order_char_with_multiplier_and_trace
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (hpG : p ∣ Nat.card G) (P : Sylow p G)
    (m f t : ℕ) (htp : Nat.Coprime t p)
    (hPcard : Nat.card (P : Subgroup G) = p ^ m)
    (hNcard : Nat.card (Subgroup.normalizer (P : Set G)) = p ^ m * t)
    (hindex : (Subgroup.normalizer (P : Set G)).index = 1 + f * p ^ m)
    (hcount : Nat.card {g : G // g ≠ 1 ∧ g ^ p = 1} =
      (1 + f * p ^ m) * (p ^ m - 1))
    (hhalf : 2 * t = p ^ m - 1)
    (M : Subfield (K p)) [Finite M] (L : Subgroup Mˣ)
    (hLcard : Nat.card L = t) (j : G →* PGL p) (hj : Function.Injective j)
    (coord : Subgroup.normalizer (P : Set G) → M × L)
    (hcoord : Function.Bijective coord)
    (hnormal : ∀ n : Subgroup.normalizer (P : Set G),
      j n.1 = Matrix.ProjGenLinGroup.map M.subtype
        (Matrix.ProjGenLinGroup.mk
          (DicksonWildAffine.affineGL (coord n).1 (coord n).2.1)))
    (hout : ∀ g : G, g ∉ Subgroup.normalizer (P : Set G) →
      ∃ S : GL (Fin 2) (K p), Matrix.ProjGenLinGroup.mk S = j g ∧
        (S : Matrix (Fin 2) (Fin 2) (K p)) 1 0 ≠ 0)
    (g : G) (hg : g ∉ Subgroup.normalizer (P : Set G))
    (S : GL (Fin 2) (K p)) (hS : Matrix.ProjGenLinGroup.mk S = j g)
    (hS10 : (S : Matrix (Fin 2) (Fin 2) (K p)) 1 0 ≠ 0)
    (l : L) (r : K p)
    (hr : r ^ 2 = 4 * Matrix.det (S : Matrix (Fin 2) (Fin 2) (K p)) *
      (Units.map M.subtype.toMonoidHom l.1 : K p)) :
    ∃ n : Subgroup.normalizer (P : Set G),
      (g * (n.1 : G)) ^ p = 1 ∧ (coord n).2 = l ∧
      Matrix.trace (((S * Matrix.GeneralLinearGroup.map M.subtype
        (DicksonWildAffine.affineGL (coord n).1 (coord n).2.1) :
          GL (Fin 2) (K p)) : Matrix (Fin 2) (Fin 2) (K p))) = r := by
  classical
  let N := Subgroup.normalizer (P : Set G)
  let X := {n : {n : N // (g * (n.1 : G)) ^ p = 1} // (coord n.1).2 = l}
  have hXcard : Nat.card X = 2 :=
    dicksonWild_card_order_char_with_multiplier_eq_two G hpG P m f t htp
      hPcard hNcard hindex hcount hhalf M L hLcard j hj coord hcoord hnormal hout g hg l
  obtain ⟨x, y, hxy, -⟩ := Nat.card_eq_two_iff.mp hXcard
  let A : N → GL (Fin 2) (K p) := fun n ↦
    Matrix.GeneralLinearGroup.map M.subtype
      (DicksonWildAffine.affineGL (coord n).1 (coord n).2.1)
  have hA (n : N) : A n = DicksonWildAffine.affineGL ((coord n).1 : K p)
      (Units.map M.subtype.toMonoidHom (coord n).2.1) :=
    DicksonWildAffine.affineGL_map_subfield M (coord n).1 (coord n).2.1
  have hnormal' (n : N) : j n.1 = Matrix.ProjGenLinGroup.mk (A n) := by
    rw [hnormal n, Matrix.ProjGenLinGroup.map_mk]
  have htraceSq (z : X) :
      Matrix.trace (((S * A z.1.1 : GL (Fin 2) (K p)) :
        Matrix (Fin 2) (Fin 2) (K p))) ^ 2 = r ^ 2 := by
    have hgne : g * (z.1.1.1 : G) ≠ 1 := by
      intro hone
      apply hg
      have hgeq : g = (z.1.1.1 : G)⁻¹ := eq_inv_of_mul_eq_one_left hone
      rw [hgeq]
      exact N.inv_mem z.1.1.2
    have horderG : orderOf (g * (z.1.1.1 : G)) = p :=
      orderOf_eq_prime z.1.2 hgne
    have horderJ : orderOf (j (g * (z.1.1.1 : G))) = p :=
      (orderOf_injective j hj (g * (z.1.1.1 : G))).trans horderG
    have hmk : Matrix.ProjGenLinGroup.mk (S * A z.1.1) =
        j (g * (z.1.1.1 : G)) := by
      calc
        Matrix.ProjGenLinGroup.mk (S * A z.1.1) =
            Matrix.ProjGenLinGroup.mk S * Matrix.ProjGenLinGroup.mk (A z.1.1) :=
          map_mul Matrix.ProjGenLinGroup.mk S (A z.1.1)
        _ = j g * j z.1.1.1 := by rw [hS, hnormal' z.1.1]
        _ = j (g * (z.1.1.1 : G)) := (map_mul j g z.1.1.1).symm
    have hpar : ((S * A z.1.1 : GL (Fin 2) (K p)) :
        Matrix (Fin 2) (Fin 2) (K p)).IsParabolic := by
      apply dicksonWild_lift_isParabolic_of_order_eq_char
      rw [hmk]
      exact horderJ
    have hdisc := hpar.2
    rw [Matrix.discr_fin_two] at hdisc
    have heq := sub_eq_zero.mp hdisc
    have hdet : Matrix.det (((S * A z.1.1 : GL (Fin 2) (K p)) :
        Matrix (Fin 2) (Fin 2) (K p))) =
        Matrix.det (S : Matrix (Fin 2) (Fin 2) (K p)) *
          (Units.map M.subtype.toMonoidHom l.1 : K p) := by
      rw [hA z.1.1, z.2, DicksonWildAffine.det_mul_affineGL]
    rw [hdet] at heq
    calc
      Matrix.trace (((S * A z.1.1 : GL (Fin 2) (K p)) :
          Matrix (Fin 2) (Fin 2) (K p))) ^ 2 =
          4 * (Matrix.det (S : Matrix (Fin 2) (Fin 2) (K p)) *
            (Units.map M.subtype.toMonoidHom l.1 : K p)) := heq
      _ = 4 * Matrix.det (S : Matrix (Fin 2) (Fin 2) (K p)) *
          (Units.map M.subtype.toMonoidHom l.1 : K p) := by ring
      _ = r ^ 2 := hr.symm
  have htraceInjective : Function.Injective (fun z : X ↦
      Matrix.trace (((S * A z.1.1 : GL (Fin 2) (K p)) :
        Matrix (Fin 2) (Fin 2) (K p)))) := by
    intro z w htrace
    change Matrix.trace (((S * A z.1.1 : GL (Fin 2) (K p)) :
        Matrix (Fin 2) (Fin 2) (K p))) =
      Matrix.trace (((S * A w.1.1 : GL (Fin 2) (K p)) :
        Matrix (Fin 2) (Fin 2) (K p))) at htrace
    rw [hA z.1.1, hA w.1.1, z.2, w.2,
      DicksonWildAffine.trace_mul_affineGL,
      DicksonWildAffine.trace_mul_affineGL] at htrace
    have hfirst : (coord z.1.1).1 = (coord w.1.1).1 := by
      apply Subtype.ext
      apply mul_left_cancel₀ hS10
      linear_combination htrace
    have hcoordEq : coord z.1.1 = coord w.1.1 := by
      apply Prod.ext hfirst
      exact z.2.trans w.2.symm
    have hn : z.1.1 = w.1.1 := hcoord.1 hcoordEq
    apply Subtype.ext
    apply Subtype.ext
    exact hn
  have hxCases : Matrix.trace (((S * A x.1.1 : GL (Fin 2) (K p)) :
      Matrix (Fin 2) (Fin 2) (K p))) = r ∨
      Matrix.trace (((S * A x.1.1 : GL (Fin 2) (K p)) :
        Matrix (Fin 2) (Fin 2) (K p))) = -r :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (htraceSq x)
  rcases hxCases with hx | hx
  · exact ⟨x.1.1, x.1.2, x.2, hx⟩
  have hyCases : Matrix.trace (((S * A y.1.1 : GL (Fin 2) (K p)) :
      Matrix (Fin 2) (Fin 2) (K p))) = r ∨
      Matrix.trace (((S * A y.1.1 : GL (Fin 2) (K p)) :
        Matrix (Fin 2) (Fin 2) (K p))) = -r :=
    sq_eq_sq_iff_eq_or_eq_neg.mp (htraceSq y)
  rcases hyCases with hy | hy
  · exact ⟨y.1.1, y.1.2, y.2, hy⟩
  exact (hxy (htraceInjective (hx.trans hy.symm))).elim

private lemma dicksonWild_normalized_order_char_lift_entries_mem
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (hpG : p ∣ Nat.card G) (P : Sylow p G)
    (m f t : ℕ) (htp : Nat.Coprime t p)
    (hPcard : Nat.card (P : Subgroup G) = p ^ m)
    (hNcard : Nat.card (Subgroup.normalizer (P : Set G)) = p ^ m * t)
    (hindex : (Subgroup.normalizer (P : Set G)).index = 1 + f * p ^ m)
    (hcount : Nat.card {g : G // g ≠ 1 ∧ g ^ p = 1} =
      (1 + f * p ^ m) * (p ^ m - 1))
    (hhalf : 2 * t = p ^ m - 1)
    (M : Subfield (K p)) [Finite M] (hMcard : Nat.card M = p ^ m)
    (L : Subgroup Mˣ) (hLcard : Nat.card L = t)
    (hLsquare : L = (powMonoidHom 2 : Mˣ →* Mˣ).range)
    (j : G →* PGL p) (hj : Function.Injective j)
    (coord : Subgroup.normalizer (P : Set G) → M × L)
    (hcoord : Function.Bijective coord)
    (hnormal : ∀ n : Subgroup.normalizer (P : Set G),
      j n.1 = Matrix.ProjGenLinGroup.map M.subtype
        (Matrix.ProjGenLinGroup.mk
          (DicksonWildAffine.affineGL (coord n).1 (coord n).2.1)))
    (hout : ∀ g : G, g ∉ Subgroup.normalizer (P : Set G) →
      ∃ S : GL (Fin 2) (K p), Matrix.ProjGenLinGroup.mk S = j g ∧
        (S : Matrix (Fin 2) (Fin 2) (K p)) 1 0 ≠ 0)
    (hq : 3 < p ^ m) (g : G) (hg : g ∉ Subgroup.normalizer (P : Set G))
    (S : GL (Fin 2) (K p)) (hS : Matrix.ProjGenLinGroup.mk S = j g)
    (htrace : Matrix.trace (S : Matrix (Fin 2) (Fin 2) (K p)) = 2)
    (hdet : Matrix.det (S : Matrix (Fin 2) (Fin 2) (K p)) = 1)
    (hS10 : (S : Matrix (Fin 2) (Fin 2) (K p)) 1 0 ≠ 0) :
    ∀ i k, (S : Matrix (Fin 2) (Fin 2) (K p)) i k ∈ M := by
  classical
  have htwo : (2 : K p) ≠ 0 := by
    apply (CharP.cast_eq_zero_iff (K p) p 2).not.mpr
    intro hpdiv
    have := Nat.le_of_dvd (by decide : 0 < 2) hpdiv
    have hpgt : 2 < p := Fact.out
    omega
  have hfour : (4 : K p) ≠ 0 := by
    rw [show (4 : K p) = 2 * 2 by norm_num]
    exact mul_ne_zero htwo htwo
  have htraceEntries : (S : Matrix (Fin 2) (Fin 2) (K p)) 0 0 + S 1 1 = 2 := by
    simpa [Matrix.trace, Fin.sum_univ_two] using htrace
  have findTrace (l : L) (r : K p)
      (hr : r ^ 2 = 4 * Matrix.det (S : Matrix (Fin 2) (Fin 2) (K p)) *
        (Units.map M.subtype.toMonoidHom l.1 : K p)) :
      ∃ n : Subgroup.normalizer (P : Set G),
        (g * (n.1 : G)) ^ p = 1 ∧ (coord n).2 = l ∧
        Matrix.trace (((S * Matrix.GeneralLinearGroup.map M.subtype
          (DicksonWildAffine.affineGL (coord n).1 (coord n).2.1) :
            GL (Fin 2) (K p)) : Matrix (Fin 2) (Fin 2) (K p))) = r :=
    dicksonWild_exists_order_char_with_multiplier_and_trace G hpG P m f t htp
      hPcard hNcard hindex hcount hhalf M L hLcard j hj coord hcoord hnormal hout
      g hg S hS hS10 l r hr
  have hnegRoot : (-2 : K p) ^ 2 =
      4 * Matrix.det (S : Matrix (Fin 2) (Fin 2) (K p)) *
        (Units.map M.subtype.toMonoidHom (1 : L).1 : K p) := by
    rw [hdet]
    norm_num
  obtain ⟨nNeg, -, hnNeg, htrNeg⟩ := findTrace 1 (-2) hnegRoot
  rw [DicksonWildAffine.affineGL_map_subfield, hnNeg,
    DicksonWildAffine.trace_mul_affineGL] at htrNeg
  have hunit : Units.map M.subtype.toMonoidHom (1 : L).1 = (1 : (K p)ˣ) := by
    exact map_one (Units.map M.subtype.toMonoidHom)
  have hunitVal : (Units.map M.subtype.toMonoidHom (1 : L).1 : K p) = 1 :=
    congrArg Units.val hunit
  rw [hunitVal, mul_one] at htrNeg
  change (S : Matrix (Fin 2) (Fin 2) (K p)) 0 0 +
      S 1 0 * ((coord nNeg).1 : K p) + S 1 1 = -2 at htrNeg
  let xNeg : M := (coord nNeg).1
  have hgammaMul : (S : Matrix (Fin 2) (Fin 2) (K p)) 1 0 * (xNeg : K p) = -4 := by
    dsimp [xNeg]
    linear_combination htrNeg - htraceEntries
  have hxNeg : (xNeg : K p) ≠ 0 := by
    intro hx
    rw [hx, mul_zero] at hgammaMul
    exact hfour (by simpa using hgammaMul.symm)
  have hgammaEq : (S : Matrix (Fin 2) (Fin 2) (K p)) 1 0 =
      (-4 : K p) / (xNeg : K p) := (eq_div_iff hxNeg).2 hgammaMul
  have hgamma : (S : Matrix (Fin 2) (Fin 2) (K p)) 1 0 ∈ M := by
    rw [hgammaEq]
    exact M.div_mem (M.neg_mem (natCast_mem M 4)) xNeg.2
  let _ : Fintype M := Fintype.ofFinite M
  obtain ⟨eta, heta0, heta1, hetaNeg1⟩ :
      ∃ eta : M, eta ≠ 0 ∧ eta ≠ 1 ∧ eta ≠ -1 := by
    by_contra hnone
    push Not at hnone
    have hsubset : (Finset.univ : Finset M) ⊆ {0, 1, -1} := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton]
      by_cases hx0 : x = 0
      · exact Or.inl hx0
      by_cases hx1 : x = 1
      · exact Or.inr (Or.inl hx1)
      · exact Or.inr (Or.inr (hnone x hx0 hx1))
    have hsmall : Fintype.card M ≤ 3 := by
      calc
        Fintype.card M = (Finset.univ : Finset M).card := by simp
        _ ≤ ({0, 1, -1} : Finset M).card := Finset.card_le_card hsubset
        _ ≤ 3 := Finset.card_le_three
    rw [← Nat.card_eq_fintype_card, hMcard] at hsmall
    omega
  let etaU : Mˣ := Units.mk0 eta heta0
  have hetaSqMem : etaU ^ 2 ∈ L := by
    rw [hLsquare]
    exact ⟨etaU, rfl⟩
  let lEta : L := ⟨etaU ^ 2, hetaSqMem⟩
  have hetaRoot : (2 * (eta : K p)) ^ 2 =
      4 * Matrix.det (S : Matrix (Fin 2) (Fin 2) (K p)) *
        (Units.map M.subtype.toMonoidHom lEta.1 : K p) := by
    rw [hdet]
    simp [lEta, etaU]
    ring
  obtain ⟨nEta, -, hnEta, htrEta⟩ := findTrace lEta (2 * (eta : K p)) hetaRoot
  rw [DicksonWildAffine.affineGL_map_subfield, hnEta,
    DicksonWildAffine.trace_mul_affineGL] at htrEta
  have hetaUnitVal :
      (Units.map M.subtype.toMonoidHom (etaU ^ 2) : K p) = (eta : K p) ^ 2 := by
    rfl
  change (S : Matrix (Fin 2) (Fin 2) (K p)) 0 0 *
      (Units.map M.subtype.toMonoidHom (etaU ^ 2) : K p) +
      S 1 0 * ((coord nEta).1 : K p) + S 1 1 = 2 * (eta : K p) at htrEta
  rw [hetaUnitVal] at htrEta
  let gammaM : M := ⟨(S : Matrix (Fin 2) (Fin 2) (K p)) 1 0, hgamma⟩
  let denom : M := eta ^ 2 - 1
  let numer : M := 2 * eta - 2 - gammaM * (coord nEta).1
  have hdenom : (denom : K p) ≠ 0 := by
    intro hzero
    have hetaSq : eta ^ 2 = 1 := by
      apply Subtype.ext
      exact sub_eq_zero.mp hzero
    rcases sq_eq_one_iff.mp hetaSq with h | h
    · exact heta1 h
    · exact hetaNeg1 h
  have halphaMul : (S : Matrix (Fin 2) (Fin 2) (K p)) 0 0 * (denom : K p) =
      (numer : K p) := by
    dsimp [denom, numer, gammaM]
    calc
      (S : Matrix (Fin 2) (Fin 2) (K p)) 0 0 * ((eta : K p) ^ 2 - 1) =
          (S 0 0 * (eta : K p) ^ 2 + S 1 0 * ((coord nEta).1 : K p) + S 1 1) -
            (S 0 0 + S 1 1) - S 1 0 * ((coord nEta).1 : K p) := by ring
      _ = 2 * (eta : K p) - 2 - S 1 0 * ((coord nEta).1 : K p) := by
        rw [htrEta, htraceEntries]
  have halphaEq : (S : Matrix (Fin 2) (Fin 2) (K p)) 0 0 =
      (numer : K p) / (denom : K p) := (eq_div_iff hdenom).2 halphaMul
  have halpha : (S : Matrix (Fin 2) (Fin 2) (K p)) 0 0 ∈ M := by
    rw [halphaEq]
    exact (numer / denom).2
  have hdeltaEq : (S : Matrix (Fin 2) (Fin 2) (K p)) 1 1 =
      2 - S 0 0 := by linear_combination htraceEntries
  have hdelta : (S : Matrix (Fin 2) (Fin 2) (K p)) 1 1 ∈ M := by
    rw [hdeltaEq]
    exact M.sub_mem (natCast_mem M 2) halpha
  have hdetEntries : (S : Matrix (Fin 2) (Fin 2) (K p)) 0 0 * S 1 1 -
      S 0 1 * S 1 0 = 1 := by
    simpa [Matrix.det_fin_two] using hdet
  have hbetaMul : (S : Matrix (Fin 2) (Fin 2) (K p)) 0 1 * S 1 0 =
      S 0 0 * S 1 1 - 1 := by
    calc
      (S : Matrix (Fin 2) (Fin 2) (K p)) 0 1 * S 1 0 =
          S 0 0 * S 1 1 - (S 0 0 * S 1 1 - S 0 1 * S 1 0) := by ring
      _ = S 0 0 * S 1 1 - 1 := by rw [hdetEntries]
  have hbetaEq : (S : Matrix (Fin 2) (Fin 2) (K p)) 0 1 =
      (S 0 0 * S 1 1 - 1) / S 1 0 := (eq_div_iff hS10).2 hbetaMul
  have hbeta : (S : Matrix (Fin 2) (Fin 2) (K p)) 0 1 ∈ M := by
    rw [hbetaEq]
    exact M.div_mem (M.sub_mem (M.mul_mem halpha hdelta) (M.one_mem)) hgamma
  intro i k
  fin_cases i <;> fin_cases k
  · exact halpha
  · exact hbeta
  · exact hgamma
  · exact hdelta

set_option maxHeartbeats 800000 in
-- The containment proof instantiates the trace-fiber lemma twice in dependent subtypes.
private lemma dicksonWild_range_le_embedded_psl_of_half
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (hpG : p ∣ Nat.card G) (P : Sylow p G)
    (m f t : ℕ) (htp : Nat.Coprime t p)
    (hPcard : Nat.card (P : Subgroup G) = p ^ m)
    (hNcard : Nat.card (Subgroup.normalizer (P : Set G)) = p ^ m * t)
    (hindex : (Subgroup.normalizer (P : Set G)).index = 1 + f * p ^ m)
    (hcount : Nat.card {g : G // g ≠ 1 ∧ g ^ p = 1} =
      (1 + f * p ^ m) * (p ^ m - 1))
    (hhalf : 2 * t = p ^ m - 1)
    (M : Subfield (K p)) [Finite M] (hMcard : Nat.card M = p ^ m)
    (L : Subgroup Mˣ) (hLcard : Nat.card L = t)
    (j : G →* PGL p) (hj : Function.Injective j)
    (coord : Subgroup.normalizer (P : Set G) → M × L)
    (hcoord : Function.Bijective coord)
    (hnormal : ∀ n : Subgroup.normalizer (P : Set G),
      j n.1 = Matrix.ProjGenLinGroup.map M.subtype
        (Matrix.ProjGenLinGroup.mk
          (DicksonWildAffine.affineGL (coord n).1 (coord n).2.1)))
    (hout : ∀ g : G, g ∉ Subgroup.normalizer (P : Set G) →
      ∃ S : GL (Fin 2) (K p), Matrix.ProjGenLinGroup.mk S = j g ∧
        (S : Matrix (Fin 2) (Fin 2) (K p)) 1 0 ≠ 0)
    (hq : 3 < p ^ m) :
    j.range ≤ ((Matrix.ProjGenLinGroup.map M.subtype).comp
      Matrix.ProjectiveSpecialLinearGroup.toPGL).range := by
  classical
  let N := Subgroup.normalizer (P : Set G)
  let pslEmbed : Matrix.ProjectiveSpecialLinearGroup (Fin 2) M →* PGL p :=
    (Matrix.ProjGenLinGroup.map M.subtype).comp
      Matrix.ProjectiveSpecialLinearGroup.toPGL
  have hLsquare : L = (powMonoidHom 2 : Mˣ →* Mˣ).range :=
    DicksonWildAffine.subgroup_eq_square_range_of_card L (p ^ m) t hMcard hLcard hhalf
  have hNmem (n : N) : j n.1 ∈ pslEmbed.range := by
    have hl : (coord n).2.1 ∈ (powMonoidHom 2 : Mˣ →* Mˣ).range := by
      rw [← hLsquare]
      exact (coord n).2.2
    obtain ⟨v, hv⟩ := hl
    have hv' : v ^ 2 = (coord n).2.1 := by simpa using hv
    have hdetAff : v ^ 2 = Matrix.GeneralLinearGroup.det
        (DicksonWildAffine.affineGL (coord n).1 (coord n).2.1) := by
      rw [hv']
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.val_det_apply]
      simp [DicksonWildAffine.affineGL, Matrix.det_fin_two]
    obtain ⟨z, hz⟩ := dicksonWild_exists_psl_preimage_of_det_square
      (DicksonWildAffine.affineGL (coord n).1 (coord n).2.1) v hdetAff
    refine ⟨z, ?_⟩
    change Matrix.ProjGenLinGroup.map M.subtype
      (Matrix.ProjectiveSpecialLinearGroup.toPGL z) = j n.1
    rw [hz, hnormal n]
  rintro y ⟨g, rfl⟩
  by_cases hg : g ∈ N
  · exact hNmem ⟨g, hg⟩
  · have hfiber : Nat.card {n : {n : N // (g * (n.1 : G)) ^ p = 1} //
        (coord n.1).2 = 1} = 2 :=
      dicksonWild_card_order_char_with_multiplier_eq_two G hpG P m f t htp
        hPcard hNcard hindex hcount hhalf M L hLcard j hj coord hcoord hnormal hout
          g hg 1
    have hnonempty : Nonempty {n : {n : N // (g * (n.1 : G)) ^ p = 1} //
        (coord n.1).2 = 1} :=
      (Nat.card_pos_iff.mp (by rw [hfiber]; omega)).1
    obtain ⟨w⟩ := hnonempty
    let n : N := w.1.1
    let z : G := g * (n.1 : G)
    have hzpow : z ^ p = 1 := w.1.2
    have hzOut : z ∉ N := by
      intro hzN
      apply hg
      have hgeq : g = z * (n.1 : G)⁻¹ := by dsimp [z]; group
      rw [hgeq]
      exact N.mul_mem hzN (N.inv_mem n.2)
    have hzNe : z ≠ 1 := by
      intro hz
      apply hzOut
      rw [hz]
      exact N.one_mem
    have hzOrder : orderOf z = p := orderOf_eq_prime hzpow hzNe
    obtain ⟨S₀, hS₀, hS₀10⟩ := hout z hzOut
    have hS₀Order : orderOf (Matrix.ProjGenLinGroup.mk S₀) = p := by
      rw [hS₀]
      exact (orderOf_injective j hj z).trans hzOrder
    obtain ⟨S, hSmk, hStrace, hSdet, hS10⟩ :=
      dicksonWild_exists_normalized_lift_of_orderOf_eq_char S₀ hS₀Order hS₀10
    have hSj : Matrix.ProjGenLinGroup.mk S = j z := hSmk.trans hS₀
    have hentries := dicksonWild_normalized_order_char_lift_entries_mem
      G hpG P m f t htp hPcard hNcard hindex hcount hhalf M hMcard L hLcard
      hLsquare j hj coord hcoord hnormal hout hq z hzOut S hSj hStrace hSdet hS10
    obtain ⟨s, hs⟩ :=
      dicksonWild_exists_embedded_psl_preimage_of_entries_mem M S hentries hSdet
    have hzMem : j z ∈ pslEmbed.range := by
      refine ⟨s, ?_⟩
      exact hs.trans hSj
    have hnMem : j n.1 ∈ pslEmbed.range := hNmem n
    have hjg : j g = j z * (j n.1)⁻¹ := by
      dsimp [z]
      rw [map_mul]
      group
    rw [hjg]
    exact pslEmbed.range.mul_mem hzMem (pslEmbed.range.inv_mem hnMem)

private lemma dicksonWild_psl_case_of_half_gt_three
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (hpG : p ∣ Nat.card G) (P : Sylow p G)
    (m f t : ℕ) (hm : 1 ≤ m) (hf : 0 < f) (htp : Nat.Coprime t p)
    (hPcard : Nat.card (P : Subgroup G) = p ^ m)
    (hNcard : Nat.card (Subgroup.normalizer (P : Set G)) = p ^ m * t)
    (hindex : (Subgroup.normalizer (P : Set G)).index = 1 + f * p ^ m)
    (hcount : Nat.card {g : G // g ≠ 1 ∧ g ^ p = 1} =
      (1 + f * p ^ m) * (p ^ m - 1))
    (hhalf : 2 * t = p ^ m - 1) (hq : 3 < p ^ m) :
    Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p m)) := by
  classical
  have hsandwich : p ^ m - 1 ≤ 2 * t := hhalf.ge
  obtain ⟨M, L, j, coord, hMfinite, hMcard, hLcard, hj, hcoord, hnormal, hout⟩ :=
    dicksonWild_exists_matrix_normal_form G hpG P m t hm htp hNcard hsandwich
  let _ : Finite M := hMfinite
  let _ : Fintype M := Fintype.ofFinite M
  let pslEmbed : Matrix.ProjectiveSpecialLinearGroup (Fin 2) M →* PGL p :=
    (Matrix.ProjGenLinGroup.map M.subtype).comp
      Matrix.ProjectiveSpecialLinearGroup.toPGL
  have hpslInjective : Function.Injective pslEmbed :=
    (projGenLinGroup_map_injective M.subtype M.subtype_injective).comp
      Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  let J : Subgroup (PGL p) := j.range
  let H : Subgroup (PGL p) := pslEmbed.range
  have hJfinite : Finite J := Finite.of_surjective j.rangeRestrict
    j.rangeRestrict_surjective
  let _ : Finite J := hJfinite
  have hHfinite : Finite H := Finite.of_surjective pslEmbed.rangeRestrict
    pslEmbed.rangeRestrict_surjective
  let _ : Finite H := hHfinite
  have hle : J ≤ H :=
    dicksonWild_range_le_embedded_psl_of_half G hpG P m f t htp hPcard hNcard
      hindex hcount hhalf M hMcard L hLcard j hj coord hcoord hnormal hout hq
  have hp2 : p ≠ 2 := by
    have hpgt : 2 < p := Fact.out
    omega
  have hqeq : p ^ m = 2 * t + 1 := by omega
  have hquad : (p ^ m) ^ 2 - 1 = 2 * (t * (p ^ m + 1)) := by
    rw [hqeq]
    have hring : (2 * t + 1) ^ 2 = 2 * (t * (2 * t + 1 + 1)) + 1 := by ring
    omega
  have hHcard : Nat.card H = p ^ m * t * (p ^ m + 1) := by
    calc
      Nat.card H = Nat.card
          (Matrix.ProjectiveSpecialLinearGroup (Fin 2) M) :=
        Nat.card_congr (MonoidHom.ofInjective hpslInjective).symm.toEquiv
      _ = Nat.card M * (Nat.card M ^ 2 - 1) / 2 := by
        rw [card_projectiveSpecialLinearGroup_fin_two p M hp2,
          Nat.card_eq_fintype_card]
      _ = p ^ m * ((p ^ m) ^ 2 - 1) / 2 := by rw [hMcard]
      _ = p ^ m * t * (p ^ m + 1) := by
        rw [hquad]
        rw [show p ^ m * (2 * (t * (p ^ m + 1))) =
          2 * (p ^ m * t * (p ^ m + 1)) by ring]
        exact Nat.mul_div_cancel_left _ (by omega)
  have hGcard : Nat.card G = p ^ m * t * (1 + f * p ^ m) := by
    have hprod := (Subgroup.normalizer (P : Set G)).card_mul_index
    rw [hNcard, hindex] at hprod
    exact hprod.symm
  have hJcard : Nat.card J = p ^ m * t * (1 + f * p ^ m) := by
    rw [← hGcard]
    exact (Nat.card_congr (MonoidHom.ofInjective hj).toEquiv).symm
  have hcardLe : Nat.card J ≤ Nat.card H :=
    Nat.card_le_card_of_injective (Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  rw [hJcard, hHcard] at hcardLe
  have hfactorPos : 0 < p ^ m * t := by
    have ht : 0 < t := by
      have hpPow : 3 < p ^ m := hq
      omega
    exact mul_pos (pow_pos (Fact.out : p.Prime).pos m) ht
  have honeLe : 1 + f * p ^ m ≤ p ^ m + 1 := by
    apply Nat.le_of_mul_le_mul_left (c := p ^ m * t)
    · simpa [mul_assoc] using hcardLe
    · exact hfactorPos
  have hfmul : f * p ^ m ≤ 1 * p ^ m := by omega
  have hfle : f ≤ 1 := Nat.le_of_mul_le_mul_right hfmul (pow_pos (Fact.out : p.Prime).pos m)
  have hf1 : f = 1 := by omega
  have hcardEq : Nat.card J = Nat.card H := by
    rw [hJcard, hHcard, hf1]
    ring
  let incl : J →* H := Subgroup.inclusion hle
  have hincl : Function.Bijective incl := by
    let _ : Fintype J := Fintype.ofFinite J
    let _ : Fintype H := Fintype.ofFinite H
    apply (Fintype.bijective_iff_injective_and_card incl).2
    exact ⟨Subgroup.inclusion_injective hle, by
      simpa only [← Nat.card_eq_fintype_card] using hcardEq⟩
  have hge : H ≤ J := by
    intro x hx
    obtain ⟨y, hy⟩ := hincl.2 ⟨x, hx⟩
    have hval : (y.1 : PGL p) = x := congrArg Subtype.val hy
    rw [← hval]
    exact y.2
  have hJH : J = H := le_antisymm hle hge
  let eJ : G ≃* J := MonoidHom.ofInjective hj
  let eH : Matrix.ProjectiveSpecialLinearGroup (Fin 2) M ≃* H :=
    MonoidHom.ofInjective hpslInjective
  let eJH : J ≃* H :=
    MulEquiv.cast (M := fun Q : Subgroup (PGL p) ↦ Q) hJH
  let eJM : G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) M :=
    eJ.trans (eJH.trans eH.symm)
  let _ : Algebra (ZMod p) M := ZMod.algebra M p
  let eField : M ≃ₐ[ZMod p] GaloisField p m :=
    GaloisField.algEquivGaloisField p m hMcard
  exact ⟨eJM.trans
    (dicksonWild_projectiveSpecialLinearGroup_congr eField.toRingEquiv)⟩

private lemma dicksonWild_pgl_case_of_full
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (hpG : p ∣ Nat.card G) (P : Sylow p G)
    (m t : ℕ) (hm : 1 ≤ m) (htp : Nat.Coprime t p)
    (hNcard : Nat.card (Subgroup.normalizer (P : Set G)) = p ^ m * t)
    (hindex : (Subgroup.normalizer (P : Set G)).index = 1 + p ^ m)
    (hfull : t = p ^ m - 1) :
    Nonempty (G ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m)) := by
  classical
  have hsandwich : p ^ m - 1 ≤ 2 * t := by omega
  obtain ⟨M, L, j, coord, hMfinite, hMcard, hLcard, hj, hcoord, hnormal, hout⟩ :=
    dicksonWild_exists_matrix_normal_form G hpG P m t hm htp hNcard hsandwich
  let _ : Finite M := hMfinite
  let _ : Fintype M := Fintype.ofFinite M
  obtain ⟨κ, hle⟩ :=
    dicksonWild_exists_conjugate_range_le_embedded_pgl_of_index_eq
      G P m M hMcard L j coord hindex hcoord hnormal hout
  let j' : G →* PGL p := (MulAut.conj κ).toMonoidHom.comp j
  have hj' : Function.Injective j' := (MulAut.conj κ).injective.comp hj
  let pglEmbed : Matrix.ProjGenLinGroup (Fin 2) M →* PGL p :=
    Matrix.ProjGenLinGroup.map M.subtype
  have hpglInjective : Function.Injective pglEmbed :=
    projGenLinGroup_map_injective M.subtype M.subtype_injective
  let J : Subgroup (PGL p) := j'.range
  let H : Subgroup (PGL p) := pglEmbed.range
  have hJfinite : Finite J := Finite.of_surjective j'.rangeRestrict
    j'.rangeRestrict_surjective
  let _ : Finite J := hJfinite
  let _ : Finite (Matrix.ProjGenLinGroup (Fin 2) M) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  have hHfinite : Finite H := Finite.of_surjective pglEmbed.rangeRestrict
    pglEmbed.rangeRestrict_surjective
  let _ : Finite H := hHfinite
  have hHcard : Nat.card H = p ^ m * ((p ^ m) ^ 2 - 1) := by
    calc
      Nat.card H = Nat.card (Matrix.ProjGenLinGroup (Fin 2) M) :=
        Nat.card_congr (MonoidHom.ofInjective hpglInjective).symm.toEquiv
      _ = Fintype.card M * (Fintype.card M ^ 2 - 1) :=
        card_projGenLinGroup_fin_two M
      _ = p ^ m * ((p ^ m) ^ 2 - 1) := by
        rw [← Nat.card_eq_fintype_card, hMcard]
  have hGcard : Nat.card G = p ^ m * t * (1 + p ^ m) := by
    have hprod := (Subgroup.normalizer (P : Set G)).card_mul_index
    rw [hNcard, hindex] at hprod
    exact hprod.symm
  have hJcard : Nat.card J = p ^ m * t * (1 + p ^ m) := by
    rw [← hGcard]
    exact (Nat.card_congr (MonoidHom.ofInjective hj').toEquiv).symm
  have hqone : 1 ≤ p ^ m := one_le_pow₀ (Fact.out : p.Prime).one_lt.le
  have hfactor : (p ^ m) ^ 2 - 1 = (p ^ m - 1) * (p ^ m + 1) := by
    have hqeq : p ^ m = (p ^ m - 1) + 1 := by omega
    rw [Nat.sub_eq_iff_eq_add (one_le_pow₀ hqone)]
    nlinarith
  have hcardEq : Nat.card J = Nat.card H := by
    rw [hJcard, hHcard, hfull, hfactor]
    ring
  let incl : J → H := Subgroup.inclusion hle
  have hincl : Function.Bijective incl := by
    let _ : Fintype J := Fintype.ofFinite J
    let _ : Fintype H := Fintype.ofFinite H
    apply (Fintype.bijective_iff_injective_and_card incl).2
    exact ⟨Subgroup.inclusion_injective hle, by
      simpa only [← Nat.card_eq_fintype_card] using hcardEq⟩
  have hge : H ≤ J := by
    intro x hx
    obtain ⟨y, hy⟩ := hincl.2 ⟨x, hx⟩
    have hval : (y.1 : PGL p) = x := congrArg Subtype.val hy
    rw [← hval]
    exact y.2
  have hJH : J = H := le_antisymm hle hge
  let eJ : G ≃* J := MonoidHom.ofInjective hj'
  let eH : Matrix.ProjGenLinGroup (Fin 2) M ≃* H :=
    MonoidHom.ofInjective hpglInjective
  let eJH : J ≃* H := MulEquiv.cast (M := fun Q : Subgroup (PGL p) ↦ Q) hJH
  let eJM : G ≃* Matrix.ProjGenLinGroup (Fin 2) M :=
    eJ.trans (eJH.trans eH.symm)
  let _ : Algebra (ZMod p) M := ZMod.algebra M p
  let eField : M ≃ₐ[ZMod p] GaloisField p m :=
    GaloisField.algEquivGaloisField p m hMcard
  exact ⟨eJM.trans (dicksonWild_projGenLinGroup_congr eField.toRingEquiv)⟩

private lemma dicksonWild_psl_case_of_half_eq_three
    {p : ℕ} [Fact p.Prime] [Fact (2 < p)]
    (G : Subgroup (PGL p)) [Finite G] (hpG : p ∣ Nat.card G) (P : Sylow p G)
    (m t : ℕ) (hm : 1 ≤ m) (htp : Nat.Coprime t p)
    (hNcard : Nat.card (Subgroup.normalizer (P : Set G)) = p ^ m * t)
    (hindex : (Subgroup.normalizer (P : Set G)).index = 1 + p ^ m)
    (hhalf : 2 * t = p ^ m - 1) (hq3 : p ^ m = 3) :
    Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2)
      (GaloisField p m)) := by
  classical
  have hsandwich : p ^ m - 1 ≤ 2 * t := hhalf.ge
  obtain ⟨M, L, j, coord, hMfinite, hMcard, hLcard, hj, hcoord, hnormal, hout⟩ :=
    dicksonWild_exists_matrix_normal_form G hpG P m t hm htp hNcard hsandwich
  let _ : Finite M := hMfinite
  let _ : Fintype M := Fintype.ofFinite M
  obtain ⟨κ, hle⟩ :=
    dicksonWild_exists_conjugate_range_le_embedded_pgl_of_index_eq
      G P m M hMcard L j coord hindex hcoord hnormal hout
  let j' : G →* PGL p := (MulAut.conj κ).toMonoidHom.comp j
  have hj' : Function.Injective j' := (MulAut.conj κ).injective.comp hj
  let pglEmbed : Matrix.ProjGenLinGroup (Fin 2) M →* PGL p :=
    Matrix.ProjGenLinGroup.map M.subtype
  have hpglInjective : Function.Injective pglEmbed :=
    projGenLinGroup_map_injective M.subtype M.subtype_injective
  let J : Subgroup (PGL p) := j'.range
  let H : Subgroup (PGL p) := pglEmbed.range
  let eJ : G ≃* J := MonoidHom.ofInjective hj'
  let eH : Matrix.ProjGenLinGroup (Fin 2) M ≃* H :=
    MonoidHom.ofInjective hpglInjective
  let incl : J →* H := Subgroup.inclusion hle
  let toPGL : J →* Matrix.ProjGenLinGroup (Fin 2) M :=
    eH.symm.toMonoidHom.comp incl
  have htoPGL : Function.Injective toPGL :=
    eH.symm.injective.comp (Subgroup.inclusion_injective hle)
  have ht1 : t = 1 := by omega
  have hGcard : Nat.card G = 12 := by
    have hprod := (Subgroup.normalizer (P : Set G)).card_mul_index
    rw [hNcard, hindex, hq3, ht1] at hprod
    norm_num at hprod ⊢
    exact hprod.symm
  have hJfinite : Finite J := Finite.of_surjective eJ eJ.surjective
  let _ : Finite J := hJfinite
  have hJcard : Nat.card J = 12 := by
    rw [← hGcard]
    exact (Nat.card_congr eJ.toEquiv).symm
  let X := Projectivization M (Fin 2 → M)
  let _ : Fintype X := Fintype.ofEquiv (OnePoint M)
    (OnePoint.equivProjectivization M)
  have hMcard3 : Nat.card M = 3 := hMcard.trans hq3
  have hOneCard : Fintype.card (OnePoint M) = 4 := by
    change Fintype.card (Option M) = 4
    rw [Fintype.card_option, ← Nat.card_eq_fintype_card, hMcard3]
  have hXcard : Fintype.card X = 4 := by
    calc
      Fintype.card X = Fintype.card (OnePoint M) :=
        (Fintype.card_congr (OnePoint.equivProjectivization M)).symm
      _ = 4 := hOneCard
  let eFin : X ≃ Fin 4 := (Fintype.equivFin X).trans (finCongr hXcard)
  let pglAct : Matrix.ProjGenLinGroup (Fin 2) M →* Equiv.Perm (Fin 4) :=
    eFin.permCongrHom.toMonoidHom.comp
      (MulAction.toPermHom (Matrix.ProjGenLinGroup (Fin 2) M) X)
  have hpglAct : Function.Injective pglAct := eFin.permCongrHom.injective.comp
    dicksonWild_pgl_toPermHom_injective
  let act : J →* Equiv.Perm (Fin 4) := pglAct.comp toPGL
  have hact : Function.Injective act := hpglAct.comp htoPGL
  have hPermCard : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    norm_num [Nat.factorial]
  have hactIndex : act.range.index = 2 :=
    dicksonWild_perm_range_index_eq_two_of_card act hact 12 hJcard (by omega)
  obtain ⟨eJAlt⟩ :=
    dicksonWild_mulEquiv_alternating_of_perm_index_two act hact hactIndex
  have hp2 : p ≠ 2 := by
    have hpgt : 2 < p := Fact.out
    omega
  obtain ⟨ePSLAlt⟩ :=
    dicksonWild_psl_card_three_equiv_alternating_four p M hp2 hMcard3
  let eJM : G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) M :=
    eJ.trans (eJAlt.trans ePSLAlt.symm)
  let _ : Algebra (ZMod p) M := ZMod.algebra M p
  let eField : M ≃ₐ[ZMod p] GaloisField p m :=
    GaloisField.algEquivGaloisField p m hMcard
  exact ⟨eJM.trans
    (dicksonWild_projectiveSpecialLinearGroup_congr eField.toRingEquiv)⟩

/-- **Dickson's classification**, wild case: a finite subgroup of `PGL₂` over
an algebraic closure of `𝔽_p` (odd `p`), of order divisible by `p`, is a
Frobenius group with a faithful action that fixes no nonzero vector, `PSL₂` or
`PGL₂` over a finite subfield, or (for `p = 3`) `A₅`. The first alternative
records the group-theoretic consequences of the scalar-root action rather than
constructing the scalar embedding itself.

Source: L. E. Dickson, *Linear Groups with an Exposition of the Galois Field
Theory*, Teubner (1901).

Proves `Wanted` entry `classification_wild`.

Proof: We follow X. Faber, *Finite p-irregular subgroups of PGL₂(k)*,
arXiv:1112.1999, §6, using the Sylow normal form, exceptional-orbit count, and projective-line
actions to identify the `PSL₂`, `PGL₂`, and `A₅` cases.
-/
theorem classification_wild (G : Subgroup (PGL p)) [Finite G]
    (hG_p : p ∣ Nat.card G) :
    (∃ (m t : ℕ) (_ : m ≥ 1) (_ : Nat.Coprime t p) (_ : t ∣ p ^ m - 1)
      (φ : Multiplicative (ZMod t) →* MulAut (Multiplicative (Fin m → ZMod p)))
      (_hφ_injective : Function.Injective φ)
      (_hφ_fixed_point_free : ∀ c ≠ 1, ∀ v ≠ 1, φ c v ≠ v),
      Nonempty (G ≃* (Multiplicative (Fin m → ZMod p)) ⋊[φ] Multiplicative (ZMod t))) ∨
    (∃ m : ℕ, m ≥ 1 ∧
      Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p m))) ∨
    (∃ m : ℕ, m ≥ 1 ∧
      Nonempty (G ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p m))) ∨
    (p = 3 ∧ Nonempty (G ≃* alternatingGroup (Fin 5))) := by
  let P : Sylow p G := Classical.choice inferInstance
  by_cases hPnormal : (P : Subgroup G).Normal
  · exact Or.inl (dicksonWild_frobenius_case_of_normal_sylow G hG_p P hPnormal)
  · obtain ⟨m, f, hm, hPcard, hf, hSylowCard, hpCount⟩ :=
      dicksonWild_order_char_count G hG_p P hPnormal
    obtain ⟨mN, t, hmN, htp, htdiv, hPcardN, hNcard⟩ :=
      dicksonWild_normalizer_order_data G hG_p P
    have hmEq : mN = m := by
      apply (Nat.pow_right_inj (Fact.out : p.Prime).one_lt).mp
      exact hPcardN.symm.trans hPcard
    subst mN
    have hindex : (Subgroup.normalizer (P : Set G)).index = 1 + f * p ^ m :=
      (P.card_eq_index_normalizer.symm.trans hSylowCard)
    have hsandwich : p ^ m - 1 ≤ 2 * t :=
      dicksonWild_sandwich_bound G hG_p P m f t hf htp hPcard hNcard
        hindex hpCount
    have hqpos : 0 < p ^ m - 1 := by
      have hpPow : 1 < p ^ m := one_lt_pow₀ (Fact.out : p.Prime).one_lt (by omega)
      omega
    have htpos : 0 < t := by
      by_contra ht
      have ht0 : t = 0 := Nat.eq_zero_of_not_pos ht
      rw [ht0, mul_zero] at hNcard
      exact Nat.card_pos.ne' hNcard
    have htCases : t = p ^ m - 1 ∨ 2 * t = p ^ m - 1 :=
      dicksonWild_eq_or_two_mul_eq_of_dvd_of_le (p ^ m - 1) t hqpos htpos
        htdiv hsandwich
    obtain ⟨M, L, j, coord, hMfinite, hMcard, hLcard, hj, hcoord, hnormal, hout⟩ :=
      dicksonWild_exists_matrix_normal_form G hG_p P m t hm htp hNcard hsandwich
    let _ : Finite M := hMfinite
    obtain ⟨d, hd, hrelation, hstabilizerLarge, hstabilizerSmall,
      hstabilizers, hexceptionalOrbits⟩ :=
      dicksonWild_exceptional_orbit_data G P m f t hm hf hNcard hindex hpCount
        M L j hj coord hnormal hout
    have hp3 : 3 ≤ p := by
      have hpgt : 2 < p := Fact.out
      omega
    have hq3 : 3 ≤ p ^ m :=
      hp3.trans (Nat.le_pow (a := p) (b := m) hm)
    rcases htCases with hfull | hhalf
    · rcases dicksonWild_f_eq_one_or_exceptional_of_full_multiplier_relation
          (p ^ m) f t d hq3 hf hfull hrelation with hf1 | hexceptional
      · subst f
        have hindex1 : (Subgroup.normalizer (P : Set G)).index = 1 + p ^ m := by
          simpa using hindex
        exact Or.inr (Or.inr (Or.inl ⟨m, hm,
          dicksonWild_pgl_case_of_full G hG_p P m t hm htp hNcard hindex1 hfull⟩))
      · obtain ⟨hqEq, hfEq⟩ := hexceptional
        subst f
        let _ : MulAction G (Projectivization (K p) (Fin 2 → K p)) :=
          MulAction.compHom _ j
        have hpEq : p = 3 := by
          have hpLe : p ≤ p ^ m := Nat.le_pow hm
          omega
        have hdEq : d = 5 := by
          rw [hfull, hqEq] at hrelation
          norm_num at hrelation
          omega
        have hqt : p ^ m * t = 6 := by rw [hfull, hqEq]
        obtain ⟨x₆, hx₆⟩ := hstabilizerLarge
        obtain ⟨x₅, hx₅⟩ := hstabilizerSmall
        have hx₆' : Nat.card (MulAction.stabilizer G x₆) = 6 := hx₆.trans hqt
        have hx₅' : Nat.card (MulAction.stabilizer G x₅) = 5 := hx₅.trans hdEq
        have hall :
            ∀ x : dicksonWildExceptional G
                (Projectivization (K p) (Fin 2 → K p)),
              Nat.card (MulAction.stabilizer G x) = 6 ∨
              Nat.card (MulAction.stabilizer G x) = 5 := by
          intro x
          rcases hstabilizers x with h | h
          · exact Or.inl (h.trans hqt)
          · exact Or.inr (h.trans hdEq)
        have hGcard : Nat.card G = 60 := by
          have hprod := (Subgroup.normalizer (P : Set G)).card_mul_index
          rw [hNcard, hindex, hfull, hqEq] at hprod
          norm_num at hprod ⊢
          omega
        have hPcardThree : Nat.card (P : Subgroup G) = 3 := hPcard.trans hqEq
        exact Or.inr (Or.inr (Or.inr ⟨hpEq,
          dicksonWild_a5_case_of_exceptional G hpEq P hPnormal hPcardThree
            j hj hGcard x₆ x₅ hx₆' hx₅' hall hexceptionalOrbits⟩))
    · have hf1 := dicksonWild_f_eq_one_of_half_multiplier_relation
          (p ^ m) f t d hq3 hf hhalf hrelation
      subst f
      have hindex1 : (Subgroup.normalizer (P : Set G)).index = 1 + p ^ m := by
        simpa using hindex
      by_cases hqgt : 3 < p ^ m
      · exact Or.inr (Or.inl ⟨m, hm,
          dicksonWild_psl_case_of_half_gt_three G hG_p P m 1 t hm (by omega)
            htp hPcard hNcard (by simpa using hindex1) (by simpa using hpCount) hhalf hqgt⟩)
      · have hqEq : p ^ m = 3 := by omega
        exact Or.inr (Or.inl ⟨m, hm,
          dicksonWild_psl_case_of_half_eq_three G hG_p P m t hm htp hNcard
            hindex1 hhalf hqEq⟩)

end Dickson

end MetaMathlibExt
