import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped TensorProduct


attribute [local instance] Algebra.TensorProduct.rightAlgebra


private noncomputable def alphaR
  {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R'] [CommRing S'] [Algebra R S] [Algebra R R'] [Algebra S S'] [Algebra R' S'] [Algebra R S'] [IsScalarTower R S S'] [IsScalarTower R R' S'] :
  S ⊗[R] R' →ₐ[R] S' :=
  Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R S S') (IsScalarTower.toAlgHom R R' S')
    (fun _ _ => Commute.all _ _)

private lemma alphaR_tmul
  {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R'] [CommRing S'] [Algebra R S] [Algebra R R'] [Algebra S S'] [Algebra R' S'] [Algebra R S'] [IsScalarTower R S S'] [IsScalarTower R R' S']
  (s : S) (r : R') :
-- imply
  (alphaR : S ⊗[R] R' →ₐ[R] S') (s ⊗ₜ r) = algebraMap S S' s * algebraMap R' S' r := by
-- proof
  simp [alphaR, Algebra.TensorProduct.lift_tmul]

private lemma algebraMap_right_apply
  {R S R' : Type u} [CommRing R] [CommRing S] [CommRing R'] [Algebra R S] [Algebra R R']
  (r : R') :
-- imply
  algebraMap R' (S ⊗[R] R') r = (1 : S) ⊗ₜ[R] r :=
  rfl

private noncomputable def alpha
  {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R'] [CommRing S'] [Algebra R S] [Algebra R R'] [Algebra S S'] [Algebra R' S'] [Algebra R S'] [IsScalarTower R S S'] [IsScalarTower R R' S'] :
  S ⊗[R] R' →ₐ[R'] S' :=
  AlgHom.mk (alphaR : S ⊗[R] R' →ₐ[R] S').toRingHom (fun r => by
    change (alphaR : S ⊗[R] R' →ₐ[R] S').toRingHom (algebraMap R' (S ⊗[R] R') r) = _
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, algebraMap_right_apply, alphaR_tmul, map_one,
      one_mul])

private lemma alpha_apply
  {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R'] [CommRing S'] [Algebra R S] [Algebra R R'] [Algebra S S'] [Algebra R' S'] [Algebra R S'] [IsScalarTower R S S'] [IsScalarTower R R' S']
  (x : S ⊗[R] R') :
-- imply
  (alpha : S ⊗[R] R' →ₐ[R'] S') x = (alphaR : S ⊗[R] R' →ₐ[R] S') x :=
  rfl

private lemma alpha_tmul
  {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R'] [CommRing S'] [Algebra R S] [Algebra R R'] [Algebra S S'] [Algebra R' S'] [Algebra R S'] [IsScalarTower R S S'] [IsScalarTower R R' S']
  (s : S) (r : R') :
-- imply
  (alpha : S ⊗[R] R' →ₐ[R'] S') (s ⊗ₜ r) = algebraMap S S' s * algebraMap R' S' r := by
-- proof
  rw [alpha_apply, alphaR_tmul]

private lemma alpha_comp_algebraMap
  {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R'] [CommRing S'] [Algebra R S] [Algebra R R'] [Algebra S S'] [Algebra R' S'] [Algebra R S'] [IsScalarTower R S S'] [IsScalarTower R R' S'] :
-- imply
  (alpha : S ⊗[R] R' →ₐ[R'] S').toRingHom.comp (algebraMap S (S ⊗[R] R')) = algebraMap S S' := by
-- proof
  ext s
  change (alpha : S ⊗[R] R' →ₐ[R'] S') (algebraMap S (S ⊗[R] R') s) = _
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    alpha_tmul, map_one, mul_one]

private lemma includeLeft_compat
  {R S R' : Type u} [CommRing R] [CommRing S] [CommRing R'] [Algebra R S] [Algebra R R'] :
-- imply
  (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] R').comp (algebraMap R S) =
    (algebraMap R' (S ⊗[R] R')).comp (algebraMap R R') := by
-- proof
  ext r
  simp only [RingHom.coe_comp, Function.comp_apply,
    Algebra.TensorProduct.includeLeftRingHom_apply, algebraMap_right_apply]
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]


/--
[Algebra_isPushout_of_forall_existsUnique_algHom_comp_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_isPushout_of_forall_existsUnique_algHom_comp_eq.lean)
-/
@[path]
private lemma main
  {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R'] [CommRing S'] [Algebra R S] [Algebra R R'] [Algebra S S'] [Algebra R' S'] [Algebra R S'] [IsScalarTower R S S'] [IsScalarTower R R' S']
-- given
  (h : ∀ (T : Type u) [CommRing T] [Algebra R' T] (g : S →+* T),
    g.comp (algebraMap R S) = (algebraMap R' T).comp (algebraMap R R') →
      ∃! k : S' →ₐ[R'] T, k.toRingHom.comp (algebraMap S S') = g) :
-- imply
  Algebra.IsPushout R S R' S' := by
-- proof
  classical
  obtain ⟨β, hβ, -⟩ := h (S ⊗[R] R') Algebra.TensorProduct.includeLeftRingHom includeLeft_compat
  have hcompat : (algebraMap S S').comp (algebraMap R S) =
      (algebraMap R' S').comp (algebraMap R R') := by
    rw [← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
  have hαβ : (alpha : S ⊗[R] R' →ₐ[R'] S').comp β = AlgHom.id R' S' := by
    refine (h S' (algebraMap S S') hcompat).unique ?_ ?_
    ·
      change ((alpha : S ⊗[R] R' →ₐ[R'] S').toRingHom.comp β.toRingHom).comp (algebraMap S S') = _
      rw [RingHom.comp_assoc, hβ]
      ext s
      change (alpha : S ⊗[R] R' →ₐ[R'] S') (s ⊗ₜ 1) = _
      rw [alpha_tmul, map_one, mul_one]
    · rfl
  have hβα : ∀ x : S ⊗[R] R', β ((alpha : S ⊗[R] R' →ₐ[R'] S') x) = x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul s r =>
      rw [alpha_tmul, map_mul, AlgHom.commutes, algebraMap_right_apply]
      have hs : β (algebraMap S S' s) = s ⊗ₜ 1 := by
        have := congrArg (fun φ : S →+* S ⊗[R] R' => φ s) hβ
        simpa using this
      rw [hs, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add x y hx hy =>
      rw [map_add, map_add, hx, hy]
  let e : (S ⊗[R] R') ≃ₐ[R'] S' :=
    AlgEquiv.ofAlgHom (alpha : S ⊗[R] R' →ₐ[R'] S') β hαβ (by ext x; apply hβα x)
  have he : e.toRingHom.comp (algebraMap S (S ⊗[R] R')) = algebraMap S S' :=
    alpha_comp_algebraMap
  have : Algebra.IsPushout R R' S S' :=
    Algebra.IsPushout.of_equiv (h := TensorProduct.isPushout') e he
  exact this.symm


-- created on 2026-10-13
