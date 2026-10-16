import Mathlib
import sympy.Basic
open scoped TensorProduct


@[reducible] private def dualModule (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] :
  Module B (Module.Dual A B) where
  smul b φ := φ.comp (LinearMap.mulLeft A b)
  one_smul φ := by
    refine LinearMap.ext fun y => ?_
    change φ (1 * y) = φ y
    rw [one_mul]
  mul_smul b c φ := by
    refine LinearMap.ext fun y => ?_
    change φ (b * c * y) = φ (c * (b * y))
    congr 1
    ring
  smul_zero b := by
    refine LinearMap.ext fun y => ?_
    change (0 : Module.Dual A B) (b * y) = 0
    rfl
  smul_add b φ ψ := by
    refine LinearMap.ext fun y => ?_
    change (φ + ψ) (b * y) = φ (b * y) + ψ (b * y)
    rfl
  add_smul b c φ := by
    refine LinearMap.ext fun y => ?_
    change φ ((b + c) * y) = φ (b * y) + φ (c * y)
    rw [add_mul, map_add]
  zero_smul φ := by
    refine LinearMap.ext fun y => ?_
    change φ (0 * y) = 0
    rw [zero_mul, map_zero]

attribute [local instance] dualModule

private lemma smul_dual_apply
  [CommRing A] [CommRing B] [Algebra A B]
  (b : B) (φ : Module.Dual A B) (y : B) :
-- imply
  (b • φ) y = φ (b * y) :=
  rfl

private instance [CommRing A] [CommRing B] [Algebra A B] :
  IsScalarTower A B (Module.Dual A B) where
  smul_assoc a b φ := by
    refine LinearMap.ext fun y => ?_
    rw [smul_dual_apply, LinearMap.smul_apply, smul_dual_apply, smul_mul_assoc, map_smul]

private noncomputable def theta (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] :
  B →ₗ[B] Module.Dual A B where
  toFun x := Algebra.traceForm A B x
  map_add' := by
    intro x y
    rw [map_add]
  map_smul' := by
    intro b x
    refine LinearMap.ext fun y => ?_
    rw [RingHom.id_apply, smul_dual_apply, Algebra.traceForm_apply, Algebra.traceForm_apply, smul_eq_mul]
    congr 1
    ring

private lemma theta_apply
  [CommRing A] [CommRing B] [Algebra A B]
  (x y : B) :
-- imply
  theta A B x y = Algebra.trace A B (x * y) :=
  rfl

private abbrev Coker (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] :=
  Module.Dual A B ⧸ LinearMap.range (theta A B)

private instance [CommRing A] [CommRing B] [Algebra A B] [Module.Free A B] [Module.Finite A B] : Module.Finite B (Module.Dual A B) := Module.Finite.of_restrictScalars_finite A B (Module.Dual A B)

private lemma cond_iff_not_annihilator_le
  [CommRing A] [CommRing B] [Algebra A B]
  (P : Ideal B) :
-- imply
  (∃ s ∉ P, ∀ φ : Module.Dual A B, ∃ x : B, ∀ y : B, φ (s * y) = Algebra.trace A B (x * y)) ↔
    ¬ Module.annihilator B (Coker A B) ≤ P := by
-- proof
  rw [SetLike.not_le_iff_exists]
  refine exists_congr fun s => ?_
  rw [and_comm (a := s ∈ Module.annihilator B (Coker A B))]
  refine and_congr_right fun _ => ?_
  rw [Module.mem_annihilator]
  constructor
  ·
    intro h n
    obtain ⟨φ, rfl⟩ := Submodule.Quotient.mk_surjective _ n
    obtain ⟨x, hx⟩ := h φ
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    refine ⟨x, LinearMap.ext fun y => ?_⟩
    rw [theta_apply, smul_dual_apply, hx]
  ·
    intro h φ
    have := h (Submodule.Quotient.mk φ)
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at this
    obtain ⟨x, hx⟩ := this
    refine ⟨x, fun y => ?_⟩
    rw [← theta_apply, hx, smul_dual_apply]

private lemma cond_iff_subsingleton
  [CommRing A] [CommRing B] [Algebra A B]
  [Module.Free A B] [Module.Finite A B]
  (P : Ideal B) [P.IsPrime] :
-- imply
  (∃ s ∉ P, ∀ φ : Module.Dual A B, ∃ x : B, ∀ y : B, φ (s * y) = Algebra.trace A B (x * y)) ↔
    Subsingleton (P.ResidueField ⊗[B] Coker A B) := by
-- proof
  rw [cond_iff_not_annihilator_le, ← not_nontrivial_iff_subsingleton,
    ← Module.mem_support_iff_nontrivial_residueField_tensorProduct (p := ⟨P, inferInstance⟩),
    Module.mem_support_iff_of_finite]

attribute [local instance] dualModule Algebra.TensorProduct.rightAlgebra

@[instance_reducible] private noncomputable def dualTModuleB
  (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
  (κ : Type*) [CommRing κ] [Algebra A κ] :
    Module B (Module.Dual κ (κ ⊗[A] B)) :=
  Module.compHom (Module.Dual κ (κ ⊗[A] B)) (algebraMap B (κ ⊗[A] B))

attribute [local instance] dualTModuleB

private instance [CommRing A] [CommRing B] [Algebra A B] [CommRing κ] [Algebra A κ] : IsScalarTower B (κ ⊗[A] B) (Module.Dual κ (κ ⊗[A] B)) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl

private lemma smul_dualT_B
  [CommRing A] [CommRing B] [Algebra A B]
  [CommRing κ] [Algebra A κ]
  (b : B) (ψ : Module.Dual κ (κ ⊗[A] B)) :
-- imply
  b • ψ = (algebraMap B (κ ⊗[A] B) b) • ψ :=
  rfl

private lemma ibcB
  (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
  (κ : Type*) [CommRing κ] [Algebra A κ] :
-- imply
  IsBaseChange κ (TensorProduct.mk A κ B 1) :=
  TensorProduct.isBaseChange A B κ

private noncomputable def beta
  (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
  (κ : Type*) [CommRing κ] [Algebra A κ] :
    Module.Dual A B →ₗ[B] Module.Dual κ (κ ⊗[A] B) where
  toFun f := (ibcB A B κ).toDual f
  map_add' := by
    intro f g
    rw [map_add]
  map_smul' := by
    intro b f
    refine (ibcB A B κ).algHom_ext _ _ fun v => ?_
    rw [RingHom.id_apply, IsBaseChange.toDual_comp_apply, smul_dual_apply, smul_dualT_B, smul_dual_apply]
    change _ = (ibcB A B κ).toDual f ((1 ⊗ₜ[A] b) * (1 ⊗ₜ[A] v))
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    apply ((ibcB A B κ).toDual_comp_apply f (b * v)).symm

private lemma beta_apply
  [CommRing A] [CommRing B] [Algebra A B]
  [CommRing κ] [Algebra A κ]
  (f : Module.Dual A B) :
-- imply
  beta A B κ f = (ibcB A B κ).toDual f :=
  rfl

private noncomputable def Phi
  (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B] [Module.Free A B]
  (κ : Type*) [CommRing κ] [Algebra A κ] :
    (κ ⊗[A] B) ⊗[B] Module.Dual A B →ₗ[κ ⊗[A] B] Module.Dual κ (κ ⊗[A] B) :=
  (TensorProduct.isBaseChange B (Module.Dual A B) (κ ⊗[A] B)).lift (beta A B κ)

private lemma Phi_tmul
  [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B] [Module.Free A B]
  [CommRing κ] [Algebra A κ]
  (t : κ ⊗[A] B) (f : Module.Dual A B) :
-- imply
  Phi A B κ (t ⊗ₜ[B] f) = t • beta A B κ f := by
-- proof
  have h : Phi A B κ ((TensorProduct.mk B (κ ⊗[A] B) (Module.Dual A B) 1) f) = beta A B κ f :=
    (TensorProduct.isBaseChange B (Module.Dual A B) (κ ⊗[A] B)).lift_eq (beta A B κ) f
  rw [TensorProduct.mk_apply] at h
  rw [show t ⊗ₜ[B] f = t • ((1 : κ ⊗[A] B) ⊗ₜ[B] f) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
    map_smul, h]

private lemma Phi_bijective
  [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B] [Module.Free A B]
  [CommRing κ] [Algebra A κ] :
-- imply
  Function.Bijective (Phi A B κ) := by
-- proof
  let G : (κ ⊗[A] B) ⊗[B] Module.Dual A B ≃ₗ[κ] κ ⊗[A] Module.Dual A B :=
    Algebra.IsPushout.cancelBaseChange A κ B (κ ⊗[A] B) (Module.Dual A B)
  let E : κ ⊗[A] Module.Dual A B ≃ₗ[κ] Module.Dual κ (κ ⊗[A] B) := (ibcB A B κ).dual.equiv
  have key : ∀ z, Phi A B κ z = E (G z) := by
    intro z
    obtain ⟨w, rfl⟩ := G.symm.surjective z
    rw [LinearEquiv.apply_symm_apply]
    refine TensorProduct.inductionOn
      (motive := fun w => Phi A B κ (G.symm w) = E w) w ?_ ?_
    ·
      intro s f
      rw [Algebra.IsPushout.cancelBaseChange_symm_tmul, Phi_tmul, IsBaseChange.equiv_tmul, beta_apply]
      refine LinearMap.ext fun t => ?_
      rw [smul_dual_apply, LinearMap.smul_apply, ← Algebra.smul_def, map_smul]
    ·
      intro x y hx hy
      rw [G.symm.map_add, (Phi A B κ).map_add, E.map_add, hx, hy]
  have : (Phi A B κ : (κ ⊗[A] B) ⊗[B] Module.Dual A B → Module.Dual κ (κ ⊗[A] B)) = E ∘ G :=
    funext key
  rw [this]
  apply E.bijective.comp G.bijective

private noncomputable def PhiEquiv
  (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B] [Module.Free A B]
  (κ : Type*) [CommRing κ] [Algebra A κ] :
    (κ ⊗[A] B) ⊗[B] Module.Dual A B ≃ₗ[κ ⊗[A] B] Module.Dual κ (κ ⊗[A] B) :=
  LinearEquiv.ofBijective (Phi A B κ) (Phi_bijective (A := A) (B := B) (κ := κ))

private lemma trace_one_tmul
  [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B] [Module.Free A B]
  [CommRing κ] [Algebra A κ]
  (z : B) :
-- imply
  Algebra.trace κ (κ ⊗[A] B) ((1 : κ) ⊗ₜ[A] z) = algebraMap A κ (Algebra.trace A B z) := by
-- proof
  rw [Algebra.trace_apply, Algebra.trace_apply, ← LinearMap.trace_baseChange]
  congr 1
  refine TensorProduct.AlgebraTensorModule.ext fun a b => ?_
  rw [LinearMap.baseChange_tmul]
  change ((1 : κ) ⊗ₜ[A] z) * (a ⊗ₜ[A] b) = a ⊗ₜ[A] (Algebra.lmul A B z) b
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rfl

private lemma beta_theta
  [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B] [Module.Free A B]
  [CommRing κ] [Algebra A κ]
  (x : B) :
-- imply
  beta A B κ (theta A B x) = theta κ (κ ⊗[A] B) ((1 : κ) ⊗ₜ[A] x) := by
-- proof
  refine (ibcB A B κ).algHom_ext _ _ fun v => ?_
  rw [beta_apply, IsBaseChange.toDual_comp_apply, TensorProduct.mk_apply, theta_apply, theta_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, trace_one_tmul]

private noncomputable abbrev Q1
  (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B] [Module.Free A B]
  (κ : Type*) [CommRing κ] [Algebra A κ] :
    Submodule (κ ⊗[A] B) ((κ ⊗[A] B) ⊗[B] Module.Dual A B) :=
  LinearMap.range (TensorProduct.AlgebraTensorModule.lTensor (κ ⊗[A] B) (κ ⊗[A] B)
    ((LinearMap.range (theta A B)).subtype.restrictScalars B))

private lemma map_Q1
  [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B] [Module.Free A B]
  [CommRing κ] [Algebra A κ] :
-- imply
  (Q1 A B κ).map (PhiEquiv A B κ).toLinearMap = LinearMap.range (theta κ (κ ⊗[A] B)) := by
-- proof
  refine le_antisymm ?_ ?_
  ·
    rw [Submodule.map_le_iff_le_comap, LinearMap.range_le_iff_comap, Submodule.eq_top_iff']
    intro w
    rw [Submodule.mem_comap, Submodule.mem_comap]
    refine TensorProduct.inductionOn
      (motive := fun w => (PhiEquiv A B κ).toLinearMap
        (TensorProduct.AlgebraTensorModule.lTensor (κ ⊗[A] B) (κ ⊗[A] B)
          ((LinearMap.range (theta A B)).subtype.restrictScalars B) w) ∈
        LinearMap.range (theta κ (κ ⊗[A] B))) w ?_ ?_
    ·
      intro t d
      obtain ⟨_, ⟨x, rfl⟩⟩ := d
      rw [TensorProduct.AlgebraTensorModule.lTensor_tmul]
      change PhiEquiv A B κ (t ⊗ₜ[B] theta A B x) ∈ LinearMap.range (theta κ (κ ⊗[A] B))
      rw [show (PhiEquiv A B κ) (t ⊗ₜ[B] theta A B x) = Phi A B κ (t ⊗ₜ[B] theta A B x) from rfl,
        Phi_tmul, beta_theta, ← map_smul]
      refine ⟨_, rfl⟩
    ·
      intro x y hx hy
      rw [map_add, map_add]
      apply Submodule.add_mem _ hx hy
  ·
    intro _ h
    obtain ⟨t, rfl⟩ := h
    refine ⟨t ⊗ₜ[B] theta A B 1, ?_, ?_⟩
    ·
      refine ⟨t ⊗ₜ[B] ⟨theta A B 1, ⟨1, rfl⟩⟩, ?_⟩
      rw [TensorProduct.AlgebraTensorModule.lTensor_tmul]
      rfl
    ·
      change Phi A B κ (t ⊗ₜ[B] theta A B 1) = theta κ (κ ⊗[A] B) t
      rw [Phi_tmul, beta_theta, ← Algebra.TensorProduct.one_def, ← map_smul, smul_eq_mul, mul_one]

private noncomputable def PhiN
  (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B] [Module.Free A B]
  (κ : Type*) [CommRing κ] [Algebra A κ] :
    (κ ⊗[A] B) ⊗[B] Coker A B ≃ₗ[κ ⊗[A] B] Coker κ (κ ⊗[A] B) :=
  (TensorProduct.AlgebraTensorModule.tensorQuotientEquiv (κ ⊗[A] B) B (κ ⊗[A] B)
      (LinearMap.range (theta A B))).trans
    (Submodule.Quotient.equiv (Q1 A B κ) (LinearMap.range (theta κ (κ ⊗[A] B))) (PhiEquiv A B κ)
      (map_Q1 (A := A) (B := B) (κ := κ)))


/--
[Algebra_exists_notMem_forall_dual_eq_trace_iff_fiber](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_exists_notMem_forall_dual_eq_trace_iff_fiber.lean)
-/
@[path]
private lemma main
  [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B] [Module.Free A B]
  {p : Ideal A} [p.IsPrime]
  {P : Ideal B} [P.IsPrime] [P.LiesOver p]
  {P' : Ideal (p.Fiber B)} [P'.IsPrime]
-- given
  (hP' : P = P'.comap Algebra.TensorProduct.includeRight.toRingHom) :
-- imply
  (∃ s ∉ P, ∀ φ : Module.Dual A B, ∃ x : B, ∀ y : B, φ (s * y) = Algebra.trace A B (x * y)) ↔
    (∃ s ∉ P', ∀ φ : Module.Dual p.ResidueField (p.Fiber B), ∃ x : p.Fiber B, ∀ y : p.Fiber B,
      φ (s * y) = Algebra.trace p.ResidueField (p.Fiber B) (x * y)) := by
-- proof
  rw [cond_iff_subsingleton (P := P), cond_iff_subsingleton (A := p.ResidueField) (B := p.Fiber B) (P := P')]
  let g : P.ResidueField →ₐ[B] P'.ResidueField :=
    Ideal.ResidueField.mapₐ P P' (Algebra.ofId B (p.Fiber B)) hP'
  let _ : Algebra P.ResidueField P'.ResidueField := g.toRingHom.toAlgebra
  let _ : IsScalarTower B P.ResidueField P'.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun b => (g.commutes b).symm
  let e1 : P'.ResidueField ⊗[p.Fiber B] Coker p.ResidueField (p.Fiber B) ≃ₗ[P'.ResidueField]
    P'.ResidueField ⊗[p.Fiber B] ((p.Fiber B) ⊗[B] Coker A B) :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl P'.ResidueField P'.ResidueField)
      (PhiN A B p.ResidueField).symm
  let e2 : P'.ResidueField ⊗[p.Fiber B] ((p.Fiber B) ⊗[B] Coker A B) ≃ₗ[P'.ResidueField]
    P'.ResidueField ⊗[B] Coker A B :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange B (p.Fiber B) P'.ResidueField
      P'.ResidueField (Coker A B)
  let e3 : P'.ResidueField ⊗[B] Coker A B ≃ₗ[P'.ResidueField]
    P'.ResidueField ⊗[P.ResidueField] (P.ResidueField ⊗[B] Coker A B) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange B P.ResidueField P'.ResidueField
      P'.ResidueField (Coker A B)).symm
  rw [((e1.trans e2).trans e3).toEquiv.subsingleton_congr,
    Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right P.ResidueField P'.ResidueField]


-- created on 2026-10-13
