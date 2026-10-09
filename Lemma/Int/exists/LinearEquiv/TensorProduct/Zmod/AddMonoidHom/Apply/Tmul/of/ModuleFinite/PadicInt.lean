import Mathlib
import sympy.Basic

open scoped TensorProduct

/--
[AddMonoidHom_exists_linearEquiv_tensorProduct_zmod_addMonoidHom_apply_tmul_of_moduleFinite_padicInt](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AddMonoidHom_exists_linearEquiv_tensorProduct_zmod_addMonoidHom_apply_tmul_of_moduleFinite_padicInt.lean)
-/

noncomputable def pSub
  (p : ℕ)
  [Fact p.Prime]
  (P : Type*)
  [AddCommGroup P]
  [Module ℤ_[p] P]
  : AddSubgroup P := (LinearMap.range (DistribSMul.toLinearMap ℤ_[p] P (p : ℤ_[p]))).toAddSubgroup

abbrev V
  (p : ℕ)
  [Fact p.Prime]
  (P : Type*)
  [AddCommGroup P]
  [Module ℤ_[p] P]
  : Type _ := P ⧸ pSub p P

private lemma nsmul_mem_pSub
  (p : ℕ)
  [Fact p.Prime]
  (P : Type*)
  [AddCommGroup P]
  [Module ℤ_[p] P]
  (x : P) : p • x ∈ pSub p P := by
  refine ⟨x, ?_⟩
  change (p : ℤ_[p]) • x = p • x
  exact Nat.cast_smul_eq_nsmul ℤ_[p] p x

noncomputable instance moduleV
  (p : ℕ)
  [Fact p.Prime]
  (P : Type*)
  [AddCommGroup P]
  [Module ℤ_[p] P]
  : Module (ZMod p) (V p P) := QuotientAddGroup.zmodModule (nsmul_mem_pSub p P)

private lemma apply_eq_zero_of_mem_pSub
  (p : ℕ)
  [Fact p.Prime]
  (P : Type*)
  [AddCommGroup P]
  [Module ℤ_[p] P]
  (W : Type*)
  [AddCommGroup W]
  [Module (ZMod p) W]
  (φ : P →+ W) (x : P) (hx : x ∈ pSub p P) : φ x = 0 := by
  obtain ⟨y, rfl⟩ := hx
  change φ ((p : ℤ_[p]) • y) = 0
  rw [Nat.cast_smul_eq_nsmul, map_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_self, zero_smul]

noncomputable def liftEquiv
  (p : ℕ)
  [Fact p.Prime]
  (P : Type*)
  [AddCommGroup P]
  [Module ℤ_[p] P]
  (W : Type*)
  [AddCommGroup W]
  [Module (ZMod p) W]
  : (P →+ W) ≃ₗ[ZMod p] (V p P →ₗ[ZMod p] W) where
  toFun φ := (QuotientAddGroup.lift (pSub p P) φ (apply_eq_zero_of_mem_pSub p P W φ)).toZModLinearMap p
  invFun ψ := ψ.toAddMonoidHom.comp (QuotientAddGroup.mk' (pSub p P))
  map_add' φ ψ := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective (pSub p P) v
    rfl
  map_smul' c φ := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective (pSub p P) v
    rfl
  left_inv φ := by ext x; rfl
  right_inv ψ := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective (pSub p P) v
    rfl

@[simp]
def toB
  (p : ℕ)
  [Fact p.Prime]
  (P : Type*)
  [AddCommGroup P]
  [Module ℤ_[p] P]
  (B : Type*)
  [CommRing B]
  [Algebra (ZMod p) B]
  : (P →+ ZMod p) →ₗ[ZMod p] (P →+ B) where
  toFun φ := (algebraMap (ZMod p) B).toAddMonoidHom.comp φ
  map_add' φ ψ := by ext x; simp
  map_smul' c φ := by
    ext x
    simp [Algebra.smul_def]

def E
  (p : ℕ)
  [Fact p.Prime]
  (P : Type*)
  [AddCommGroup P]
  [Module ℤ_[p] P]
  (B : Type*)
  [CommRing B]
  [Algebra (ZMod p) B]
  : B ⊗[ZMod p] (P →+ ZMod p) →ₗ[B] (P →+ B) :=
  (toB p P B).liftBaseChange B

private lemma exists_eq_natCast_add_mul
  (p : ℕ)
  [Fact p.Prime]
  (P : Type*)
  [AddCommGroup P]
  [Module ℤ_[p] P]
  (r : ℤ_[p]) : ∃ (n : ℕ) (r' : ℤ_[p]), r = n + p * r' := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp (PadicInt.appr_spec 1 r)
  refine ⟨r.appr 1, c, ?_⟩
  rw [pow_one] at hc
  linear_combination hc

instance finiteV
  (p : ℕ)
  [Fact p.Prime]
  (P : Type*)
  [AddCommGroup P]
  [Module ℤ_[p] P]
  [Module.Finite ℤ_[p] P]
  : Module.Finite (ZMod p) (V p P) := by
  obtain ⟨s, hs⟩ := (‹Module.Finite ℤ_[p] P›).fg_top
  classical
  refine ⟨⟨s.image (QuotientAddGroup.mk' (pSub p P)), ?_⟩⟩
  rw [eq_top_iff]
  rintro v -
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective (pSub p P) v
  have hx : x ∈ Submodule.span ℤ_[p] (s : Set P) := by rw [hs]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy =>
    exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hy))
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    obtain ⟨n, c', rfl⟩ := exists_eq_natCast_add_mul p P c
    have h' : ((n : ℤ_[p]) + p * c') • y = n • y + p • (c' • y) := by
      rw [add_smul, Nat.cast_smul_eq_nsmul, mul_smul, Nat.cast_smul_eq_nsmul]
    have hp0 : QuotientAddGroup.mk' (pSub p P) (p • (c' • y)) = 0 :=
      (QuotientAddGroup.eq_zero_iff _).mpr (nsmul_mem_pSub p P _)
    rw [h', map_add, hp0, add_zero, map_nsmul]
    exact Submodule.smul_of_tower_mem _ n hy

private lemma liftEquiv_apply_mk
  (p : ℕ)
  [Fact p.Prime]
  (P : Type*)
  [AddCommGroup P]
  [Module ℤ_[p] P]
  (W : Type*)
  [AddCommGroup W]
  [Module (ZMod p) W]
  (φ : P →+ W) (x : P) :
    liftEquiv p P W φ (QuotientAddGroup.mk' (pSub p P) x) = φ x := rfl

private lemma liftEquiv_symm_apply
  (p : ℕ)
  [Fact p.Prime]
  (P : Type*)
  [AddCommGroup P]
  [Module ℤ_[p] P]
  (W : Type*)
  [AddCommGroup W]
  [Module (ZMod p) W]
  (ψ : V p P →ₗ[ZMod p] W) (x : P) :
    (liftEquiv p P W).symm ψ x = ψ (QuotientAddGroup.mk' (pSub p P) x) := rfl

private lemma toB_apply
  (p : ℕ)
  [Fact p.Prime]
  (P : Type*)
  [AddCommGroup P]
  [Module ℤ_[p] P]
  (B : Type*)
  [CommRing B]
  [Algebra (ZMod p) B]
  (φ : P →+ ZMod p) (x : P) : toB p P B φ x = algebraMap (ZMod p) B (φ x) := rfl

private lemma E_tmul
  (p : ℕ)
  [Fact p.Prime]
  (P : Type*)
  [AddCommGroup P]
  [Module ℤ_[p] P]
  (B : Type*)
  [CommRing B]
  [Algebra (ZMod p) B]
  (b : B) (φ : P →+ ZMod p) (x : P) : E p P B (b ⊗ₜ[ZMod p] φ) x = b * algebraMap (ZMod p) B (φ x) :=
  rfl

noncomputable def Ecomp
  (p : ℕ)
  [Fact p.Prime]
  (P : Type*)
  [AddCommGroup P]
  [Module ℤ_[p] P]
  (B : Type*)
  [CommRing B]
  [Algebra (ZMod p) B]
  [Module.Finite ℤ_[p] P]
  : B ⊗[ZMod p] (P →+ ZMod p) ≃ₗ[ZMod p] (P →+ B) :=
  ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B) (liftEquiv p P (ZMod p))).restrictScalars
      (ZMod p)).trans <|
    (TensorProduct.comm (ZMod p) B (Module.Dual (ZMod p) (V p P))).trans <|
      (dualTensorHomEquiv (ZMod p) (V p P) B).trans (liftEquiv p P B).symm

private lemma Ecomp_tmul
  (p : ℕ)
  [Fact p.Prime]
  (P : Type*)
  [AddCommGroup P]
  [Module ℤ_[p] P]
  (B : Type*)
  [CommRing B]
  [Algebra (ZMod p) B]
  [Module.Finite ℤ_[p] P]
  (b : B) (φ : P →+ ZMod p) (x : P) :
    Ecomp p P B (b ⊗ₜ[ZMod p] φ) x = b * algebraMap (ZMod p) B (φ x) := by
  sorry

private lemma E_eq_Ecomp
  (p : ℕ)
  [Fact p.Prime]
  (P : Type*)
  [AddCommGroup P]
  [Module ℤ_[p] P]
  (B : Type*)
  [CommRing B]
  [Algebra (ZMod p) B]
  [Module.Finite ℤ_[p] P]
  (z : B ⊗[ZMod p] (P →+ ZMod p)) : E p P B z = Ecomp p P B z := by
  sorry

private lemma E_bijective
  (p : ℕ)
  [Fact p.Prime]
  (P : Type*)
  [AddCommGroup P]
  [Module ℤ_[p] P]
  (B : Type*)
  [CommRing B]
  [Algebra (ZMod p) B]
  [Module.Finite ℤ_[p] P]
  : Function.Bijective (E p P B) := by
  have : (E p P B : B ⊗[ZMod p] (P →+ ZMod p) → (P →+ B)) = Ecomp p P B := funext (E_eq_Ecomp p P B)
  rw [this]
  exact (Ecomp p P B).bijective

noncomputable def Eequiv
  (p : ℕ)
  [Fact p.Prime]
  (P : Type*)
  [AddCommGroup P]
  [Module ℤ_[p] P]
  (B : Type*)
  [CommRing B]
  [Algebra (ZMod p) B]
  [Module.Finite ℤ_[p] P]
  : B ⊗[ZMod p] (P →+ ZMod p) ≃ₗ[B] (P →+ B) :=
  LinearEquiv.ofBijective (E p P B) (E_bijective p P B)

private lemma Eequiv_tmul
  (p : ℕ)
  [Fact p.Prime]
  (P : Type*)
  [AddCommGroup P]
  [Module ℤ_[p] P]
  (B : Type*)
  [CommRing B]
  [Algebra (ZMod p) B]
  [Module.Finite ℤ_[p] P]
  (b : B) (φ : P →+ ZMod p) (x : P) :
    Eequiv p P B (b ⊗ₜ[ZMod p] φ) x = b * algebraMap (ZMod p) B (φ x) :=
  rfl

@[path]
private lemma main
  [AddCommGroup P] [CommRing B]
  {p : ℕ} [Fact p.Prime] [Module ℤ_[p] P] [Module.Finite ℤ_[p] P] [Algebra (ZMod p) B] :
-- imply
  ∃ e : B ⊗[ZMod p] (P →+ ZMod p) ≃ₗ[B] (P →+ B),
      ∀ (b : B) (φ : P →+ ZMod p) (x : P), e (b ⊗ₜ[ZMod p] φ) x = b * algebraMap (ZMod p) B (φ x) :=
-- proof
  ⟨Eequiv p P B, Eequiv_tmul p P B⟩


-- created on 2026-10-09
