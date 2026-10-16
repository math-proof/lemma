import Mathlib
import sympy.Basic
open TensorProduct
open scoped TensorProduct


attribute [local instance] Ideal.Quotient.field


private lemma subsingleton_baseChange_kaehler
  {S A B : Type u} [CommRing S] [CommRing A] [CommRing B] [Algebra S A] [Algebra S B] [Algebra A B] [IsScalarTower S A B]
  {k : Type u} [Field k] [Algebra S k]
-- given
  (h : (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S A B) (AlgHom.id S k)).toRingHom.FormallyUnramified) :
-- imply
  Subsingleton ((B ⊗[S] k) ⊗[B] Ω[B⁄A]) := by
-- proof
  let f := Algebra.TensorProduct.map (IsScalarTower.toAlgHom S A B) (AlgHom.id S k)
  let _ : Algebra (A ⊗[S] k) (B ⊗[S] k) := f.toRingHom.toAlgebra
  have : IsScalarTower A (A ⊗[S] k) (B ⊗[S] k) :=
    IsScalarTower.of_algebraMap_eq (R := A) (S := A ⊗[S] k) (A := B ⊗[S] k) (fun a => by
      rw [RingHom.algebraMap_toAlgebra]
      show algebraMap A (B ⊗[S] k) a = f (algebraMap A (A ⊗[S] k) a)
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      show algebraMap A B a ⊗ₜ[S] (1 : k) = f (a ⊗ₜ 1)
      rw [Algebra.TensorProduct.map_tmul]
      rfl)
  have : Algebra.IsPushout A (A ⊗[S] k) B (B ⊗[S] k) := by
    refine (Algebra.IsPushout.tensorProduct_tensorProduct S k A B ?_).symm
    ext x
    show f ((1 : A) ⊗ₜ[S] x) = (1 : B) ⊗ₜ[S] x
    rw [Algebra.TensorProduct.map_tmul, map_one]
    rfl
  have : Algebra.FormallyUnramified (A ⊗[S] k) (B ⊗[S] k) := h
  have : Subsingleton Ω[(B ⊗[S] k)⁄(A ⊗[S] k)] := Algebra.FormallyUnramified.subsingleton_kaehlerDifferential
  apply (KaehlerDifferential.tensorKaehlerEquiv A (A ⊗[S] k) B (B ⊗[S] k)).toEquiv.subsingleton


private lemma subsingleton_tensor_of_subsingleton_baseChange
  {S B : Type u} [CommRing S] [CommRing B] [Algebra S B] [AddCommGroup M] [Module B M]
  {k : Type u} [Field k] [Algebra S k] [Algebra B k] [IsScalarTower S B k]
-- given
  (h : Subsingleton ((B ⊗[S] k) ⊗[B] M)) :
-- imply
  Subsingleton (k ⊗[B] M) := by
-- proof
  let ψ : B ⊗[S] k →ₐ[S] k := Algebra.TensorProduct.lift (IsScalarTower.toAlgHom S B k) (AlgHom.id S k) (fun _ _ => Commute.all _ _)
  let _ : Algebra (B ⊗[S] k) k := ψ.toRingHom.toAlgebra
  have : IsScalarTower B (B ⊗[S] k) k :=
    IsScalarTower.of_algebraMap_eq (R := B) (S := B ⊗[S] k) (A := k) (fun b => by
      rw [RingHom.algebraMap_toAlgebra]
      show algebraMap B k b = ψ (b ⊗ₜ 1)
      rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
      rfl)
  apply (TensorProduct.AlgebraTensorModule.cancelBaseChange B (B ⊗[S] k) k k M).symm.toEquiv.subsingleton


private lemma subsingleton_tensor_of_field_ext
  {B : Type u} [CommRing B] [AddCommGroup M] [Module B M]
  {κ : Type u} [Field κ] [Algebra B κ]
  {k : Type u} [Field k] [Algebra κ k] [Algebra B k] [IsScalarTower B κ k]
-- given
  (h : Subsingleton (k ⊗[B] M)) :
-- imply
  Subsingleton (κ ⊗[B] M) := by
-- proof
  have : Subsingleton (k ⊗[κ] (κ ⊗[B] M)) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange B κ k k M).toEquiv.subsingleton
  apply (Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right κ k).mp this


private lemma not_mem_support_of_subsingleton_quotient_tensor
  {B : Type u} [CommRing B] [AddCommGroup M] [Module B M] [Module.Finite B M]
  {m : Ideal B} [hm : m.IsMaximal]
-- given
  (h : Subsingleton ((B ⧸ m) ⊗[B] M))
  (hmem : (⟨m, hm.isPrime⟩ : PrimeSpectrum B) ∈ Module.support B M) :
-- imply
  False := by
-- proof
  have hsub : Subsingleton (M ⧸ (m • (⊤ : Submodule B M))) :=
    (TensorProduct.quotTensorEquivQuotSMul M m).symm.toEquiv.subsingleton
  have htop : m • (⊤ : Submodule B M) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    apply (Submodule.Quotient.mk_eq_zero _).mp (Subsingleton.elim _ _)
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m (⊤ : Submodule B M)
    Module.Finite.fg_top (by rw [htop])
  have hrann : r ∈ Module.annihilator B M := by
    rw [Module.mem_annihilator]
    intro x
    apply hr x trivial
  have hrm : r ∈ m := by
    rw [Module.mem_support_iff_of_finite] at hmem
    apply hmem hrann
  have : (1 : B) ∈ m := by
    have := m.sub_mem hrm hr1
    rwa [sub_sub_cancel] at this
  apply hm.ne_top ((Ideal.eq_top_iff_one _).mpr this)


/--
[Algebra_FormallyUnramified_of_forall_isAlgClosed_formallyUnramified_tensorProduct_map](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_FormallyUnramified_of_forall_isAlgClosed_formallyUnramified_tensorProduct_map.lean)
-/
@[path]
private lemma main
  {S A B : Type u} [CommRing S] [CommRing A] [CommRing B] [Algebra S A] [Algebra S B] [Algebra A B] [IsScalarTower S A B] [Algebra.FiniteType S B]
-- given
  (h : ∀ (k : Type u) [Field k] [IsAlgClosed k] [Algebra S k],
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom S A B) (AlgHom.id S k)).toRingHom.FormallyUnramified) :
-- imply
  Algebra.FormallyUnramified A B := by
-- proof
  classical
  have : Algebra.FiniteType A B := Algebra.FiniteType.of_restrictScalars_finiteType S A B
  have : Module.Finite B Ω[B⁄A] := inferInstance
  suffices hs : Subsingleton Ω[B⁄A] from ⟨hs⟩
  rw [← Module.support_eq_empty_iff (R := B), Set.eq_empty_iff_forall_notMem]
  intro p hp
  obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p.asIdeal p.isPrime.ne_top
  have := hm
  apply not_mem_support_of_subsingleton_quotient_tensor
    (subsingleton_tensor_of_field_ext (κ := B ⧸ m) (k := AlgebraicClosure (B ⧸ m)) (M := Ω[B⁄A])
      (subsingleton_tensor_of_subsingleton_baseChange (S := S) (k := AlgebraicClosure (B ⧸ m)) (M := Ω[B⁄A])
        (subsingleton_baseChange_kaehler (k := AlgebraicClosure (B ⧸ m)) (h (AlgebraicClosure (B ⧸ m))))))
    (Module.mem_support_mono hpm hp)


-- created on 2026-10-16
