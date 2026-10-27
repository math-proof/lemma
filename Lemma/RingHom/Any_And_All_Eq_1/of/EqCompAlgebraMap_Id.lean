import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Algebra.PointDerivations.Part2
import Def.Algebra_PointDerivations
open scoped TensorProduct

universe u

private def W
  {k : Type u} [Field k] {A : Type u} [CommRing A] [Algebra k A]
  (ev : A →+* k) : Submodule k A :=
  (Submodule.span k {(1 : A)}) ⊔ ((RingHom.ker ev) ^ 2 : Ideal A).restrictScalars k

private abbrev T
  {k : Type u} [Field k] {A : Type u} [CommRing A] [Algebra k A]
  (ev : A →+* k) : Type u :=
  A ⧸ W ev

private lemma ev_algebraMap
  {k : Type u} [Field k] {A : Type u} [CommRing A] [Algebra k A]
  (ev : A →+* k) (hev : ev.comp (algebraMap k A) = RingHom.id k) (c : k) :
  ev (algebraMap k A c) = c := by
  have h := congrArg (fun f : k →+* k => f c) hev
  simpa using h

private lemma sub_mem_ker
  {k : Type u} [Field k] {A : Type u} [CommRing A] [Algebra k A]
  (ev : A →+* k) (hev : ev.comp (algebraMap k A) = RingHom.id k) (a : A) :
  a - algebraMap k A (ev a) ∈ RingHom.ker ev := by
  rw [RingHom.mem_ker, map_sub, ev_algebraMap ev hev, sub_self]

private lemma le_ker
  {k : Type u} [Field k] {A : Type u} [CommRing A] [Algebra k A]
  (ev : A →+* k) {M : Type u} [AddCommGroup M] [Module k M]
  (D : ↥(Algebra.PointDerivations k A ev M)) :
  W ev ≤ LinearMap.ker (D : A →ₗ[k] M) := by
  apply sup_le
  ·
    rw [Submodule.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    apply Algebra.PointDerivations.apply_one D.2
  ·
    intro x hx
    rw [Submodule.restrictScalars_mem, pow_two] at hx
    rw [LinearMap.mem_ker]
    refine Submodule.smul_induction_on (p := fun y => (D : A →ₗ[k] M) y = 0) hx ?_ ?_
    ·
      intro a ha b hb
      rw [smul_eq_mul, Algebra.PointDerivations.apply_mul D.2, (RingHom.mem_ker).mp ha,
        (RingHom.mem_ker).mp hb, zero_smul, zero_smul, add_zero]
    ·
      intro x y hx hy
      rw [map_add, hx, hy, add_zero]

private def res
  {k : Type u} [Field k] {A : Type u} [CommRing A] [Algebra k A]
  (ev : A →+* k) (M : Type u) [AddCommGroup M] [Module k M] :
  ↥(Algebra.PointDerivations k A ev M) →ₗ[k] (T ev →ₗ[k] M) where
  toFun D := (W ev).liftQ (D : A →ₗ[k] M) (le_ker ev D)
  map_add' D D' := by
    ext a
    rfl
  map_smul' c D := by
    ext a
    rfl

private lemma mk_mul
  {k : Type u} [Field k] {A : Type u} [CommRing A] [Algebra k A]
  (ev : A →+* k) (hev : ev.comp (algebraMap k A) = RingHom.id k) (a b : A) :
  (Submodule.Quotient.mk (a * b) : T ev) =
    ev a • Submodule.Quotient.mk b + ev b • Submodule.Quotient.mk a := by
  rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add,
    Submodule.Quotient.eq]
  have h : a * b - (ev a • b + ev b • a) =
      (a - algebraMap k A (ev a)) * (b - algebraMap k A (ev b)) - algebraMap k A (ev a * ev b) := by
    simp only [Algebra.smul_def, map_mul]
    ring
  rw [h]
  refine Submodule.sub_mem _ ?_ ?_
  ·
    apply Submodule.mem_sup_right
    rw [Submodule.restrictScalars_mem, pow_two]
    apply Ideal.mul_mem_mul (sub_mem_ker ev hev a) (sub_mem_ker ev hev b)
  ·
    apply Submodule.mem_sup_left
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

private def toPoint
  {k : Type u} [Field k] {A : Type u} [CommRing A] [Algebra k A]
  (ev : A →+* k) (hev : ev.comp (algebraMap k A) = RingHom.id k)
  (M : Type u) [AddCommGroup M] [Module k M] :
  (T ev →ₗ[k] M) →ₗ[k] ↥(Algebra.PointDerivations k A ev M) where
  toFun f := ⟨LinearMap.comp f (W ev).mkQ, fun a b => by
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, mk_mul ev hev, map_add, map_smul, map_smul,
      LinearMap.comp_apply, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mkQ_apply]⟩
  map_add' f g := by
    ext a
    rfl
  map_smul' c f := by
    ext a
    rfl

private def resEquiv
  {k : Type u} [Field k] {A : Type u} [CommRing A] [Algebra k A]
  (ev : A →+* k) (hev : ev.comp (algebraMap k A) = RingHom.id k)
  (M : Type u) [AddCommGroup M] [Module k M] :
  ↥(Algebra.PointDerivations k A ev M) ≃ₗ[k] (T ev →ₗ[k] M) := by
  refine LinearEquiv.ofLinearMap (res ev M) (toPoint ev hev M) ?_ ?_
  ·
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro x
    refine Submodule.Quotient.induction_on (p := W ev) (x := x) ?_
    intro a
    rfl
  ·
    apply LinearMap.ext
    intro D
    apply Subtype.ext
    apply LinearMap.ext
    intro a
    rfl

private lemma res_map
  {k : Type u} [Field k] {A : Type u} [CommRing A] [Algebra k A]
  (ev : A →+* k) {M M' : Type u} [AddCommGroup M] [Module k M]
  [AddCommGroup M'] [Module k M'] (g : M →ₗ[k] M')
  (D : ↥(Algebra.PointDerivations k A ev M)) :
  res ev M' (Algebra.PointDerivations.map ev g D) = LinearMap.comp g (res ev M D) := by
  apply LinearMap.ext
  intro x
  refine Submodule.Quotient.induction_on (p := W ev) (x := x) ?_
  intro a
  rfl

private lemma finite_T
  {k : Type u} [Field k] {A : Type u} [CommRing A] [Algebra k A]
  (ev : A →+* k) (hev : ev.comp (algebraMap k A) = RingHom.id k)
  [Algebra.FiniteType k A] : Module.Finite k (T ev) := by
  classical
  let _ : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (RingHom.ker ev) : (RingHom.ker ev).FG)
  let v : ↥s → T ev := fun i => Submodule.Quotient.mk (i : A)
  refine Module.Finite.of_surjective
    ((Finsupp.linearCombination k v).comp
      (Finsupp.linearEquivFunOnFinite k k ↥s).symm.toLinearMap) ?_
  intro x
  refine Submodule.Quotient.induction_on (p := W ev) (x := x) ?_
  intro a
  have hm : a - algebraMap k A (ev a) ∈ Submodule.span A (s : Set A) := by
    rw [hs]
    exact sub_mem_ker ev hev a
  rw [Submodule.mem_span_finset] at hm
  obtain ⟨c, -, hc⟩ := hm
  refine ⟨fun i => ev (c i), ?_⟩
  change (Finsupp.linearCombination k v) (Finsupp.equivFunOnFinite.symm (fun i => ev (c i))) = Submodule.Quotient.mk a
  rw [Finsupp.equivFunOnFinite_symm_eq_sum, map_sum]
  simp only [Finsupp.linearCombination_single]
  have hsum : (∑ i : ↥s, ev (c ↑i) • (Submodule.Quotient.mk (↑i : A) : T ev)) =
      Submodule.Quotient.mk (∑ i ∈ s, algebraMap k A (ev (c i)) * i) := by
    rw [← Finset.sum_coe_sort s (fun i => algebraMap k A (ev (c i)) * i)]
    simp only [← Algebra.smul_def, ← Submodule.Quotient.mk_smul]
    exact (map_sum ((W ev).mkQ) _ _).symm
  rw [hsum, Submodule.Quotient.eq]
  simp only [smul_eq_mul] at hc
  have hrw : (∑ i ∈ s, algebraMap k A (ev (c i)) * i) - a =
      (∑ i ∈ s, (algebraMap k A (ev (c i)) - c i) * i) - algebraMap k A (ev a) := by
    rw [Finset.sum_congr rfl (fun i _ => sub_mul (algebraMap k A (ev (c i))) (c i) i),
      Finset.sum_sub_distrib, hc]
    ring
  rw [hrw]
  refine Submodule.sub_mem _ ?_ ?_
  ·
    apply Submodule.mem_sup_right
    rw [Submodule.restrictScalars_mem, pow_two]
    refine Ideal.sum_mem _ (fun i hi => Ideal.mul_mem_mul ?_ ?_)
    ·
      have hneg := (RingHom.ker ev).neg_mem (sub_mem_ker ev hev (c i))
      rwa [neg_sub] at hneg
    ·
      rw [← hs]
      apply Submodule.subset_span hi
  ·
    apply Submodule.mem_sup_left
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

private noncomputable def Psi
  {k : Type u} [Field k] {A : Type u} [CommRing A] [Algebra k A]
  (ev : A →+* k) (hev : ev.comp (algebraMap k A) = RingHom.id k)
  [Algebra.FiniteType k A] (M : Type u) [AddCommGroup M] [Module k M] :
  ↥(Algebra.PointDerivations k A ev M) ≃ₗ[k]
    (↥(Algebra.PointDerivations k A ev k) ⊗[k] M) :=
  let _ : Module.Finite k (T ev) := finite_T ev hev
  (resEquiv ev hev M).trans ((dualTensorHomEquiv k (T ev) M).symm.trans
    (TensorProduct.congr (resEquiv ev hev k).symm (LinearEquiv.refl k M)))

private lemma dualTensorHom_lTensor_apply
  {k : Type u} [Field k] {A : Type u} [CommRing A] [Algebra k A]
  (ev : A →+* k) [Algebra.FiniteType k A]
  (hev : ev.comp (algebraMap k A) = RingHom.id k)
  {M M' : Type u} [AddCommGroup M] [Module k M] [AddCommGroup M'] [Module k M']
  (g : M →ₗ[k] M') (x : Module.Dual k (T ev) ⊗[k] M) :
  dualTensorHom k (T ev) M' (LinearMap.lTensor (Module.Dual k (T ev)) g x) =
    LinearMap.comp g (dualTensorHom k (T ev) M x) := by
  let _ : Module.Finite k (T ev) := finite_T ev hev
  refine TensorProduct.inductionOn x ?_ ?_
  ·
    intro f m
    apply LinearMap.ext
    intro t
    simp [LinearMap.lTensor_tmul, dualTensorHom_apply, map_smul]
  ·
    intro x y hx hy
    rw [map_add, map_add, hx, hy, map_add, LinearMap.comp_add]

private lemma Psi_natural
  {k : Type u} [Field k] {A : Type u} [CommRing A] [Algebra k A]
  (ev : A →+* k) (hev : ev.comp (algebraMap k A) = RingHom.id k)
  [Algebra.FiniteType k A]
  {M M' : Type u} [AddCommGroup M] [Module k M] [AddCommGroup M'] [Module k M']
  (g : M →ₗ[k] M') (δ : ↥(Algebra.PointDerivations k A ev M)) :
  Psi ev hev M' (Algebra.PointDerivations.map ev g δ) =
    LinearMap.lTensor (↥(Algebra.PointDerivations k A ev k)) g (Psi ev hev M δ) := by
  let _ : Module.Finite k (T ev) := finite_T ev hev
  have h1 : resEquiv ev hev M' (Algebra.PointDerivations.map ev g δ) =
      LinearMap.comp g (resEquiv ev hev M δ) := res_map ev g δ
  have h2 : (dualTensorHomEquiv k (T ev) M').symm (LinearMap.comp g (resEquiv ev hev M δ)) =
      LinearMap.lTensor (Module.Dual k (T ev)) g
        ((dualTensorHomEquiv k (T ev) M).symm (resEquiv ev hev M δ)) := by
    apply (dualTensorHomEquiv k (T ev) M').injective
    rw [LinearEquiv.apply_symm_apply]
    show LinearMap.comp g (resEquiv ev hev M δ) = dualTensorHom k (T ev) M' (LinearMap.lTensor (Module.Dual k (T ev)) g
      ((dualTensorHomEquiv k (T ev) M).symm (resEquiv ev hev M δ)))
    rw [dualTensorHom_lTensor_apply ev hev]
    congr 1
    exact ((dualTensorHomEquiv k (T ev) M).apply_symm_apply _).symm
  have h3 : ∀ y : Module.Dual k (T ev) ⊗[k] M, TensorProduct.congr (resEquiv ev hev k).symm (LinearEquiv.refl k M') (LinearMap.lTensor (Module.Dual k (T ev)) g y) = LinearMap.lTensor (↥(Algebra.PointDerivations k A ev k)) g (TensorProduct.congr (resEquiv ev hev k).symm (LinearEquiv.refl k M) y) := by
    intro y
    refine TensorProduct.inductionOn y ?_ ?_
    ·
      intro _ _
      rfl
    ·
      intro x y hx hy
      simp only [map_add, hx, hy]
  unfold Psi
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearEquiv.trans_apply, h1, h2, h3]

private lemma Psi_self
  {k : Type u} [Field k] {A : Type u} [CommRing A] [Algebra k A]
  (ev : A →+* k) (hev : ev.comp (algebraMap k A) = RingHom.id k)
  [Algebra.FiniteType k A] (δ : ↥(Algebra.PointDerivations k A ev k)) :
  Psi ev hev k δ = δ ⊗ₜ[k] (1 : k) := by
  let _ : Module.Finite k (T ev) := finite_T ev hev
  have h : (dualTensorHomEquiv k (T ev) k).symm (resEquiv ev hev k δ) =
      (resEquiv ev hev k δ) ⊗ₜ[k] (1 : k) := by
    apply (dualTensorHomEquiv k (T ev) k).injective
    rw [LinearEquiv.apply_symm_apply]
    apply LinearMap.ext
    intro t
    rw [dualTensorHomEquiv_tmul, smul_eq_mul, mul_one]
  unfold Psi
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, h, TensorProduct.congr_tmul,
    LinearEquiv.symm_apply_apply]
  rfl

/--
[Algebra_PointDerivations_exists_linearEquiv_tensor_forall_map_eq_of_finiteType](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_PointDerivations_exists_linearEquiv_tensor_forall_map_eq_of_finiteType.lean)
-/
@[path]
private lemma main
  {k : Type u} [Field k]
  {A : Type u} [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
  {ev : A →+* k}
-- given
  (hev : ev.comp (algebraMap k A) = RingHom.id k) :
-- imply
  ∃ Ψ : ∀ (M : Type u) [AddCommGroup M] [Module k M], ↥(Algebra.PointDerivations k A ev M) ≃ₗ[k] (↥(Algebra.PointDerivations k A ev k) ⊗[k] M), (∀ (M M' : Type u) [AddCommGroup M] [Module k M] [AddCommGroup M'] [Module k M'] (g : M →ₗ[k] M') (δ : ↥(Algebra.PointDerivations k A ev M)), Ψ M' (Algebra.PointDerivations.map ev g δ) = LinearMap.lTensor (↥(Algebra.PointDerivations k A ev k)) g (Ψ M δ)) ∧ (∀ δ : ↥(Algebra.PointDerivations k A ev k), Ψ k δ = δ ⊗ₜ[k] (1 : k)) := by
-- proof
  classical
  apply Exists.intro (fun (M : Type u) [AddCommGroup M] [Module k M] => Psi ev hev M)
  constructor
  ·
    intro M M' _ _ _ _ g δ
    apply Psi_natural ev hev g δ
  ·
    intro δ
    apply Psi_self ev hev δ

-- created on 2026-10-20
