import Mathlib
import sympy.Basic
open scoped TensorProduct


private lemma norm_pi_apply
  [CommRing L]
  [Fintype ι]
  {g : ι → L} :
-- imply
  Algebra.norm L g = ∏ i, g i := by
-- proof
  classical
  rw [Algebra.norm_eq_matrix_det (Pi.basisFun L ι)]
  have h : Algebra.leftMulMatrix (Pi.basisFun L ι) g = Matrix.diagonal g := by
    ext i j
    rw [Algebra.leftMulMatrix_eq_repr_mul, Matrix.diagonal_apply, Pi.basisFun_repr, Pi.basisFun_apply,
      Pi.mul_apply, Pi.single_apply]
    split_ifs with h
    ·
      subst h
      simp
    ·
      simp
  rw [h, Matrix.det_diagonal]


/--
[Algebra_algebraMap_norm_eq_prod_apply_of_card_eq_finrank](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_algebraMap_norm_eq_prod_apply_of_card_eq_finrank.lean)
-/
@[path]
private lemma main
  {W : Type u} [CommRing W]
  {T : Type v} [CommRing T] [Algebra W T] [Module.Free W T] [Module.Finite W T]
  {L : Type w} [Field L] [Algebra W L]
  {σ : ι → (T →ₐ[W] L)} [Fintype ι]
  {a : T}
-- given
  (hσ : Function.Injective σ)
  (hcard : Fintype.card ι = Module.finrank W T) :
-- imply
  algebraMap W L (Algebra.norm W a) = ∏ i, σ i a := by
-- proof
  classical
  let _ : Nontrivial W := (algebraMap W L).domain_nontrivial
  have h1 : algebraMap W L (Algebra.norm W a) = Algebra.norm L ((1 : L) ⊗ₜ[W] a : L ⊗[W] T) := by
    rw [Algebra.norm_apply, Algebra.norm_apply, ← LinearMap.det_baseChange (A := L)]
    congr 1
    refine LinearMap.ext fun x => ?_
    induction x using TensorProduct.inductionOn with
    | tmul l t =>
      rw [LinearMap.baseChange_tmul]
      simp [Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy =>
      rw [map_add, map_add, hx, hy]
  rw [h1]
  obtain hι | hι := isEmpty_or_nonempty ι
  ·
    have h0 : Module.finrank L (L ⊗[W] T) = 0 := by
      rw [Module.finrank_baseChange, ← hcard, Fintype.card_eq_zero]
    rw [Algebra.norm_apply, LinearMap.det_eq_one_of_finrank_eq_zero h0, Finset.univ_eq_empty,
      Finset.prod_empty]
  ·
    let σ' : ι → (L ⊗[W] T →ₐ[L] L) := fun i =>
      Algebra.TensorProduct.lift (AlgHom.id L L) (σ i) (fun _ _ => Commute.all _ _)
    have hσ't : ∀ i (l : L) (t : T), σ' i (l ⊗ₜ[W] t) = l * σ i t := fun i l t => by
      simp [σ', Algebra.TensorProduct.lift_tmul]
    have hσ'inj : Function.Injective σ' := by
      intro i j h
      apply hσ
      ext t
      have := DFunLike.congr_fun h ((1 : L) ⊗ₜ[W] t)
      simpa [hσ't] using this
    have hli0 : LinearIndependent L (fun i => ((σ' i : L ⊗[W] T →ₐ[L] L) : L ⊗[W] T → L)) := by
      apply (linearIndependent_monoidHom (L ⊗[W] T) L).comp (fun i => (σ' i).toMonoidHom)
      intro i j h
      apply hσ'inj
      apply AlgHom.ext
      intro x
      apply DFunLike.congr_fun h x
    let f : ι → Module.Dual L (L ⊗[W] T) := fun i => (σ' i).toLinearMap
    let ev : Module.Dual L (L ⊗[W] T) →ₗ[L] (L ⊗[W] T → L) :=
      { toFun := fun g => ⇑g
        map_add' := by
          intro _ _
          rfl
        map_smul' := by
          intro _ _
          rfl }
    have hli : LinearIndependent L f := LinearIndependent.of_comp ev hli0
    have hfinT : Module.finrank L (L ⊗[W] T) = Fintype.card ι := by
      rw [Module.finrank_baseChange, hcard]
    have hfinD : Fintype.card ι = Module.finrank L (Module.Dual L (L ⊗[W] T)) := by
      rw [Subspace.dual_finrank_eq, hfinT]
    let b := basisOfLinearIndependentOfCardEqFinrank hli hfinD
    let Φ : L ⊗[W] T →ₐ[L] (ι → L) := AlgHom.pi σ'
    have hΦ : ∀ x i, Φ x i = σ' i x := fun x i => rfl
    have hinj : Function.Injective Φ := by
      rw [injective_iff_map_eq_zero]
      intro v hv
      have hv' : ∀ i, σ' i v = 0 := fun i => by
        rw [← hΦ, hv]
        rfl
      refine (Module.forall_dual_apply_eq_zero_iff L v).1 (fun φ => ?_)
      rw [← b.sum_repr φ, LinearMap.sum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [LinearMap.smul_apply, coe_basisOfLinearIndependentOfCardEqFinrank]
      show b.repr φ i • (σ' i).toLinearMap v = 0
      rw [AlgHom.toLinearMap_apply, hv', smul_zero]
    have hfin : Module.finrank L (L ⊗[W] T) = Module.finrank L (ι → L) := by
      rw [hfinT, Module.finrank_fintype_fun_eq_card]
    have hsurj : Function.Surjective Φ :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin (f := Φ.toLinearMap)).1 hinj
    let e : L ⊗[W] T ≃ₐ[L] (ι → L) := AlgEquiv.ofBijective Φ ⟨hinj, hsurj⟩
    have he : e ((1 : L) ⊗ₜ[W] a) = fun i => σ i a := by
      funext i
      show Φ ((1 : L) ⊗ₜ[W] a) i = σ i a
      rw [hΦ, hσ't, one_mul]
    rw [← Algebra.norm_eq_of_algEquiv e, he, norm_pi_apply]


-- created on 2026-10-13
