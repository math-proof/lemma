import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[LinearMap_bijective_of_forall_bijective_baseChange_quotient_maximal](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_LinearMap_bijective_of_forall_bijective_baseChange_quotient_maximal.lean)
-/
@[path]
private lemma main
  [CommRing R]
  [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Free R M]
  [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Free R N]
  (f : M →ₗ[R] N)
  -- given
  (h : ∀ (𝔪 : Ideal R) [𝔪.IsMaximal], Function.Bijective (f.baseChange (R ⧸ 𝔪))) :
  -- imply
  Function.Bijective f := by
  -- proof
  classical
  obtain hR | hR := subsingleton_or_nontrivial R
  ·
    let _ : Subsingleton M := Module.subsingleton R M
    let _ : Subsingleton N := Module.subsingleton R N
    refine ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ _⟩⟩
  let bM := Module.Free.chooseBasis R M
  let bN := Module.Free.chooseBasis R N
  obtain ⟨𝔪₀, h𝔪₀⟩ := Ideal.exists_maximal R
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex R M) = Fintype.card (Module.Free.ChooseBasisIndex R N) := by
    let _ := h𝔪₀
    let e := LinearEquiv.ofBijective (f.baseChange (R ⧸ 𝔪₀)) (h 𝔪₀)
    have h1 := e.finrank_eq
    rw [Module.finrank_eq_card_basis (Algebra.TensorProduct.basis (R ⧸ 𝔪₀) bM),
      Module.finrank_eq_card_basis (Algebra.TensorProduct.basis (R ⧸ 𝔪₀) bN)] at h1
    apply h1
  let σ : Module.Free.ChooseBasisIndex R N ≃ Module.Free.ChooseBasisIndex R M := (Fintype.equivOfCardEq hcard).symm
  let bN' : Module.Basis (Module.Free.ChooseBasisIndex R M) R N := bN.reindex σ
  let A := LinearMap.toMatrix bM bN' f
  suffices hdet : IsUnit A.det by
    apply (LinearEquiv.ofIsUnitDet hdet).bijective
  by_contra hndet
  obtain ⟨𝔪, h𝔪, hmem⟩ := exists_max_ideal_of_mem_nonunits hndet
  let _ := h𝔪
  have hzero : (A.map (algebraMap R (R ⧸ 𝔪))).det = 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    apply hmem
  have hA : LinearMap.toMatrix (Algebra.TensorProduct.basis (R ⧸ 𝔪) bM)
    (Algebra.TensorProduct.basis (R ⧸ 𝔪) bN') (f.baseChange (R ⧸ 𝔪)) =
    A.map (algebraMap R (R ⧸ 𝔪)) :=
    LinearMap.toMatrix_baseChange _ _ _ _
  have hunit : IsUnit (LinearMap.toMatrix (Algebra.TensorProduct.basis (R ⧸ 𝔪) bM)
    (Algebra.TensorProduct.basis (R ⧸ 𝔪) bN') (f.baseChange (R ⧸ 𝔪))).det := by
    apply LinearEquiv.isUnit_det (LinearEquiv.ofBijective (f.baseChange (R ⧸ 𝔪)) (h 𝔪))
      (Algebra.TensorProduct.basis (R ⧸ 𝔪) bM) (Algebra.TensorProduct.basis (R ⧸ 𝔪) bN')
  rw [hA, hzero] at hunit
  apply not_isUnit_zero hunit


-- created on 2026-10-20
