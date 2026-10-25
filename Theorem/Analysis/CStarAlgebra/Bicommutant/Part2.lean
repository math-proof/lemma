import Mathlib.Analysis.InnerProductSpace.Adjoint
import Def.Analysis.CStarAlgebra.Bicommutant.Part2


namespace Complex.CStarAlgebra.Bicommutant

open Matrix ComplexInnerProductSpace

/-- Pointwise action of the amplified operator. -/
theorem ampOp_apply (n m : ℕ) (A : Matrix (Fin n) (Fin n) ℂ)
    (v : PiLp 2 fun _ : Fin m => EuclideanSpace ℂ (Fin n)) (i : Fin m) :
    ampOp n m A v i = matToOp n A (v i) := by
  simp [ampOp]

/-- Inner product against the amplified action moves to the starred matrix. -/
theorem ampOp_inner (n m : ℕ) (A : Matrix (Fin n) (Fin n) ℂ)
    (w v : PiLp 2 fun _ : Fin m => EuclideanSpace ℂ (Fin n)) :
    ⟪ampOp n m A w, v⟫ = ⟪w, ampOp n m (star A) v⟫ := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [ampOp_apply, ampOp_apply, matToOp_star, LinearMap.adjoint_inner_right]

/-- The orthogonal complement of an invariant subspace is invariant. -/
theorem inv_orthogonal_of_invariant (n m : ℕ)
    (S : Set (Matrix (Fin n) (Fin n) ℂ))
    (K : Submodule ℂ (PiLp 2 fun _ : Fin m => EuclideanSpace ℂ (Fin n)))
    (hKs : ∀ A ∈ S, ∀ v ∈ K, ampOp n m (star A) v ∈ K)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A ∈ S)
    (w : PiLp 2 fun _ : Fin m => EuclideanSpace ℂ (Fin n)) (hw : w ∈ Kᗮ) :
    ampOp n m A w ∈ Kᗮ := by
  rw [Submodule.mem_orthogonal]
  intro v hv
  rw [inner_eq_zero_symm, ampOp_inner]
  exact Submodule.inner_left_of_mem_orthogonal (hKs A hA v hv) hw

set_option linter.style.haveILetI false in
/-- The orthogonal projection onto an invariant subspace commutes with the
amplified action. -/
theorem proj_comm_of_invariant (n m : ℕ)
    (S : Set (Matrix (Fin n) (Fin n) ℂ))
    (K : Submodule ℂ (PiLp 2 fun _ : Fin m => EuclideanSpace ℂ (Fin n)))
    (hK : ∀ A ∈ S, ∀ v ∈ K, ampOp n m A v ∈ K)
    (hKs : ∀ A ∈ S, ∀ v ∈ K, ampOp n m (star A) v ∈ K)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A ∈ S) :
    K.starProjection.toLinearMap ∘ₗ ampOp n m A
      = ampOp n m A ∘ₗ K.starProjection.toLinearMap := by
  haveI := FiniteDimensional.complete ℂ (PiLp 2 fun _ : Fin m => EuclideanSpace ℂ (Fin n))
  haveI := FiniteDimensional.complete ℂ (↥K)
  haveI := Submodule.HasOrthogonalProjection.ofCompleteSpace K
  have hPz : ∀ z ∈ Kᗮ, K.starProjection.toLinearMap z = 0 := by
    intro z hz
    have h0 : K.starProjection z =
        ((0 : ↥K) : PiLp 2 fun _ : Fin m => EuclideanSpace ℂ (Fin n)) := by
      rw [Submodule.starProjection_apply,
        Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal hz]
    change K.starProjection z = 0
    rw [h0]
    rfl
  have hPy : ∀ y ∈ K, K.starProjection.toLinearMap y = y := by
    intro y hy
    change K.starProjection y = y
    exact Submodule.starProjection_eq_self_iff.mpr hy
  apply LinearMap.ext
  intro x
  obtain ⟨y, hy, z, hz, rfl⟩ := K.exists_add_mem_mem_orthogonal x
  have hAy : ampOp n m A y ∈ K := hK A hA y hy
  have hAz : ampOp n m A z ∈ Kᗮ :=
    inv_orthogonal_of_invariant n m S K hKs A hA z hz
  have hPAy : K.starProjection.toLinearMap (ampOp n m A y) = ampOp n m A y :=
    hPy _ hAy
  have hPAz : K.starProjection.toLinearMap (ampOp n m A z) = 0 := hPz _ hAz
  simp only [LinearMap.comp_apply, map_add, map_zero, hPy y hy, hPz z hz, hPAy, hPAz,
    add_zero]

end Complex.CStarAlgebra.Bicommutant
