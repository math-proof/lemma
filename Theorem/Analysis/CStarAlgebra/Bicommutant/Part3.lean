import Mathlib.Analysis.InnerProductSpace.Adjoint
import Def.Analysis.CStarAlgebra.Bicommutant.Part3


namespace Complex.CStarAlgebra.Bicommutant

open Matrix ComplexInnerProductSpace

/-- Pointwise form of the inclusion. -/
theorem ampIncl_ofLp (n m : ℕ) (j : Fin m)
    (x : EuclideanSpace ℂ (Fin n)) (i : Fin m) :
    (ampIncl n m j x).ofLp i =
      Pi.single (M := fun _ : Fin m => EuclideanSpace ℂ (Fin n)) j x i :=
  rfl

/-- Amplified operators commute past inclusions. -/
theorem ampOp_incl (n m : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (j : Fin m) :
    (ampOp n m A).comp (ampIncl n m j) = (ampIncl n m j).comp (matToOp n A) := by
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  intro i
  rw [LinearMap.comp_apply, LinearMap.comp_apply, ampOp_apply, ampIncl_ofLp,
    ampIncl_ofLp, Pi.single_apply, Pi.single_apply]
  split_ifs with h <;> simp_all

/-- Amplified operators commute past projections. -/
theorem ampOp_proj (n m : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (i : Fin m) :
    (PiLp.projₗ (𝕜 := ℂ) 2 (fun _ : Fin m => EuclideanSpace ℂ (Fin n)) i).comp
        (ampOp n m A) =
      (matToOp n A).comp
        (PiLp.projₗ (𝕜 := ℂ) 2 (fun _ : Fin m => EuclideanSpace ℂ (Fin n)) i) := by
  apply LinearMap.ext
  intro v
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  change (ampOp n m A v).ofLp i = matToOp n A (v.ofLp i)
  exact ampOp_apply n m A v i

/-- Every amplified vector is the sum of its coordinate inclusions. -/
theorem sum_ampIncl_proj (n m : ℕ)
    (v : PiLp 2 fun _ : Fin m => EuclideanSpace ℂ (Fin n)) :
    ∑ j, ampIncl n m j
        ((PiLp.projₗ (𝕜 := ℂ) 2 (fun _ : Fin m => EuclideanSpace ℂ (Fin n)) j) v) = v := by
  apply WithLp.ofLp_injective
  rw [WithLp.ofLp_sum]
  have h := LinearMap.sum_single_apply _ (WithLp.ofLp v)
  rw [← h]
  apply Finset.sum_congr rfl
  intro j _
  rfl

/-- Amplification preserves multiplication. -/
theorem ampOp_mul (n m : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ) :
    ampOp n m (A * B) = (ampOp n m A).comp (ampOp n m B) := by
  apply LinearMap.ext
  intro v
  apply PiLp.ext
  intro i
  rw [LinearMap.comp_apply, ampOp_apply, ampOp_apply, ampOp_apply, matToOp_mul,
    Module.End.mul_apply]

/-- Amplification preserves one. -/
theorem ampOp_one (n m : ℕ) : ampOp n m 1 = LinearMap.id := by
  have h1 : matToOp n (1 : Matrix (Fin n) (Fin n) ℂ) = LinearMap.id := by
    apply LinearMap.ext
    intro x
    simp [matToOp]
  apply LinearMap.ext
  intro v
  apply PiLp.ext
  intro i
  rw [ampOp_apply, h1, LinearMap.id_apply, LinearMap.id_apply]

/-- Pointwise form of inclusion commutation. -/
theorem ampOp_incl_apply (n m : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (j : Fin m)
    (x : EuclideanSpace ℂ (Fin n)) :
    ampOp n m A (ampIncl n m j x) = ampIncl n m j (matToOp n A x) :=
  LinearMap.congr_fun (ampOp_incl n m A j) x

/-- Pointwise form of projection commutation. -/
theorem ampOp_proj_apply (n m : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (i : Fin m)
    (v : PiLp 2 fun _ : Fin m => EuclideanSpace ℂ (Fin n)) :
    (PiLp.projₗ (𝕜 := ℂ) 2 (fun _ : Fin m => EuclideanSpace ℂ (Fin n)) i)
        (ampOp n m A v) =
      matToOp n A
        ((PiLp.projₗ (𝕜 := ℂ) 2 (fun _ : Fin m => EuclideanSpace ℂ (Fin n)) i) v) :=
  LinearMap.congr_fun (ampOp_proj n m A i) v

end Complex.CStarAlgebra.Bicommutant
