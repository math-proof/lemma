import Mathlib.Analysis.InnerProductSpace.Adjoint
import Def.Analysis.CStarAlgebra.Bicommutant.Part4


namespace Complex.CStarAlgebra.Bicommutant

open Matrix ComplexInnerProductSpace

theorem matToOp_entryMat (n : ℕ)
    (E : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) :
    matToOp n (entryMat n E) = E :=
  Matrix.toEuclideanLin.apply_symm_apply E

/-- Entries inherit commutation with amplified operators. -/
theorem ampEntry_comm_of_comm (n m : ℕ)
    (T : PiLp 2 (fun _ : Fin m => EuclideanSpace ℂ (Fin n)) →ₗ[ℂ]
      PiLp 2 (fun _ : Fin m => EuclideanSpace ℂ (Fin n)))
    (A : Matrix (Fin n) (Fin n) ℂ)
    (hT : T.comp (ampOp n m A) = (ampOp n m A).comp T) (i j : Fin m) :
    (matToOp n A).comp (ampEntry n m T i j) =
      (ampEntry n m T i j).comp (matToOp n A) := by
  apply LinearMap.ext
  intro x
  simp only [ampEntry, LinearMap.comp_apply]
  have hTx := LinearMap.congr_fun hT ((ampIncl n m j) x)
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at hTx
  rw [← ampOp_proj_apply, ← hTx, ampOp_incl_apply]

/-- Entry matrices lie in the centralizer. -/
theorem entryMat_mem_centralizer_of_comm (n m : ℕ)
    (S : StarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ))
    (T : PiLp 2 (fun _ : Fin m => EuclideanSpace ℂ (Fin n)) →ₗ[ℂ]
      PiLp 2 (fun _ : Fin m => EuclideanSpace ℂ (Fin n)))
    (hT : ∀ A ∈ (S : Set (Matrix (Fin n) (Fin n) ℂ)),
      T.comp (ampOp n m A) = (ampOp n m A).comp T) (i j : Fin m) :
    entryMat n (ampEntry n m T i j) ∈
      StarSubalgebra.centralizer ℂ (S : Set (Matrix (Fin n) (Fin n) ℂ)) := by
  rw [StarSubalgebra.mem_centralizer_iff]
  intro A hA
  have hAs : star A ∈ (S : Set (Matrix (Fin n) (Fin n) ℂ)) :=
    StarMemClass.star_mem hA
  have e1 := ampEntry_comm_of_comm n m T A (hT A hA) i j
  have e2 := ampEntry_comm_of_comm n m T (star A) (hT (star A) hAs) i j
  refine ⟨?_, ?_⟩ <;> apply matToOp_injective n <;>
    rw [matToOp_mul, matToOp_mul, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
      matToOp_entryMat] <;>
    assumption

/-- A double-centralizer element commutes, amplified, with anything commuting
with the amplification. -/
theorem amp_comm_of_mem (n m : ℕ)
    (S : StarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ))
    (B : Matrix (Fin n) (Fin n) ℂ)
    (hB : B ∈ StarSubalgebra.centralizer ℂ
      ((StarSubalgebra.centralizer ℂ (S : Set (Matrix (Fin n) (Fin n) ℂ))) :
        Set (Matrix (Fin n) (Fin n) ℂ)))
    (T : PiLp 2 (fun _ : Fin m => EuclideanSpace ℂ (Fin n)) →ₗ[ℂ]
      PiLp 2 (fun _ : Fin m => EuclideanSpace ℂ (Fin n)))
    (hT : ∀ A ∈ (S : Set (Matrix (Fin n) (Fin n) ℂ)),
      T.comp (ampOp n m A) = (ampOp n m A).comp T) :
    (ampOp n m B).comp T = T.comp (ampOp n m B) := by
  have eop : ∀ i j : Fin m, (matToOp n B).comp (ampEntry n m T i j) =
      (ampEntry n m T i j).comp (matToOp n B) := by
    intro i j
    have hM := entryMat_mem_centralizer_of_comm n m S T hT i j
    obtain ⟨hM1, -⟩ := (StarSubalgebra.mem_centralizer_iff (R := ℂ)).mp
      (SetLike.mem_coe.mpr hB) _ hM
    have hmul : matToOp n (entryMat n (ampEntry n m T i j) * B) =
        matToOp n (B * entryMat n (ampEntry n m T i j)) := by rw [hM1]
    rw [matToOp_mul, matToOp_mul, matToOp_entryMat] at hmul
    rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp]
    exact hmul.symm
  have hTentry : ∀ (j : Fin m) (x : EuclideanSpace ℂ (Fin n)),
      T (ampIncl n m j x) =
        ∑ i, ampIncl n m i ((ampEntry n m T i j) x) := by
    intro j x
    conv_lhs => rw [← sum_ampIncl_proj n m (T (ampIncl n m j x))]
    apply Finset.sum_congr rfl
    intro i _
    rfl
  have hTv : ∀ (v : PiLp 2 fun _ : Fin m => EuclideanSpace ℂ (Fin n)),
      T v = ∑ j, T (ampIncl n m j
        ((PiLp.projₗ (𝕜 := ℂ) 2 (fun _ : Fin m => EuclideanSpace ℂ (Fin n)) j) v)) := by
    intro v
    conv_lhs => rw [← sum_ampIncl_proj n m v, map_sum]
  have hBv : ∀ (v : PiLp 2 fun _ : Fin m => EuclideanSpace ℂ (Fin n)),
      ampOp n m B v = ∑ j, ampIncl n m j (matToOp n B
        ((PiLp.projₗ (𝕜 := ℂ) 2 (fun _ : Fin m => EuclideanSpace ℂ (Fin n)) j) v)) := by
    intro v
    conv_lhs => rw [← sum_ampIncl_proj n m v, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact ampOp_incl_apply n m B j _
  apply LinearMap.ext
  intro v
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  conv_lhs => rw [hTv, map_sum]
  conv_rhs => rw [hBv, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [hTentry]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [ampOp_incl_apply]
  congr 1
  exact LinearMap.congr_fun (eop i j) _

end Complex.CStarAlgebra.Bicommutant
