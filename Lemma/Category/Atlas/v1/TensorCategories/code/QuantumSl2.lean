import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TensorCategories.code.QuantumSl2
open Coalgebra HopfAlgebra QuantumSl2
open scoped TensorProduct


namespace QuantumSl2

/--
[comul_Kinv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2.lean)
-/
@[path]
lemma comul_Kinv
  {k : Type u}
  [Field k]
  {A : Type v}
  [Ring A]
  [HopfAlgebra k A]
  [h : QuantumSl2 k A] :
-- imply
  comul (R := k) h.Kinv = h.Kinv ⊗ₜ[k] h.Kinv := by
-- proof
  have key1 : (h.K ⊗ₜ[k] h.K) * comul (R := k) h.Kinv = 1 := by
    rw [← h.comul_K, ← Bialgebra.comul_mul, h.K_mul_Kinv, Bialgebra.comul_one]
  have inv1 : (h.Kinv ⊗ₜ[k] h.Kinv) * (h.K ⊗ₜ[k] h.K) = (1 : A ⊗[k] A) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, h.Kinv_mul_K]
    exact (Algebra.TensorProduct.one_def).symm
  calc comul (R := k) h.Kinv
    = 1 * comul (R := k) h.Kinv := (one_mul _).symm
    _ = (h.Kinv ⊗ₜ[k] h.Kinv) * (h.K ⊗ₜ[k] h.K) * comul (R := k) h.Kinv := by rw [inv1]
    _ = (h.Kinv ⊗ₜ[k] h.Kinv) * ((h.K ⊗ₜ[k] h.K) * comul (R := k) h.Kinv) := mul_assoc _ _ _
    _ = (h.Kinv ⊗ₜ[k] h.Kinv) * 1 := by rw [key1]
    _ = h.Kinv ⊗ₜ[k] h.Kinv := mul_one _

end QuantumSl2

namespace QuantumSl2

/--
[counit_Kinv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2.lean)
-/
@[path]
lemma counit_Kinv
  {k : Type u}
  [Field k]
  {A : Type v}
  [Ring A]
  [HopfAlgebra k A]
  [h : QuantumSl2 k A] :
-- imply
  counit (R := k) h.Kinv = (1 : k) := by
-- proof
  have : counit (R := k) (h.K * h.Kinv) = counit (R := k) (1 : A) := by rw [h.K_mul_Kinv]
  rw [Bialgebra.counit_mul, Bialgebra.counit_one, h.counit_K] at this
  simpa using this

end QuantumSl2

namespace QuantumSl2

/--
[antipode_Kinv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2.lean)
-/
@[path]
lemma antipode_Kinv
  {k : Type u}
  [Field k]
  {A : Type v}
  [Ring A]
  [HopfAlgebra k A]
  [h : QuantumSl2 k A] :
-- imply
  antipode k h.Kinv = h.K := by
-- proof
  have hSKinv_mul : antipode k h.Kinv * h.Kinv = 1 := by
    have hopf := LinearMap.congr_fun
      (HopfAlgebra.mul_antipode_rTensor_comul (R := k) (A := A)) h.Kinv
    simp only [LinearMap.comp_apply, comul_Kinv, LinearMap.rTensor_tmul] at hopf
    rw [LinearMap.mul'_apply, counit_Kinv] at hopf
    simp only [Algebra.linearMap_apply, map_one] at hopf
    exact hopf
  calc antipode k h.Kinv
    = antipode k h.Kinv * 1 := (mul_one _).symm
    _ = antipode k h.Kinv * (h.Kinv * h.K) := by rw [h.Kinv_mul_K]
    _ = (antipode k h.Kinv * h.Kinv) * h.K := (mul_assoc _ _ _).symm
    _ = 1 * h.K := by rw [hSKinv_mul]
    _ = h.K := one_mul _

end QuantumSl2

namespace QuantumSl2

/--
[Theorem_1_25_2_Uq_sl2_Hopf](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2.lean)
-/
@[path]
lemma Theorem_1_25_2_Uq_sl2_Hopf
  {k : Type u}
  [Field k]
  {A : Type v}
  [Ring A]
  [HopfAlgebra k A]
  [h : QuantumSl2 k A] :
-- imply
  (comul (R := k) h.K = h.K ⊗ₜ[k] h.K) ∧ (comul (R := k) h.E = h.E ⊗ₜ[k] h.K + 1 ⊗ₜ[k] h.E) ∧ (comul (R := k) h.F = h.F ⊗ₜ[k] 1 + h.Kinv ⊗ₜ[k] h.F) ∧ (comul (R := k) h.Kinv = h.Kinv ⊗ₜ[k] h.Kinv) ∧ (counit (R := k) h.K = (1 : k)) ∧ (counit (R := k) h.E = (0 : k)) ∧ (counit (R := k) h.F = (0 : k)) ∧ (counit (R := k) h.Kinv = (1 : k)) ∧ (antipode k h.K = h.Kinv) ∧ (antipode k h.E = -(h.E * h.Kinv)) ∧ (antipode k h.F = -(h.K * h.F)) ∧ (antipode k h.Kinv = h.K) :=
-- proof
  ⟨h.comul_K, h.comul_E, h.comul_F, comul_Kinv,
    h.counit_K, h.counit_E, h.counit_F, counit_Kinv,
    h.antipode_K, h.antipode_E, h.antipode_F, antipode_Kinv⟩

end QuantumSl2


-- created on 2026-10-23
