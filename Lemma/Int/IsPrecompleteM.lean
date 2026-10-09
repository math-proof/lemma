import Mathlib
import sympy.Basic


/--
[IharaLemma_isPrecomplete_of_finite](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IharaLemma_isPrecomplete_of_finite.lean)
-/
@[path]
private lemma main
  [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
  {I : Ideal R} [IsPrecomplete I R] :
-- imply
  IsPrecomplete I M := by
-- proof
  rw [← AdicCompletion.of_surjective_iff]
  intro y
  obtain ⟨t, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite (I := I) (M := M) y
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by rw [map_zero, map_zero]⟩
  | tmul r m =>
    obtain ⟨s, rfl⟩ := AdicCompletion.of_surjective I R r
    refine ⟨s • m, ?_⟩
    rw [AdicCompletion.ofTensorProduct_tmul, map_smul]
    exact (algebraMap_smul (AdicCompletion I R) s (AdicCompletion.of I M m)).symm
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add, map_add, ha, hb]⟩


-- created on 2026-10-05
