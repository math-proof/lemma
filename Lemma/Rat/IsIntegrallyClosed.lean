import Mathlib
import sympy.Basic


/--
[IsIntegrallyClosed_of_isIntegrallyClosedIn_of_faithfulSMul](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsIntegrallyClosed_of_isIntegrallyClosedIn_of_faithfulSMul.lean)
-/
@[path]
private lemma main
  {A F : Type*} [CommRing A] [IsDomain A] [Field F] [Algebra A F] [FaithfulSMul A F] [IsIntegrallyClosedIn A F] :
-- imply
  IsIntegrallyClosed A := by
-- proof
  rw [isIntegrallyClosed_iff (FractionRing A)]
  intro x hx
  have hinj : Function.Injective (algebraMap A F) := FaithfulSMul.algebraMap_injective A F
  let φ : FractionRing A →ₐ[A] F :=
    { IsFractionRing.lift hinj with
      commutes' := fun a => by simp [IsFractionRing.lift_algebraMap] }
  have hφ : ∀ y, φ y = IsFractionRing.lift hinj y := fun _ => rfl
  have hx' : IsIntegral A (φ x) := hx.map φ
  obtain ⟨a, ha⟩ := IsIntegrallyClosedIn.algebraMap_eq_of_integral hx'
  refine ⟨a, ?_⟩
  apply (IsFractionRing.lift hinj : FractionRing A →+* F).injective
  rw [IsFractionRing.lift_algebraMap, ← hφ]
  exact ha


-- created on 2026-10-05
