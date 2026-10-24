import Mathlib
import sympy.Basic


namespace Lemma34

/--
[noZeroSMulDivisors_of_linearEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lemma34DegreeAdditivity.lean)
-/
@[path]
lemma noZeroSMulDivisors_of_linearEquiv
  [CommRing R']
  [IsDomain R']
  [AddCommGroup M₁]
  [Module R' M₁]
  [AddCommGroup M₂]
  [Module R' M₂]
  [NoZeroSMulDivisors R' M₂]
  {e : M₁ ≃ₗ[R'] M₂} :
-- imply
  NoZeroSMulDivisors R' M₁ where eq_zero_or_eq_zero_of_smul_eq_zero {r x} h := by
-- proof
  have h' : r • e x = 0 := by rw [← e.map_smul, h, map_zero]
  obtain hr | hx := smul_eq_zero.mp h'
  · left; exact hr
  · right; exact e.injective (by rw [hx, map_zero])

end Lemma34

namespace Lemma34

/--
[Module.IsTorsion.of_linearEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lemma34DegreeAdditivity.lean)
-/
@[path]
lemma Module.IsTorsion.of_linearEquiv
  [CommRing R]
  [AddCommGroup M]
  [Module R M]
  [AddCommGroup N]
  [Module R N]
  {e : M ≃ₗ[R] N}
-- given
  (h : Module.IsTorsion R N) :
-- imply
  Module.IsTorsion R M := by
-- proof
  intro x
  obtain ⟨⟨a, ha⟩, hax⟩ := h (x := e x)
  refine ⟨⟨a, ha⟩, ?_⟩
  apply e.injective
  simp only [map_zero]
  change e ((a : R) • x) = 0
  rwa [map_smul]
variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
/-- Induction predicate for Lemma 34: for any submodule `N ⊆ M'` with
torsion quotient of length `k`, the degrees differ by `k`. -/
end Lemma34
/-- Lec 22, Lemma 34 (degree additivity): for a short exact sequence
`0 → E → E' → T → 0` of finite modules over a Dedekind domain `R`,
with `E, E'` torsion-free and `T` torsion of finite length,
`deg E' = deg E + length(T)`. -/



-- created on 2026-10-23
