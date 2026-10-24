import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.EllipticCurves.code.OrdinarySupersingular
open OrdinarySupersingular OrdinarySupersingularClassification
open ConductorOrder


namespace OrdinarySupersingular

/--
[isOrdinary_iff_not_supersingular](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/OrdinarySupersingular.lean)
-/
@[path]
lemma isOrdinary_iff_not_supersingular
  {F : Type u}
  [Field F]
  [DecidableEq F]
  {E : WeierstrassCurve.Affine F}
  {p : ℕ}
  [Fact (Nat.Prime p)]
  [CharP F p] :
-- imply
  IsOrdinary E p ↔ ¬ IsSupersingular E p := by
-- proof
  constructor
  · rintro ⟨P, hP, hPne⟩ hss
    exact hPne (hss P hP)
  · intro hns
    unfold IsSupersingular at hns
    push_neg at hns
    exact hns

end OrdinarySupersingular

namespace OrdinarySupersingular

/--
[ordinary_or_supersingular](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/OrdinarySupersingular.lean)
-/
@[path]
lemma ordinary_or_supersingular
  {F : Type u}
  [Field F]
  [DecidableEq F]
  {E : WeierstrassCurve.Affine F}
  {p : ℕ}
  [Fact (Nat.Prime p)]
  [CharP F p] :
-- imply
  IsOrdinary E p ∨ IsSupersingular E p := by
-- proof
  obtain hss | hns := em (IsSupersingular E p)
  · exact Or.inr hss
  · exact Or.inl ((isOrdinary_iff_not_supersingular E p).mpr hns)

end OrdinarySupersingular

namespace OrdinarySupersingular

/--
[jInvariant_pow_frobenius](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/OrdinarySupersingular.lean)
-/
@[path]
lemma jInvariant_pow_frobenius
  {F : Type u}
  [Field F]
  [DecidableEq F]
  {A B : F}
  {p : ℕ}
  [Fact (Nat.Prime p)]
  [CharP F p] :
-- imply
  jInvariant (A ^ (p ^ 2)) (B ^ (p ^ 2)) = (jInvariant A B) ^ (p ^ 2) := by
-- proof
  haveI : ExpChar F p := expChar_prime F p
  let φ := iterateFrobenius F p 2
  have hφ : ∀ x : F, φ x = x ^ (p ^ 2) := fun x => iterateFrobenius_def p 2 x
  suffices h : φ (jInvariant A B) = jInvariant (φ A) (φ B) by
    rw [← hφ (jInvariant A B), h]
    simp only [hφ]
  simp only [jInvariant, φ, map_div₀, map_mul, map_pow, map_add, map_ofNat]
/-- If `E : y² = x³ + Ax + B` is supersingular, then `E` is isomorphic to its `p²`-Frobenius
twist: there exists `μ ≠ 0` with `A^(p²) = μ⁴ A` and `B^(p²) = μ⁶ B`. -/
end OrdinarySupersingular
namespace OrdinarySupersingularClassification
open ConductorOrder


namespace OrdinarySupersingularClassification

/--
[conductor_dvd_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/OrdinarySupersingular.lean)
-/
@[path]
lemma conductor_dvd_of_le
  {d : ℤ}
  {f₁ f₂ : ℕ}
-- given
  (h : conductorOrder d f₁ ≤ conductorOrder d f₂) :
-- imply
  f₂ ∣ f₁ := by
-- proof
  have hmem : (⟨0, (f₁ : ℤ)⟩ : ℤ√d) ∈ conductorOrder d f₂ := by
    apply h
    simp [mem_conductorOrder_iff]
  rw [mem_conductorOrder_iff] at hmem
  exact Int.natCast_dvd_natCast.mp hmem

end OrdinarySupersingularClassification


-- created on 2026-10-23
