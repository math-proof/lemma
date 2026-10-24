import Mathlib
import sympy.Basic


/--
[finite_map_strict_chains](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/FiniteMapStrictChains.lean)
-/
@[path]
lemma finite_map_strict_chains
  {A B : Type*}
  [CommRing A]
  [CommRing B]
  [Algebra A B]
  [Module.Finite A B]
  {p₁ p₂ : Ideal B}
  [p₁.IsPrime]
  [p₂.IsPrime]
-- given
  (h : p₁ < p₂) :
-- imply
  p₁.comap (algebraMap A B) < p₂.comap (algebraMap A B) := by
-- proof
  obtain ⟨h_le, x, hx2, hx1⟩ := SetLike.lt_iff_le_and_exists.mp h
  exact Ideal.comap_lt_comap_of_integral_mem_sdiff h_le ⟨hx2, hx1⟩
    (Algebra.IsIntegral.isIntegral x)


-- created on 2026-10-23
