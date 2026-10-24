import Mathlib
import sympy.Basic


/--
[dim_affine_space_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DimensionTheoryLight.lean)
-/
@[path]
lemma dim_affine_space_eq
  {k : Type*}
  [Field k]
  {n : ℕ} :
-- imply
  ringKrullDim (MvPolynomial (Fin n) k) = ↑n := by
-- proof
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
    zero_add, Nat.card_fin]

/--
[variety_finite_krullDim](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DimensionTheoryLight.lean)
-/
@[path]
lemma variety_finite_krullDim
  {k : Type*}
  [Field k]
  {A : Type*}
  [CommRing A]
  [Algebra k A]
  [Algebra.FiniteType k A] :
-- imply
  ringKrullDim A ≠ ⊤ := by
-- proof
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹_›
  have h := ringKrullDim_le_of_surjective (f : MvPolynomial (Fin n) k →+* A) hf
  rw [dim_affine_space_eq] at h
  intro htop
  rw [htop] at h
  exact absurd h (by nofun)


-- created on 2026-10-23
