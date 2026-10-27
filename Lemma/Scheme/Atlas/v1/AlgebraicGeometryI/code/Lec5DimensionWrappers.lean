import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.AlgebraicGeometryI.code.Lec5DimensionWrappers


/--
[thm51_dim_affine_space](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec5DimensionWrappers.lean)
-/
@[path]
lemma thm51_dim_affine_space
  {k : Type*}
  [Field k]
  {n : ℕ} :
-- imply
  ringKrullDim (MvPolynomial (Fin n) k) = n := by
-- proof
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing]
  simp

/--
[cor11_variety_finite_dim](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec5DimensionWrappers.lean)
-/
@[path]
lemma cor11_variety_finite_dim
  {k : Type*}
  [Field k]
  {A : Type*}
  [CommRing A]
  [Algebra k A]
  [Algebra.FiniteType k A] :
-- imply
  ringKrullDim A < ⊤ := by
-- proof
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹_›
  have h1 : ringKrullDim A ≤ ringKrullDim (MvPolynomial (Fin n) k) :=
    ringKrullDim_le_of_surjective f.toRingHom hf
  have h2 : ringKrullDim (MvPolynomial (Fin n) k) < ⊤ := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing,
      ringKrullDim_eq_zero_of_isField (Field.toIsField k)]
    simp only [zero_add]
    exact WithBot.coe_lt_coe.mpr (ENat.coe_lt_top _)
  exact lt_of_le_of_lt h1 h2


-- created on 2026-10-23
