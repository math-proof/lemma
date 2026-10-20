/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ImaginaryQuadraticDiscriminant.lean -/

import sympy.atlas.NumberTheory.DirichletCharacter.Quadratic
set_option autoImplicit false

/-!
# Imaginary quadratic discriminants

This file specializes the canonical predicate `MetaMathlibExt.IsFundamentalDiscriminant` to
negative discriminants and packages conductor--fundamental-discriminant decompositions.
-/

namespace ImaginaryQuadraticDiscriminant

/-- `D` is an imaginary quadratic discriminant if it is negative and congruent to `0` or `1`
modulo `4`. -/
def IsImaginaryQuadraticDiscriminant (D : Int) : Prop :=
  D < 0 ∧ (D % 4 = 0 ∨ D % 4 = 1)

/-- A fundamental imaginary quadratic discriminant is a negative instance of the canonical
fundamental-discriminant predicate `MetaMathlibExt.IsFundamentalDiscriminant`. -/
def IsFundamentalImaginaryQuadraticDiscriminant (D : Int) : Prop :=
  D < 0 ∧ MetaMathlibExt.IsFundamentalDiscriminant D

/-- The set of imaginary quadratic discriminants. -/
def imaginaryQuadraticDiscriminants : Set Int :=
  {D | IsImaginaryQuadraticDiscriminant D}

/-- The set of fundamental imaginary quadratic discriminants. -/
def fundamentalImaginaryQuadraticDiscriminants : Set Int :=
  {D | IsFundamentalImaginaryQuadraticDiscriminant D}

@[simp]
theorem mem_imaginaryQuadraticDiscriminants {D : Int} :
    D ∈ imaginaryQuadraticDiscriminants ↔ IsImaginaryQuadraticDiscriminant D :=
  Iff.rfl

@[simp]
theorem mem_fundamentalImaginaryQuadraticDiscriminants {D : Int} :
    D ∈ fundamentalImaginaryQuadraticDiscriminants ↔
      IsFundamentalImaginaryQuadraticDiscriminant D :=
  Iff.rfl

/-- A decomposition `D = u ^ 2 * D_K` into a positive conductor and a fundamental imaginary
quadratic discriminant. -/
structure ImaginaryQuadraticDiscriminantDecomposition (D : Int) where
  u : Int
  D_K : Int
  hu : u ≥ 1
  hD_K : IsFundamentalImaginaryQuadraticDiscriminant D_K
  hD : D = u ^ 2 * D_K

/-- Exact unfolding of `IsImaginaryQuadraticDiscriminant`. -/
theorem isImaginaryQuadraticDiscriminant_iff (D : Int) :
    IsImaginaryQuadraticDiscriminant D ↔ D < 0 ∧ (D % 4 = 0 ∨ D % 4 = 1) :=
  Iff.rfl

/-- Constructor for an imaginary quadratic discriminant. -/
theorem isImaginaryQuadraticDiscriminant_mk {D : Int} (hneg : D < 0)
    (hmod : D % 4 = 0 ∨ D % 4 = 1) : IsImaginaryQuadraticDiscriminant D :=
  ⟨hneg, hmod⟩

/-- An imaginary quadratic discriminant is negative. -/
theorem isImaginaryQuadraticDiscriminant_neg {D : Int}
    (h : IsImaginaryQuadraticDiscriminant D) : D < 0 :=
  h.1

/-- An imaginary quadratic discriminant is congruent to `0` or `1` modulo `4`. -/
theorem isImaginaryQuadraticDiscriminant_mod {D : Int}
    (h : IsImaginaryQuadraticDiscriminant D) : D % 4 = 0 ∨ D % 4 = 1 :=
  h.2

/-- Constructor from the `0` modulo `4` case. -/
theorem isImaginaryQuadraticDiscriminant_of_mod_zero {D : Int} (hneg : D < 0)
    (hmod : D % 4 = 0) : IsImaginaryQuadraticDiscriminant D :=
  ⟨hneg, Or.inl hmod⟩

/-- Constructor from the `1` modulo `4` case. -/
theorem isImaginaryQuadraticDiscriminant_of_mod_one {D : Int} (hneg : D < 0)
    (hmod : D % 4 = 1) : IsImaginaryQuadraticDiscriminant D :=
  ⟨hneg, Or.inr hmod⟩

/-- The fundamental imaginary predicate is exactly negativity together with the canonical
fundamental-discriminant predicate. -/
theorem isFundamentalImaginaryQuadraticDiscriminant_iff (D : Int) :
    IsFundamentalImaginaryQuadraticDiscriminant D ↔
      D < 0 ∧ MetaMathlibExt.IsFundamentalDiscriminant D :=
  Iff.rfl

/-- Constructor for a fundamental imaginary quadratic discriminant. -/
theorem isFundamentalImaginaryQuadraticDiscriminant_mk {D : Int} (hneg : D < 0)
    (hfund : MetaMathlibExt.IsFundamentalDiscriminant D) :
    IsFundamentalImaginaryQuadraticDiscriminant D :=
  ⟨hneg, hfund⟩

/-- A fundamental imaginary quadratic discriminant satisfies the canonical predicate. -/
theorem isFundamentalImaginaryQuadraticDiscriminant_isFundamentalDiscriminant {D : Int}
    (h : IsFundamentalImaginaryQuadraticDiscriminant D) :
    MetaMathlibExt.IsFundamentalDiscriminant D :=
  h.2

/-- Every fundamental imaginary quadratic discriminant is an imaginary quadratic
discriminant. -/
theorem isFundamentalImaginaryQuadraticDiscriminant_isImaginary {D : Int}
    (h : IsFundamentalImaginaryQuadraticDiscriminant D) :
    IsImaginaryQuadraticDiscriminant D := by
  obtain ⟨hneg, hfund⟩ := h
  unfold MetaMathlibExt.IsFundamentalDiscriminant at hfund
  rcases hfund with ⟨_, hmod1⟩ | ⟨m, hDm, _, _⟩
  · exact ⟨hneg, Or.inr hmod1⟩
  · have h0 : D % 4 = 0 := by simp [hDm]
    exact ⟨hneg, Or.inl h0⟩

namespace ImaginaryQuadraticDiscriminantDecomposition

variable {D : Int}

/-- The fundamental discriminant stored by a decomposition is fundamental. -/
theorem isFundamental (h : ImaginaryQuadraticDiscriminantDecomposition D) :
    IsFundamentalImaginaryQuadraticDiscriminant h.D_K :=
  h.hD_K

/-- The conductor stored by a decomposition is at least one. -/
theorem u_ge_one (h : ImaginaryQuadraticDiscriminantDecomposition D) : h.u ≥ 1 :=
  h.hu

/-- The defining discriminant equation stored by a decomposition. -/
theorem prop_eq (h : ImaginaryQuadraticDiscriminantDecomposition D) :
    D = h.u ^ 2 * h.D_K :=
  h.hD

/-- Construct a decomposition from its conductor, fundamental discriminant, and equation. -/
def ofFundamental (u D_K : Int) (hu : u ≥ 1)
    (hD_K : IsFundamentalImaginaryQuadraticDiscriminant D_K)
    (hD : D = u ^ 2 * D_K) : ImaginaryQuadraticDiscriminantDecomposition D :=
  ⟨u, D_K, hu, hD_K, hD⟩

end ImaginaryQuadraticDiscriminantDecomposition

end ImaginaryQuadraticDiscriminant
