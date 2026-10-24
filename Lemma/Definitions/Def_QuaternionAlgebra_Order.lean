import Mathlib

set_option autoImplicit false

namespace QuaternionAlgebra

open scoped Quaternion

variable {a b : ℚ}

structure IsOrder (Λ : Submodule ℤ ℍ[ℚ, a, b]) : Prop where

  one_mem : (1 : ℍ[ℚ, a, b]) ∈ Λ

  mul_mem : ∀ ⦃x y : ℍ[ℚ, a, b]⦄, x ∈ Λ → y ∈ Λ → x * y ∈ Λ

  spanTop : Submodule.span ℚ (Λ : Set ℍ[ℚ, a, b]) = ⊤

  fg : Λ.FG

def IsUnitOf (Λ : Submodule ℤ ℍ[ℚ, a, b]) (u : ℍ[ℚ, a, b]) : Prop :=
  u ∈ Λ ∧ ∃ v ∈ Λ, u * v = 1 ∧ v * u = 1

def IsQuadraticDatum (t n : ℤ) (α : ℍ[ℚ, a, b]) : Prop :=
  α * α - (t : ℚ) • α + (n : ℚ) • (1 : ℍ[ℚ, a, b]) = 0

def EmbeddingDatum (Λ : Submodule ℤ ℍ[ℚ, a, b]) (t n : ℤ) : Type :=
  {α : ℍ[ℚ, a, b] // α ∈ Λ ∧ IsQuadraticDatum t n α}

def IsOptimalDatum (Λ : Submodule ℤ ℍ[ℚ, a, b]) (α : ℍ[ℚ, a, b]) : Prop :=
  ∀ x ∈ Λ, (∃ c d : ℚ, x = c • (1 : ℍ[ℚ, a, b]) + d • α) →
    ∃ p q : ℤ, x = (p : ℚ) • (1 : ℍ[ℚ, a, b]) + (q : ℚ) • α

def UnitConj {Λ : Submodule ℤ ℍ[ℚ, a, b]} {t n : ℤ} (d d' : EmbeddingDatum Λ t n) : Prop :=
  ∃ u : ℍ[ℚ, a, b], IsUnitOf Λ u ∧ d'.1 * u = u * d.1

def HasEmbeddingConductor (Λ : Submodule ℤ ℍ[ℚ, a, b]) (α : ℍ[ℚ, a, b]) (f : ℕ) : Prop :=
  (∀ x ∈ Λ, (∃ c e : ℚ, x = c • (1 : ℍ[ℚ, a, b]) + e • α) →
      ∃ p q : ℤ, (f : ℚ) • x = (p : ℚ) • (1 : ℍ[ℚ, a, b]) + (q : ℚ) • α) ∧
    (∀ g : ℕ, 0 < g → g < f →
      ¬ (∀ x ∈ Λ, (∃ c e : ℚ, x = c • (1 : ℍ[ℚ, a, b]) + e • α) →
        ∃ p q : ℤ, (g : ℚ) • x = (p : ℚ) • (1 : ℍ[ℚ, a, b]) + (q : ℚ) • α))

abbrev EmbeddingDatum.HasConductor {Λ : Submodule ℤ ℍ[ℚ, a, b]} {t n : ℤ}
    (d : EmbeddingDatum Λ t n) (f : ℕ) : Prop :=
  HasEmbeddingConductor Λ d.1 f

def EmbeddingClassSet (Λ : Submodule ℤ ℍ[ℚ, a, b]) (t n : ℤ) : Type :=
  Quot (UnitConj (Λ := Λ) (t := t) (n := n))

noncomputable def condEmbeddingCount (Λ : Submodule ℤ ℍ[ℚ, a, b]) (t n : ℤ) (f : ℕ) : ℕ :=
  Nat.card {c : EmbeddingClassSet Λ t n //
    ∃ d : EmbeddingDatum Λ t n, Quot.mk _ d = c ∧ d.HasConductor f}

theorem isQuadraticDatum_iff {t n : ℤ} {α : ℍ[ℚ, a, b]} :
    IsQuadraticDatum t n α ↔ α * α - (t : ℚ) • α + (n : ℚ) • (1 : ℍ[ℚ, a, b]) = 0 :=
  Iff.rfl

end QuaternionAlgebra
