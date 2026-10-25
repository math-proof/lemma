import Mathlib
import Lemma.PeriodPair.Uniformization

set_option autoImplicit false

noncomputable section

open UpperHalfPlane

open scoped MatrixGroups

namespace ModularCurve.LevelN

def wp (N : ℕ) (v : Fin 2 → ZMod N) (τ : ℍ) : ℂ :=
  ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
    PeriodPair.weierstrassP (PeriodPair.ofTau τ)
      ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ))

def fricke (N : ℕ) (v : Fin 2 → ZMod N) (τ : ℍ) : ℂ :=
  -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * wp N v τ

def jAnalytic (τ : ℍ) : ℂ :=
  ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ

def generators (N : ℕ) : Set (ℍ → ℂ) :=
  insert jAnalytic {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke N v}

def ring (N : ℕ) : Subalgebra ℂ (ℍ → ℂ) :=
  Algebra.adjoin ℂ (generators N)

theorem jAnalytic_mem_generators (N : ℕ) : jAnalytic ∈ generators N :=
  Set.mem_insert _ _

theorem fricke_mem_generators (N : ℕ) {v : Fin 2 → ZMod N} (hv : v ≠ 0) :
    fricke N v ∈ generators N :=
  Set.mem_insert_of_mem _ ⟨v, hv, rfl⟩

theorem jAnalytic_mem (N : ℕ) : jAnalytic ∈ ring N :=
  Algebra.subset_adjoin (jAnalytic_mem_generators N)

theorem fricke_mem (N : ℕ) {v : Fin 2 → ZMod N} (hv : v ≠ 0) : fricke N v ∈ ring N :=
  Algebra.subset_adjoin (fricke_mem_generators N hv)

def jGen (N : ℕ) : ring N :=
  ⟨jAnalytic, jAnalytic_mem N⟩

@[simp]
theorem coe_jGen (N : ℕ) : ((jGen N : ring N) : ℍ → ℂ) = jAnalytic :=
  rfl

end ModularCurve.LevelN

end
