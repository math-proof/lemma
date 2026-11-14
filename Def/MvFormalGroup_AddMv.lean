import Mathlib.RingTheory.MvPowerSeries.Substitution
import Structure.MvFormalGroup_BasicV2

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace MvFormalGroup

variable {R : Type*} [CommRing R]

private theorem subst_X_add_X {σ τ : Type*} [Finite σ] {a : σ → MvPowerSeries τ R}
    (ha : ∀ s, (a s).constantCoeff = 0) (s t : σ) :
    subst a (X s + X t : MvPowerSeries σ R) = a s + a t := by
  have h := hasSubst_of_constantCoeff_zero ha
  rw [subst_add h, subst_X h, subst_X h]

def addMv (g : ℕ) (R : Type*) [CommRing R] : MvFormalGroup g R where
  toPowerSeries := fun i => X (Sum.inl i) + X (Sum.inr i)
  constantCoeff_eq_zero := by
    intro i
    show ((X (Sum.inl i) + X (Sum.inr i) : MvPowerSeries (Fin g ⊕ Fin g) R)).constantCoeff = 0
    rw [map_add, constantCoeff_X, constantCoeff_X, add_zero]
  coeff_single_inl := by
    intro i j
    show ((X (Sum.inl i) + X (Sum.inr i) : MvPowerSeries (Fin g ⊕ Fin g) R)).coeff
        (Finsupp.single (Sum.inl j) 1) = if i = j then 1 else 0
    rw [map_add, coeff_index_single_X, coeff_index_single_X]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]
  coeff_single_inr := by
    intro i j
    show ((X (Sum.inl i) + X (Sum.inr i) : MvPowerSeries (Fin g ⊕ Fin g) R)).coeff
        (Finsupp.single (Sum.inr j) 1) = if i = j then 1 else 0
    rw [map_add, coeff_index_single_X, coeff_index_single_X]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]
  assoc := by
    intro i
    have hzB : ∀ s : Fin g ⊕ Fin g, ((Sum.elim
        (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
        fun l => X (Sum.inr (Sum.inl l))) s).constantCoeff = 0 := by
      rintro (l | l) <;> simp [constantCoeff_X]
    have hzC : ∀ s : Fin g ⊕ Fin g, ((Sum.elim
        (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
        fun l => X (Sum.inr (Sum.inr l))) s).constantCoeff = 0 := by
      rintro (l | l) <;> simp [constantCoeff_X]
    simp only [subst_X_add_X hzB, subst_X_add_X hzC, Sum.elim_inl, Sum.elim_inr]
    have hzA : ∀ s : Fin g ⊕ Fin g, ((Sum.elim
        (fun j => (X (Sum.inl j) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R)
          + X (Sum.inr (Sum.inl j)))
        fun j => X (Sum.inr (Sum.inr j))) s).constantCoeff = 0 := by
      rintro (j | j) <;> simp [constantCoeff_X]
    have hzA' : ∀ s : Fin g ⊕ Fin g, ((Sum.elim
        (fun j => (X (Sum.inl j) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
        fun j => X (Sum.inr (Sum.inl j)) + X (Sum.inr (Sum.inr j))) s).constantCoeff = 0 := by
      rintro (j | j) <;> simp [constantCoeff_X]
    rw [subst_X_add_X hzA, subst_X_add_X hzA']
    simp only [Sum.elim_inl, Sum.elim_inr]
    exact add_assoc _ _ _

end MvFormalGroup