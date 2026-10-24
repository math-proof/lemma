import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Data.Finite.Prod

namespace ModularCurve

open Matrix
open scoped MatrixGroups

section ProjectiveLine

variable {R S : Type*} [CommRing R] [CommRing S]

def IsUnimodularRow (a c : R) : Prop :=
  ∃ x y : R, x * a + y * c = 1

theorem isUnimodularRow_one_left (t : R) : IsUnimodularRow (1 : R) t :=
  ⟨1, 0, by simp⟩

theorem isUnimodularRow_one_right (m : R) : IsUnimodularRow m (1 : R) :=
  ⟨0, 1, by simp⟩

theorem IsUnimodularRow.map (f : R →+* S) {a c : R} (h : IsUnimodularRow a c) :
    IsUnimodularRow (f a) (f c) := by
  obtain ⟨x, y, hxy⟩ := h
  exact ⟨f x, f y, by rw [← map_mul, ← map_mul, ← map_add, hxy, map_one]⟩

abbrev UnimodularRow (R : Type*) [CommRing R] := { v : R × R // IsUnimodularRow v.1 v.2 }

instance unimodularRowSetoid (R : Type*) [CommRing R] : Setoid (UnimodularRow R) where
  r v w := ∃ u : Rˣ, (u : R) * v.1.1 = w.1.1 ∧ (u : R) * v.1.2 = w.1.2
  iseqv := by
    refine ⟨fun v => ⟨1, by simp, by simp⟩, ?_, ?_⟩
    · rintro v w ⟨u, h1, h2⟩
      exact ⟨u⁻¹, by rw [← h1, Units.inv_mul_cancel_left],
        by rw [← h2, Units.inv_mul_cancel_left]⟩
    · rintro v w z ⟨u, h1, h2⟩ ⟨u', h1', h2'⟩
      exact ⟨u' * u, by rw [Units.val_mul, mul_assoc, h1, h1'],
        by rw [Units.val_mul, mul_assoc, h2, h2']⟩

def ProjectiveLine (R : Type*) [CommRing R] : Type _ :=
  Quotient (unimodularRowSetoid R)

instance instFiniteProjectiveLine [Finite R] : Finite (ProjectiveLine R) :=
  Quotient.finite _

def ProjectiveLine.map (f : R →+* S) : ProjectiveLine R → ProjectiveLine S :=
  Quotient.lift (fun v => (⟦⟨(f v.1.1, f v.1.2), v.2.map f⟩⟧ : ProjectiveLine S)) <| by
    rintro v w ⟨u, h1, h2⟩
    refine Quotient.sound ⟨⟨f u, f ↑u⁻¹, ?_, ?_⟩, ?_, ?_⟩
    · rw [← map_mul, Units.mul_inv, map_one]
    · rw [← map_mul, Units.inv_mul, map_one]
    · show f ↑u * f v.1.1 = f w.1.1
      rw [← map_mul, h1]
    · show f ↑u * f v.1.2 = f w.1.2
      rw [← map_mul, h2]

@[simp]
theorem ProjectiveLine.map_mk (f : R →+* S) (v : UnimodularRow R) :
    ProjectiveLine.map f ⟦v⟧ = ⟦⟨(f v.1.1, f v.1.2), v.2.map f⟩⟧ :=
  rfl

end ProjectiveLine

section Borel

variable {R : Type*} [CommRing R]

def borel (R : Type*) [CommRing R] : Subgroup (SpecialLinearGroup (Fin 2) R) where
  carrier := { M | M.1 1 0 = 0 }
  one_mem' := by
    show (1 : SpecialLinearGroup (Fin 2) R).1 1 0 = 0
    simp
  mul_mem' := by
    intro A B hA hB
    simp only [Set.mem_setOf_eq] at *
    show (A * B).1 1 0 = 0
    rw [SpecialLinearGroup.coe_mul, (Matrix.two_mul_expl A.1 B.1).2.2.1, hA, hB]
    ring
  inv_mem' := by
    intro A hA
    simp only [Set.mem_setOf_eq] at *
    show (A⁻¹).1 1 0 = 0
    rw [SpecialLinearGroup.SL2_inv_expl A]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, neg_eq_zero]
    exact hA

theorem mem_borel_iff {A : SpecialLinearGroup (Fin 2) R} : A ∈ borel R ↔ A.1 1 0 = 0 :=
  Iff.rfl

end Borel

end ModularCurve
