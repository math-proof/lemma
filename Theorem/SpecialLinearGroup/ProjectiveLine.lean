module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section


namespace ModularCurve

open Matrix
open scoped MatrixGroups

section ProjectiveLine

variable {R S : Type*} [CommRing R] [CommRing S]


public theorem isUnimodularRow_one_left (t : R) : IsUnimodularRow (1 : R) t :=
  ⟨1, 0, by simp⟩


public theorem isUnimodularRow_one_right (m : R) : IsUnimodularRow m (1 : R) :=
  ⟨0, 1, by simp⟩


public theorem IsUnimodularRow.map (f : R →+* S) {a c : R} (h : IsUnimodularRow a c) :
    IsUnimodularRow (f a) (f c) := by
  obtain ⟨x, y, hxy⟩ := h
  exact ⟨f x, f y, by rw [← map_mul, ← map_mul, ← map_add, hxy, map_one]⟩


@[simp]
public theorem ProjectiveLine.map_mk (f : R →+* S) (v : UnimodularRow R) :
    ProjectiveLine.map f ⟦v⟧ = ⟦⟨(f v.1.1, f v.1.2), v.2.map f⟩⟧ :=
  rfl

end ProjectiveLine

section Borel

variable {R : Type*} [CommRing R]


public theorem mem_borel_iff {A : SpecialLinearGroup (Fin 2) R} : A ∈ borel R ↔ A.1 1 0 = 0 :=
  Iff.rfl

end Borel

end ModularCurve
