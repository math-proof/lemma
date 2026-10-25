import Def.Analysis.MeasureTheory.Notation.Part2
import Theorem.Analysis.Section_9_1.Part3
import Theorem.Analysis.MeasureTheory.Section_1_1_1.Part13
open BoundedInterval

open Pointwise


/-- Lattice points in a box decompose as a product of lattice points in each interval side. -/
def Box.sample_congr {d:ℕ} (B:Box d) (N:ℕ) :
↥(B.toSet ∩ (Set.range (fun (n:Fin d → ℤ) ↦ .toLp 2 (fun i ↦ (N:ℝ)⁻¹*(n i))))) ≃ ((i : Fin d) → ↑(↑(B.side i) ∩ Set.range fun n:ℤ ↦ (N:ℝ)⁻¹ * ↑n)) := {
    toFun x i := by
      obtain ⟨ x, hx ⟩ := x; refine ⟨ x i, ?_ ⟩
      simp at hx; obtain ⟨hx1, n, hn⟩ := hx
      exact ⟨hx1 i, ⟨n i, by rw [← hn]⟩⟩
    invFun x := by
      refine ⟨ .toLp 2 (fun i ↦ (x i).1), ?_ ⟩
      simp; constructor
      . intro i; exact (x i).2.1
      have h (i:Fin d) : ∃ y:ℤ, (N:ℝ)⁻¹ * y = (x i).1 := by
        obtain ⟨ w, hx ⟩ := (x i).2.2; exact ⟨w, by simpa using hx⟩
      choose y hy using h; use y; ext i; simp [hy i]
    left_inv x := by ext; simp
    right_inv x := by ext; simp
  }

