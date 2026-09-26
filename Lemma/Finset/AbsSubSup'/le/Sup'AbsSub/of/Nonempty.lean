import Mathlib.Order.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Order.CompleteLattice.Finset
import sympy.Basic
open Finset


@[main]
private lemma main
  {ι : Type*}
  {s : Finset ι}
  {x y : ι → ℝ}
-- given
  (h : s.Nonempty) :
-- imply
  |s.sup' h x - s.sup' h y| ≤ s.sup' h (fun i => |x i - y i|) := by
-- proof
  have key : ∀ x y : ι → ℝ, s.sup' h x - s.sup' h y ≤ s.sup' h (fun i => |x i - y i|) := fun x y => by
    rw [sub_le_iff_le_add]
    refine sup'_le h _ fun i hi => ?_
    have h₁ := le_sup' y hi
    have h₂ := le_sup' (fun i => |x i - y i|) hi
    have h₃ := le_abs_self (x i - y i)
    linarith
  refine abs_sub_le_iff.2 ⟨key x y, ?_⟩
  simpa only [abs_sub_comm] using key y x


-- created on 2026-09-26
