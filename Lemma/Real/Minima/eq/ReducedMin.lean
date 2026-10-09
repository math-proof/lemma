import sympy.Basic
import sympy.concrete.expr_with_limits
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Fintype.Lattice


@[path]
private lemma main
  [Finite ι] [Nonempty ι] [Finite κ] [Nonempty κ]
  {a : ι → κ → ℝ} :
-- imply
  Minima Set.univ (fun p : ι × κ => a p.1 p.2) = Minima Set.univ fun i => Minima Set.univ (a i) := by
-- proof
  obtain ⟨⟨i₀, j₀⟩, hp⟩ := Finite.exists_min (fun p : ι × κ => a p.1 p.2)
  have hset : ∀ i z, z ∈ (a i '' Set.univ) → a i₀ j₀ ≤ z := by
    intro i z hz
    obtain ⟨j, -, rfl⟩ := hz
    exact hp (i, j)
  have hin : ∀ i, a i₀ j₀ ≤ Minima Set.univ (a i) := fun i =>
    le_csInf (Set.image_nonempty.mpr Set.univ_nonempty) (hset i)
  have hi₀ : Minima Set.univ (a i₀) = a i₀ j₀ :=
    le_antisymm (csInf_le (Set.toFinite _).bddBelow ⟨j₀, trivial, rfl⟩) (hin i₀)
  have h₁ : IsLeast ((fun p : ι × κ => a p.1 p.2) '' Set.univ) (a i₀ j₀) := by
    refine ⟨⟨(i₀, j₀), trivial, rfl⟩, ?_⟩
    rintro _ ⟨q, -, rfl⟩
    exact hp q
  have h₂ : IsLeast ((fun i => Minima Set.univ (a i)) '' Set.univ) (a i₀ j₀) := by
    refine ⟨⟨i₀, trivial, hi₀⟩, ?_⟩
    rintro _ ⟨i, -, rfl⟩
    exact hin i
  unfold Minima at *
  rw [h₁.csInf_eq, h₂.csInf_eq]


-- created on 2026-10-08
