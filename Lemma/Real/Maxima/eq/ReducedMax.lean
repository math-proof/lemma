import sympy.Basic
import sympy.concrete.expr_with_limits
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Fintype.Lattice


@[main]
private lemma main
  [Finite ι] [Nonempty ι] [Finite κ] [Nonempty κ]
  {a : ι → κ → ℝ} :
-- imply
  Maxima Set.univ (fun p : ι × κ => a p.1 p.2) = Maxima Set.univ (fun i => Maxima Set.univ (a i)) := by
-- proof
  obtain ⟨⟨i₀, j₀⟩, hp⟩ := Finite.exists_max (fun p : ι × κ => a p.1 p.2)
  have hset : ∀ i z, z ∈ (a i '' Set.univ) → z ≤ a i₀ j₀ := by
    intro i z hz
    obtain ⟨j, -, rfl⟩ := hz
    exact hp (i, j)
  have hin : ∀ i, Maxima Set.univ (a i) ≤ a i₀ j₀ := fun i =>
    csSup_le (Set.image_nonempty.mpr Set.univ_nonempty) (hset i)
  have hi₀ : Maxima Set.univ (a i₀) = a i₀ j₀ :=
    le_antisymm (hin i₀) (le_csSup (Set.toFinite _).bddAbove ⟨j₀, trivial, rfl⟩)
  have h₁ : IsGreatest ((fun p : ι × κ => a p.1 p.2) '' Set.univ) (a i₀ j₀) := by
    refine ⟨⟨(i₀, j₀), trivial, rfl⟩, ?_⟩
    rintro _ ⟨q, -, rfl⟩
    exact hp q
  have h₂ : IsGreatest ((fun i => Maxima Set.univ (a i)) '' Set.univ) (a i₀ j₀) := by
    refine ⟨⟨i₀, trivial, hi₀⟩, ?_⟩
    rintro _ ⟨i, -, rfl⟩
    exact hin i
  unfold Maxima at *
  rw [h₁.csSup_eq, h₂.csSup_eq]


-- created on 2021-08-12
