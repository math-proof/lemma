import sympy.Basic
import sympy.concrete.expr_with_limits
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Fintype.Lattice


@[main]
private lemma main
  [Finite ι] [Nonempty ι]
  {a : ι → ℝ} :
-- imply
  Maxima Set.univ (fun p => Real.exp (a p)) = Real.exp (Maxima Set.univ a) := by
-- proof
  obtain ⟨p, hp⟩ := Finite.exists_max a
  have h₁ : IsGreatest (a '' Set.univ) (a p) := by
    refine ⟨⟨p, trivial, rfl⟩, ?_⟩
    rintro _ ⟨q, -, rfl⟩
    exact hp q
  have h₂ : IsGreatest ((fun q => Real.exp (a q)) '' Set.univ) (Real.exp (a p)) := by
    refine ⟨⟨p, trivial, rfl⟩, ?_⟩
    rintro _ ⟨q, -, rfl⟩
    exact Real.exp_le_exp.mpr (hp q)
  unfold Maxima
  rw [h₁.csSup_eq, h₂.csSup_eq]


-- created on 2026-09-27
