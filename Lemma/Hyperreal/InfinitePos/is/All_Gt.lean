import Lemma.Int.GeAbs
import Lemma.Int.GeAbs_0
import Mathlib.Analysis.Real.Hyperreal
import sympy.core.singleton
open Int


@[main, comm, mp, mpr]
private lemma pos
-- given
  (x : ℝ*) :
-- imply
  x.InfinitePos ↔ ∀ δ : ℝ⁺, x > δ := by
-- proof
  unfold Hyperreal.InfinitePos
  constructor <;>
    intro h
  ·
    intro ⟨δ, hδ⟩
    have h := h δ
    convert h
  ·
    if h_x : x > 0 then
      intro δ
      have h_δ := GeAbs_0 δ
      have h := h ⟨|δ| + 1, by linarith⟩
      simp at h
      have h_δ := GeAbs (δ : ℝ*)
      linarith
    else
      have h := h 1
      simp_all
      linarith


@[main, comm, mp, mpr]
private lemma main
-- given
  (x : ℝ*) :
-- imply
  x.InfinitePos ↔ ∀ δ : ℝ, x > δ := by
-- proof
  simp [Hyperreal.InfinitePos]


-- created on 2025-12-25
