import Lemma.Hyperreal.NotInfinitesimal.is.Any_GeAbs
import Lemma.Int.AbsAdd.eq.AddAbsS.of.Le0Mul
open Hyperreal Int


@[main]
private lemma main
  {a b : ℝ*}
-- given
  (h : a * b ≥ 0)
  (h_a : ¬Infinitesimal a)
  (h_b : ¬Infinitesimal b) :
-- imply
  ¬Infinitesimal (a + b) := by
-- proof
  apply NotInfinitesimal.of.Any_GeAbs
  let ⟨⟨A, hA⟩, h_a⟩ := Any_GeAbs.of.NotInfinitesimal h_a
  let ⟨⟨B, hB⟩, h_b⟩ := Any_GeAbs.of.NotInfinitesimal h_b
  simp at h_a h_b
  use ⟨A + B, by linarith⟩
  simp
  calc 
    A + B ≤ |a| + |b| := by linarith
    _ = _ := (AbsAdd.eq.AddAbsS.of.Le0Mul h).symm


-- created on 2025-12-20
