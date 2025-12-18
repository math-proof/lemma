import Lemma.Hyperreal.NotInfinitesimal.is.Any_GeAbs
import Lemma.Int.AbsMul.eq.MulAbsS
import Lemma.Nat.LeMulS.of.Le.Le.Ge_0.Ge_0
open Int Nat Hyperreal


@[main]
private lemma main
  {a b : ℝ*}
-- given
  (h_a : ¬Infinitesimal a)
  (h_b : ¬Infinitesimal b) :
-- imply
  ¬Infinitesimal (a * b) := by
-- proof
  apply NotInfinitesimal.of.Any_GeAbs
  let ⟨⟨δ_a, hδ_a⟩, h_a⟩ := Any_GeAbs.of.NotInfinitesimal h_a
  let ⟨⟨δ_b, hδ_b⟩, h_b⟩ := Any_GeAbs.of.NotInfinitesimal h_b
  use ⟨δ_a * δ_b, by simp_all⟩
  calc
    _ = _ := AbsMul.eq.MulAbsS a b
    _ ≥ _ := by
      simp
      apply GeMulS.of.Ge.Ge.Ge_0.Ge_0
      ·
        simp
      ·
        simp
        linarith
      ·
        simp_all
      ·
        simp_all


-- created on 2025-12-18
