import Lemma.Hyperreal.NotInfinitesimal.is.Any_GeAbs
import Lemma.Int.AbsMul.eq.MulAbsS
import Lemma.Nat.LeMulS.of.Le.Le.Ge_0.Ge_0
open Int Nat Hyperreal


@[main, mt]
private lemma main
  {a b : ℝ*}
-- given
  (h_a : ¬a → 0)
  (h_b : (a * b) → 0) :
-- imply
  b → 0 := by
-- proof
  contrapose! h_b
  suffices ¬((a * b) → 0) by grind
  apply NotInfinitesimal.of.Any_GeAbs
  let ⟨⟨δ_a, hδ_a⟩, h_a⟩ := Any_GeAbs.of.NotInfinitesimal h_a
  let ⟨⟨δ_b, hδ_b⟩, h_b⟩ := Any_GeAbs.of.NotInfinitesimal (not_lt.mpr h_b)
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
