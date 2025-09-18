import Lemma.Algebra.LtMod.of.Ne_0
import Lemma.Algebra.Le.of.Lt.Le
import Lemma.Algebra.Mod.eq.Sub_MulDiv
open Algebra


@[main]
private lemma main
  {d : ℕ} :
-- imply
  n ≥ n % d := by
-- proof
  by_cases h_d : d = 0
  ·
    subst h_d
    simp
  ·
    by_cases h_n : n ≥ d
    ·
      apply Le.of.Lt.Le h_n
      apply LtMod.of.Ne_0 h_d n
    ·
      simp at h_n
      rw [Mod.eq.Sub_MulDiv]
      simp [h_n]


-- created on 2025-07-09
