import sympy.stats.hidden_markov_sequence
import sympy.Basic


@[path]
private lemma main
  [Fintype Y]
  [Nonempty Y]
  {t : ℕ}
-- given
  (F : (Fin (t + 1) → Y) → ℝ) :
-- imply
  Finset.univ.sup' Finset.univ_nonempty F =
      Finset.univ.sup' Finset.univ_nonempty (fun b => Finset.univ.sup' Finset.univ_nonempty
        (fun ys0 : Fin t → Y => F (Fin.snoc (α := fun _ => Y) ys0 b))) := by
-- proof
  apply le_antisymm
  ·
    refine Finset.sup'_le _ _ fun ys _ => ?_
    refine Finset.le_sup'_of_le _ (Finset.mem_univ (ys (Fin.last t))) (Finset.le_sup'_of_le _ (Finset.mem_univ (Fin.init ys)) ?_)
    simp only [Fin.snoc_init_self, le_refl]
  · exact Finset.sup'_le _ _ fun b _ => Finset.sup'_le _ _ fun ys0 _ => Finset.le_sup' F (Finset.mem_univ _)


-- created on 2026-10-07
