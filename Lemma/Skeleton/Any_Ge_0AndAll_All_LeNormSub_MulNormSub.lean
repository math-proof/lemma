import sympy.stats.markov_samples
import sympy.Basic


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]
  {d : ℕ}
  {sk : Skeleton S d} :
-- imply
  ∃ C, 0 ≤ C ∧ ∀ w w' y, ‖sk.G w y - sk.G w' y‖ ≤ C * ‖w - w'‖ := by
-- proof
  obtain ⟨C, hC, h⟩ := sk.hFlip
  refine ⟨C + 1, by positivity, fun w w' y => ?_⟩
  calc _ = ‖sk.F w y - sk.F w' y - (w - w')‖ := by rw [Skeleton.G, Skeleton.G, sub_sub_sub_comm]
    _ ≤ ‖sk.F w y - sk.F w' y‖ + ‖w - w'‖ := norm_sub_le _ _
    _ ≤ C * ‖w - w'‖ + ‖w - w'‖ := by gcongr; exact h w w' y
    _ = _ := by ring


-- created on 2026-09-26