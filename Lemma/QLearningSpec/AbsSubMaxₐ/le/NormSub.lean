import sympy.stats.q_learning
import sympy.Basic
import Lemma.Finset.AbsSubSup'.le.Sup'AbsSub.of.Nonempty
open Finset


@[main]
private lemma main
  {S A : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype A] [DecidableEq A] [MeasurableSpace A] [MeasurableSingletonClass A] [Nonempty A]
-- given
  (q q' : Fin (Fintype.card (S × A)) → ℝ)
  (s : S) :
-- imply
  |QLearningSpec.maxₐ q s - QLearningSpec.maxₐ q' s| ≤ ‖q - q'‖ :=
-- proof
  (Finset.AbsSubSup'.le.Sup'AbsSub.of.Nonempty univ_nonempty).trans (sup'_le _ _ fun a _ => by simpa using norm_le_pi_norm (q - q') (QLearningSpec.sa_to_fin (s, a)))


-- created on 2026-09-26
