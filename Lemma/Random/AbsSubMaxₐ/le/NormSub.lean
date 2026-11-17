import Class.Dynamics.QLearning
import Lemma.Finset.AbsSubSup'.le.Sup'AbsSub.of.Nonempty
import Initialize.Tactic.Attr.Basic
open Finset

@[path]
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
-- updated on 2026-11-17
