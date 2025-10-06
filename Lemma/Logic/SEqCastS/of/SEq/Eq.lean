import stdlib.SEq
import Lemma.Logic.EqCastS.of.SEq.Eq
open Logic


@[main, comm 2]
private lemma left
  {Vector : α → Sort v}
  {a : Vector n_a}
  {b : Vector n_b}
-- given
  (h_a : n_a = n)
  (h_eq : a ≃ b) :
-- imply
  cast (congr_arg Vector h_a) a ≃ cast (congr_arg Vector (show n_b = n by rwa [← h_eq.left])) b := by
-- proof
  have := EqCastS.of.SEq.Eq.left h_a h_eq
  aesop


@[main, comm 2]
private lemma main
  {Vector : α → Sort v}
  {a : Vector n_a}
  {b : Vector n_b}
-- given
  (h_b : n_b = n)
  (h_eq : a ≃ b) :
-- imply
  cast (congr_arg Vector (show n_a = n by rwa [h_eq.left])) a ≃ cast (congr_arg Vector h_b) b := by
-- proof
  have := EqCastS.of.SEq.Eq h_b h_eq
  aesop


-- created on 2025-10-06
