/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/InformationTheory/HammingBall.lean -/


import sympy.atlas.InformationTheory.HammingBall
import Lemma.Real.HammingBall

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F]

example (x y : ι → F) (e : ℕ) : y ∈ Hamming.ball x e ↔ hammingDist x y ≤ e := by
  simp

example (x : ι → F) : Hamming.ball x 0 = {x} := by
  ext y
  simp [Hamming.ball, eq_comm]

example (x : ι → F) (e : ℕ) (he : Fintype.card ι ≤ e) :
    Hamming.ball x e = Finset.univ := by
  ext y
  simp [Hamming.ball, (hammingDist_le_card_fintype.trans he)]

example (x : Fin 3 → Bool) : (Hamming.ball x 1).card = 4 := by
  rw [Hamming.card_ball]
  norm_num [Finset.sum_range_succ]

example (x : Fin 3 → Bool) : (Hamming.ball x 4).card = 8 := by
  rw [Hamming.card_ball]
  norm_num [Finset.sum_range_succ]

example (x : Fin 2 → Fin 3) : (Hamming.ball x 1).card = 5 := by
  calc
    (Hamming.ball x 1).card =
        ∑ k ∈ Finset.range (1 + 1), Nat.choose 2 k * (3 - 1) ^ k :=
      Hamming.card_ball_fin (by omega) (by simp) (by omega) x 1
    _ = 5 := by norm_num [Finset.sum_range_succ]

example (x : Fin 2 → Fin 3) : (Hamming.ball x 3).card = 9 := by
  rw [Hamming.card_ball]
  norm_num [Finset.sum_range_succ]
