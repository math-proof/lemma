import Lemma.Finset.SumSetOf.eq.Sum_UFnMul
import Lemma.Nat.Even.is.Any_Eq_Mul2
import Lemma.Nat.Even.is.Mod_2.eq.Zero
open Finset Nat


@[main]
private lemma main
  [AddCommMonoid α]
-- given
  (a b : ℤ)
  (f : ℤ → α) :
-- imply
  ∑ n ∈ {n ∈ Ico a b | n % 2 = 0}, f n = ∑ n ∈ Ico ((a + 1) / 2) ((b + 1) / 2), f (2 * n) := by
-- proof
  rw [Finset.sum_congr _ fun _ _ => rfl]
  ·
    convert SumSetOf.eq.Sum_UFnMul (by norm_num : (2 : ℤ) ≠ 0) (Ico ((a + 1) / 2) ((b + 1) / 2)) (fun _ => (1 : ℝ)) f using 2
    ext n
    simp
  ·
    ext n
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Ico]
    constructor
    ·
      intro ⟨hn, hev⟩
      obtain ⟨k, hk⟩ := Any_Eq_Mul2.of.Even (Even.of.Mod_2.eq.Zero hev)
      refine ⟨k, ?_, hk.symm⟩
      grind
    ·
      grind


-- created on 2018-05-28
-- updated on 2026-08-07
