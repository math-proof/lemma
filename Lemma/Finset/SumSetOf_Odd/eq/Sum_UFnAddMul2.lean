import Lemma.Finset.SumSetOf.eq.Sum_UFnAddMul
import Lemma.Nat.Odd.is.Any_Eq_AddMul2
import Lemma.Nat.Odd.is.Mod_2.eq.One
open Finset Nat


@[main]
private lemma main
  [AddCommMonoid α]
-- given
  (a b : ℤ)
  (f : ℤ → α) :
-- imply
  ∑ n ∈ {n ∈ Ico a b | n % 2 = 1}, f n = ∑ n ∈ Ico (a / 2) (b / 2), f (2 * n + 1) := by
-- proof
  rw [Finset.sum_congr _ fun _ _ => rfl]
  ·
    convert SumSetOf.eq.Sum_UFnAddMul (by norm_num : (2 : ℤ) ≠ 0) (Ico (a / 2) (b / 2)) (fun _ => (1 : ℝ)) f using 2
    ext n
    simp
  ·
    ext n
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Ico]
    constructor
    ·
      intro ⟨hn, hod⟩
      obtain ⟨k, hk⟩ := Any_Eq_AddMul2.of.Odd (Odd.of.Mod_2.eq.One hod)
      refine ⟨k, ?_, hk.symm⟩
      grind
    ·
      grind


-- created on 2018-06-01
-- updated on 2026-08-07
