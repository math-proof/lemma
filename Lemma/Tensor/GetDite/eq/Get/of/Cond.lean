import Instance.Data.Tensor.Tensor


/--
| attributes | lemma |
| :---: | :---: |
| path | Tensor.GetDite.eq.Get.of.Cond |
| fin | Tensor.GetDite.eq.Get.of.Cond.fin |
-/
@[path, fin]
private lemma main
  [Decidable c]
  {i : ℕ}
  {t : c → Tensor α s}
  {e : ¬c → Tensor α s}
-- given
  (h : c)
  (h_i : i < (dite c t e).length) :
-- imply
  (dite c t e)[i]'h_i = (t h)[i]'(by simpa only [dite_eq_left h] using h_i) := by
-- proof
  simp only [dite_eq_left h]


-- created on 2026-07-13
-- updated on 2026-11-20
