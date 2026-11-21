import Instance.Data.Tensor.Tensor


/--
| attributes | lemma |
| :---: | :---: |
| path | Tensor.GetDite.eq.Get.of.Not |
| fin | Tensor.GetDite.eq.Get.of.Not.fin |
-/
@[path, fin]
private lemma main
  [Decidable c]
  {i : ℕ}
  {t : c → Tensor α s}
  {e : ¬c → Tensor α s}
-- given
  (h : ¬c)
  (h_i : i < (dite c t e).length) :
-- imply
  (dite c t e)[i]'h_i = (e h)[i]'(by simpa only [dite_eq_right h] using h_i) := by
-- proof
  simp only [dite_eq_right h]


-- created on 2026-07-04
-- updated on 2026-11-20
