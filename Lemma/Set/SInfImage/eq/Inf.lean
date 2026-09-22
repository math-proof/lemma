import sympy.Basic


@[main]
private lemma main
  [InfSet α]
  {f : β → α}
  {s : Set β} :
-- imply
  sInf (f '' s) = ⨅ x : s, f x :=
-- proof
  sInf_image'


-- created on 2019-01-16
-- updated on 2026-09-22
