import sympy.Basic


@[main]
private lemma main
  [Add β]
  {f g : α → β}
  {t : α} :
-- imply
  (fun x => f x + g x) t = f t + g t :=
-- proof
  rfl


-- created on 2026-09-27
