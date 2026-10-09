import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| path | Bool.All.is.All.And.Conditionset |
| mp | Bool.All.And.Conditionset.of.All |
| mpr | Bool.All.of.All.And.Conditionset |
-/
@[path, mp, mpr]
private lemma main
  {A : Set α}
  {p c : α → Prop} :
-- imply
  (∀ x ∈ {x ∈ A | c x}, p x) ↔ ∀ x ∈ {x ∈ A | c x}, p x ∧ c x :=
-- proof
  ⟨fun h x hx => ⟨h x hx, hx.2⟩, fun h x hx => (h x hx).1⟩


-- created on 2026-10-07
