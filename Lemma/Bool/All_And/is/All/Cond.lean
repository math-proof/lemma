import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Bool.All_And.is.All.Cond |
| comm | Bool.All.Cond.is.All_And |
| mp | Bool.All.Cond.of.All_And |
| mpr | Bool.All_And.of.All.Cond |
-/
@[main, comm, mp, mpr]
private lemma main
  [Nonempty α]
  {p : α → Prop}
  {q : Prop} :
-- imply
  (∀ x : α, p x ∧ q) ↔ (∀ x : α, p x) ∧ q :=
-- proof
  forall_and_right p q


@[main, comm, mp, mpr]
private lemma set
  {p : α → Prop}
  {q : Prop}
  {S : Set α}
-- given
  (h : S.Nonempty) :
-- imply
  (∀ x ∈ S, p x ∧ q) ↔ (∀ x ∈ S, p x) ∧ q := by
-- proof
  constructor
  ·
    intro h_all
    obtain ⟨x, hx⟩ := h
    exact ⟨fun y hy => (h_all y hy).left, (h_all x hx).right⟩
  ·
    intro ⟨hp, hq⟩ x hx
    exact ⟨hp x hx, hq⟩


@[main, comm, mp, mpr]
private lemma finset
  {p : α → Prop}
  {q : Prop}
  {S : Finset α}
-- given
  (h : S.Nonempty) :
-- imply
  (∀ x ∈ S, p x ∧ q) ↔ (∀ x ∈ S, p x) ∧ q := by
-- proof
  constructor
  ·
    intro h_all
    obtain ⟨x, hx⟩ := h
    exact ⟨fun y hy => (h_all y hy).left, (h_all x hx).right⟩
  ·
    intro ⟨hp, hq⟩ x hx
    exact ⟨hp x hx, hq⟩


-- created on 2018-12-24
-- updated on 2026-09-07
