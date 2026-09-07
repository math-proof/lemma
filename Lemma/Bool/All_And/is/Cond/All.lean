import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Bool.All_And.is.Cond.All |
| comm | Bool.Cond.All.is.All_And |
| mp | Bool.Cond.All.of.All_And |
| mpr | Bool.All_And.of.Cond.All |
-/
@[main, comm, mp, mpr]
private lemma main
  [Nonempty α]
  {p : Prop}
  {q : α → Prop} :
-- imply
  (∀ x : α, p ∧ q x) ↔ p ∧ ∀ x : α, q x :=
-- proof
  forall_and_left p q


@[main, comm, mp, mpr]
private lemma set
  {p : Prop}
  {q : α → Prop}
  {S : Set α}
-- given
  (h : S.Nonempty) :
-- imply
  (∀ x ∈ S, p ∧ q x) ↔ p ∧ ∀ x ∈ S, q x := by
-- proof
  constructor
  ·
    intro h_all
    obtain ⟨x, hx⟩ := h
    exact ⟨(h_all x hx).left, fun y hy => (h_all y hy).right⟩
  ·
    intro ⟨hp, hq⟩ x hx
    exact ⟨hp, hq x hx⟩


@[main, comm, mp, mpr]
private lemma finset
  {p : Prop}
  {q : α → Prop}
  {S : Finset α}
-- given
  (h : S.Nonempty) :
-- imply
  (∀ x ∈ S, p ∧ q x) ↔ p ∧ ∀ x ∈ S, q x := by
-- proof
  constructor
  ·
    intro h_all
    obtain ⟨x, hx⟩ := h
    exact ⟨(h_all x hx).left, fun y hy => (h_all y hy).right⟩
  ·
    intro ⟨hp, hq⟩ x hx
    exact ⟨hp, hq x hx⟩


-- created on 2018-12-24
-- updated on 2026-09-07
