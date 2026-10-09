import sympy.Basic


@[path]
private lemma left_open
  [Preorder α]
  {x a b : α}
-- given
  (h : x ∈ Set.Ioo a b) :
-- imply
  x ∈ Set.Ico a b :=
-- proof
  Set.Ioo_subset_Ico_self h


@[path]
private lemma right_open
  [Preorder α]
  {x a b : α}
-- given
  (h : x ∈ Set.Ioo a b) :
-- imply
  x ∈ Set.Ioc a b :=
-- proof
  Set.Ioo_subset_Ioc_self h


@[path]
private lemma left_close
  [Preorder α]
  {x a b : α}
-- given
  (h : x ∈ Set.Ioo a b) :
-- imply
  x ∈ Set.Ico a b :=
-- proof
  Set.Ioo_subset_Ico_self h


@[path]
private lemma right_close
  [Preorder α]
  {x a b : α}
-- given
  (h : x ∈ Set.Ioo a b) :
-- imply
  x ∈ Set.Ioc a b :=
-- proof
  Set.Ioo_subset_Ioc_self h


@[path]
private lemma restrict.given
  {x : α}
  {A B : Set α}
-- given
  (h : x ∈ A ∩ B) :
-- imply
  x ∈ A :=
-- proof
  h.1


-- created on 2026-09-27
-- updated on 2026-09-27
