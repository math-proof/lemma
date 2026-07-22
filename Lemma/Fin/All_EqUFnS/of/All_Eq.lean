import Lemma.Finset.All_EqUFnS.of.All_Eq
open Finset


@[main]
private lemma bin
  {a b : Fin n → α}
  {f : α → Fin n → β}
-- given
  (h : ∀ i : Fin n, a i = b i) :
-- imply
  ∀ i : Fin n, f (a i) i = f (b i) i := by
-- proof
  have := All_EqUFnS.of.All_Eq.bin (s := Finset.univ) (a := a) (b := b) (f := f)
  aesop


@[main]
private lemma main
  {a b : Fin n → β}
  {f : β → γ}
-- given
  (h : ∀ i : Fin n, a i = b i) :
-- imply
  ∀ i : Fin n, f (a i) = f (b i) := by
-- proof
  have := All_EqUFnS.of.All_Eq (s := Finset.univ) (a := a) (b := b) (f := f)
  aesop


@[main]
private lemma const
  {x : Fin n → α}
  {f : α → β}
-- given
  (h : ∀ i : Fin n, x i = a) :
-- imply
  ∀ i : Fin n, f (x i) = f a := by
-- proof
  have := All_EqUFnS.of.All_Eq.const (s := Finset.univ) (x := x) (f := f) (a := a)
  aesop


-- created on 2026-07-22
