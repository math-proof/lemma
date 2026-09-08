import Mathlib.Data.Fin.Tuple.Basic
import sympy.Basic


@[main, comm, mp, mpr]
private lemma main
  {n : ℕ}
  {α : Type*}
  {p : (Fin (n + 1) → α) → Prop} :
-- imply
  (∃ w : Fin (n + 1) → α, p w) ↔ ∃ (a : α) (v : Fin n → α), p (Fin.cons a v) :=
-- proof
  Fin.exists_fin_succ_pi (P := p)


-- created on 2023-11-18
-- updated on 2026-09-08
