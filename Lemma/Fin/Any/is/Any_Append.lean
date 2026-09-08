import Mathlib.Data.Fin.Tuple.Basic
import sympy.Basic


@[main, comm, mp, mpr]
private lemma append
  {m k : ℕ}
  {α : Type*}
  {p : (Fin (m + k) → α) → Prop} :
-- imply
  (∃ w : Fin (m + k) → α, p w) ↔ ∃ (u : Fin m → α) (v : Fin k → α), p (Fin.append u v) := by
-- proof
  constructor
  ·
    rintro ⟨w, h⟩
    refine ⟨fun i => w (Fin.castAdd k i), fun j => w (Fin.natAdd m j), ?_⟩
    convert h
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    ·
      simp [Fin.append_left]
    ·
      simp [Fin.append_right]
  ·
    rintro ⟨u, v, h⟩
    exact ⟨Fin.append u v, h⟩


-- created on 2026-09-08
