import Mathlib.Data.Fin.Basic
import sympy.Basic


/--
Splitting a finite vector at `n < m`: equality of the whole vector is the conjunction of the prefix
and suffix equalities, so the two events have the same probability.
-/
@[path]
private lemma main
  {n m : ℕ}
  (x : Ω → Fin m → α)
  (v : Fin m → α)
-- given
  (h₀ : n < m) :
-- imply
  {ω | x ω = v} =
    {ω | ∀ i : Fin n, x ω (Fin.castLE h₀.le i) = v (Fin.castLE h₀.le i)} ∩
    {ω | ∀ j : Fin (m - n),
      x ω (Fin.cast (Nat.sub_add_cancel h₀.le) (j.addNat n)) =
        v (Fin.cast (Nat.sub_add_cancel h₀.le) (j.addNat n))} := by
-- proof
  ext ω
  constructor
  ·
    intro h
    refine ⟨fun i => congrFun h _, fun j => congrFun h _⟩
  ·
    intro h
    ext k
    if hk : (k : ℕ) < n then
      have hk' : k = Fin.castLE h₀.le ⟨k, hk⟩ :=
        Fin.ext (by rw [Fin.val_castLE])
      rw [hk']
      apply h.1
    else
      have hle : n ≤ (k : ℕ) := by omega
      let j : Fin (m - n) := ⟨(k : ℕ) - n, by omega⟩
      have hval : (k : ℕ) = ↑(Fin.cast (Nat.sub_add_cancel h₀.le) (j.addNat n)) := by
        rw [Fin.val_cast, Fin.val_addNat]
        show (k : ℕ) = ((k : ℕ) - n) + n
        omega
      rw [Fin.ext hval]
      apply h.2 j


-- created on 2023-03-26
-- updated on 2026-10-17
