import sympy.tensor.Basic
import sympy.Basic


@[main, comm, mp, mpr]
private lemma main
  [Semiring α] [CharZero α]
  {m k : ℕ} :
-- imply
  (m : Tensor α []) = (k : Tensor α []) ↔ m = k := by
-- proof
  constructor
  ·
    intro h
    have hd := congrArg (fun t : Tensor α [] => t.data.get ⟨0, by simp⟩) h
    have hm : (m : Tensor α []).data.get ⟨0, by simp⟩ = (m : α) := by
      simp
      rfl
    have hk : (k : Tensor α []).data.get ⟨0, by simp⟩ = (k : α) := by
      simp
      rfl
    rw [hm, hk] at hd
    exact CharZero.cast_injective hd
  ·
    intro h
    rw [h]


-- created on 2026-09-10
