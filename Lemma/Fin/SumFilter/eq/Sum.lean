import sympy.concrete.expr_with_limits
import sympy.Basic


/-- The band `i − l < j < i + u` of row `i` is the contiguous window `[β, ζ)`, `β = relu(i − l + 1)`, `ζ = min(n, i + u)`. -/
@[main]
private lemma main
  [AddCommMonoid M]
  {n : ℕ}
-- given
  (i : Fin n)
  (l u : ℕ)
  (g : Fin n → M) :
-- imply
  ∑ j ∈ Finset.univ.filter (fun j : Fin n => (i.val : ℤ) < (j.val : ℤ) + l ∧ (j.val : ℤ) < (i.val : ℤ) + u), g j =
      ∑ j' : Fin (min n (i.val + u) - (i.val + 1 - l)), g ⟨i.val + 1 - l + j', by have := j'.2; omega⟩ := by
-- proof
  symm
  apply Finset.sum_bij (fun (j' : Fin (min n (i.val + u) - (i.val + 1 - l))) _ => (⟨i.val + 1 - l + j'.val, by have := j'.2; omega⟩ : Fin n))
  ·
    intro j' _
    have := j'.2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  ·
    intro a _ b _ h
    simp only [Fin.mk.injEq] at h
    exact Fin.ext (by omega)
  ·
    intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    have := b.2
    exact ⟨⟨b.val - (i.val + 1 - l), by omega⟩, Finset.mem_univ _, Fin.ext (by simp only; omega)⟩
  ·
    intro _ _
    rfl


-- created on 2026-10-07
