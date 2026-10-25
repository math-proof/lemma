/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Algebra/Polynomial/FormalOrthogonality.lean -/


import Def.Algebra.Polynomial.FormalOrthogonality


namespace MetaMathlibExt.Polynomial

/-- Unfolding check: the witness also supplies every degree clause. -/
example {R : Type*} [Field R] (p : ℕ → Polynomial R)
    (h : IsFormallyOrthogonal p) :
    ∀ n, (p n).natDegree = n := by
  unfold IsFormallyOrthogonal at h
  obtain ⟨_, hdeg, _, _⟩ := h
  exact hdeg

/-- Off-diagonal projection: the witness kills mixed products. -/
example {R : Type*} [Field R] (p : ℕ → Polynomial R)
    (h : IsFormallyOrthogonal p) {n m : ℕ} (hnm : n ≠ m) :
    ∃ L : Polynomial R →ₗ[R] R, L (p n * p m) = 0 := by
  obtain ⟨L, _, horth, _⟩ := h
  exact ⟨L, horth n m hnm⟩

/-- Diagonal projection: the witness does not kill any square. -/
example {R : Type*} [Field R] (p : ℕ → Polynomial R)
    (h : IsFormallyOrthogonal p) (n : ℕ) :
    ∃ L : Polynomial R →ₗ[R] R, L (p n ^ 2) ≠ 0 := by
  obtain ⟨L, _, _, hdiag⟩ := h
  exact ⟨L, hdiag n⟩

end MetaMathlibExt.Polynomial
