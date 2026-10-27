/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/TangentSpace.lean -/


import Theorem.AlgebraicGeometry.TangentSpace
set_option autoImplicit false

variable {k : Type*} [Field k] {n : Nat}

open MvPolynomial

/-! Tests for the translated tangent-space construction. -/


-- (1a) The zero polynomial has vanishing total derivative.
example (P v : Fin n → k) :
    totalDerivativeAt (0 : MvPolynomial (Fin n) k) P v = 0 := by
  simp [totalDerivativeAt, map_zero]

-- (1b) The tangent space of `0` is everything.
example (P : Fin n → k) :
    tangentSpacePoly (0 : MvPolynomial (Fin n) k) P = ⊤ := by
  rw [eq_top_iff]
  intro v _
  rw [mem_tangentSpacePoly]
  simp [totalDerivativeAt, map_zero]

-- (2a) The coordinate polynomial differentiates to the coordinate projection.
example (i : Fin n) (P v : Fin n → k) :
    totalDerivativeAt (MvPolynomial.X i : MvPolynomial (Fin n) k) P v = v i := by
  have h0 : ∀ j ∈ (Finset.univ : Finset (Fin n)), j ≠ i →
      MvPolynomial.eval P (MvPolynomial.pderiv j (MvPolynomial.X i)) * v j = 0 := by
    intro j _ hji
    rw [MvPolynomial.pderiv_X_of_ne hji.symm]
    simp
  have h1 : i ∉ (Finset.univ : Finset (Fin n)) →
      MvPolynomial.eval P (MvPolynomial.pderiv i (MvPolynomial.X i)) * v i = 0 := by
    intro h
    exact absurd (Finset.mem_univ i) h
  unfold totalDerivativeAt
  rw [Finset.sum_eq_single i h0 h1, MvPolynomial.pderiv_X_self]
  simp

-- (2b) The kernel for `X i` is the coordinate hyperplane.
example (i : Fin n) (P : Fin n → k) (v : Fin n → k) :
    v ∈ tangentSpacePoly (MvPolynomial.X i : MvPolynomial (Fin n) k) P ↔ v i = 0 := by
  rw [mem_tangentSpacePoly]
  have hderiv : totalDerivativeAt (MvPolynomial.X i : MvPolynomial (Fin n) k) P v
      = v i := by
    have h0 : ∀ j ∈ (Finset.univ : Finset (Fin n)), j ≠ i →
        MvPolynomial.eval P (MvPolynomial.pderiv j (MvPolynomial.X i)) * v j
          = 0 := by
      intro j _ hji
      rw [MvPolynomial.pderiv_X_of_ne hji.symm]
      simp
    have h1 : i ∉ (Finset.univ : Finset (Fin n)) →
        MvPolynomial.eval P (MvPolynomial.pderiv i (MvPolynomial.X i)) * v i
          = 0 := by
      intro h
      exact absurd (Finset.mem_univ i) h
    unfold totalDerivativeAt
    rw [Finset.sum_eq_single i h0 h1, MvPolynomial.pderiv_X_self]
    simp
  rw [hderiv]

-- (3a) The `iInf` tangent space of the principal coordinate ideal lies in the
-- generator's tangent space. This uses the `iInf` lattice API directly.
example (i : Fin n) (P : Fin n → k) :
    tangentSpaceIdeal (Ideal.span {(MvPolynomial.X i : MvPolynomial (Fin n) k)}) P ≤
      tangentSpacePoly (MvPolynomial.X i : MvPolynomial (Fin n) k) P := by
  unfold tangentSpaceIdeal
  exact le_trans
    (iInf_le _ (MvPolynomial.X i : MvPolynomial (Fin n) k))
    (iInf_le _ (Ideal.subset_span (Set.mem_singleton _)))

-- (3b) Membership in the principal coordinate ideal tangent space forces the
-- coordinate to vanish, via the `iInf` upper bound above.
example (i : Fin n) (P : Fin n → k) (v : Fin n → k)
    (hv : v ∈ tangentSpaceIdeal
      (Ideal.span {(MvPolynomial.X i : MvPolynomial (Fin n) k)}) P) :
    v i = 0 := by
  have hle : tangentSpaceIdeal
        (Ideal.span {(MvPolynomial.X i : MvPolynomial (Fin n) k)}) P ≤
      tangentSpacePoly (MvPolynomial.X i : MvPolynomial (Fin n) k) P :=
    by
      unfold tangentSpaceIdeal
      exact le_trans
        (iInf_le _ (MvPolynomial.X i : MvPolynomial (Fin n) k))
        (iInf_le _ (Ideal.subset_span (Set.mem_singleton _)))
  have hmem := hle hv
  rw [mem_tangentSpacePoly] at hmem
  have hderiv : totalDerivativeAt (MvPolynomial.X i : MvPolynomial (Fin n) k) P v
      = v i := by
    have h0 : ∀ j ∈ (Finset.univ : Finset (Fin n)), j ≠ i →
        MvPolynomial.eval P (MvPolynomial.pderiv j (MvPolynomial.X i)) * v j
          = 0 := by
      intro j _ hji
      rw [MvPolynomial.pderiv_X_of_ne hji.symm]
      simp
    have h1 : i ∉ (Finset.univ : Finset (Fin n)) →
        MvPolynomial.eval P (MvPolynomial.pderiv i (MvPolynomial.X i)) * v i
          = 0 := by
      intro h
      exact absurd (Finset.mem_univ i) h
    unfold totalDerivativeAt
    rw [Finset.sum_eq_single i h0 h1, MvPolynomial.pderiv_X_self]
    simp
  rw [hderiv] at hmem
  exact hmem

