/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/AlgebraicGeometry/Affine/DefinedOver.lean -/


import sympy.atlas.AlgebraicGeometry.Affine.DefinedOver

/-!
Focused tests for `MathlibExt.AlgebraicGeometry.Affine.DefinedOver`.
-/


set_option autoImplicit false

noncomputable section

namespace MvPolynomial

variable {k : Type*} [Field k] {n : ℕ}

example (Z : Set (Fin n → AlgebraicClosure k))
    (f : MvPolynomial (Fin n) k) :
    f ∈ idealOverK Z ↔
      MvPolynomial.map (algebraMap k (AlgebraicClosure k)) f ∈
        MvPolynomial.vanishingIdeal (AlgebraicClosure k) Z :=
  mem_idealOverK_iff

example (Z : Set (Fin n → AlgebraicClosure k))
    (f : MvPolynomial (Fin n) k) (P : Fin n → AlgebraicClosure k)
    (hf : f ∈ idealOverK Z) (hP : P ∈ Z) :
    MvPolynomial.eval P
      (MvPolynomial.map (algebraMap k (AlgebraicClosure k)) f) = 0 :=
  eval_of_mem_idealOverK hf hP

example : idealOverK (∅ : Set (Fin n → AlgebraicClosure k)) = ⊤ :=
  idealOverK_empty n

example (Z₁ Z₂ : Set (Fin n → AlgebraicClosure k)) (h : Z₁ ⊆ Z₂) :
    idealOverK Z₂ ≤ idealOverK Z₁ :=
  idealOverK_anti_mono h

example : IsDefinedOver (∅ : Set (Fin n → AlgebraicClosure k)) := by
  unfold IsDefinedOver
  rw [MvPolynomial.vanishingIdeal_empty, idealOverK_empty, Ideal.map_top]

end MvPolynomial
