import Mathlib
import Theorem.Algebra.DirectLimit.Part4


namespace IsDirectLimit

variable {ι : Type*} [Preorder ι] {M : ι → Type*}

variable {P₁ P₂ : Type*}

namespace Module

variable {R : Type*} [Semiring R] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  {P : Type*} [AddCommMonoid P] [Module R P]
  (f : (i j : ι) → i ≤ j → M i →ₗ[R] M j)
  (g : ∀ i, M i →ₗ[R] P)
  [DirectedSystem M (fun i j h => ⇑(f i j h))]
  [IsDirectLimit (fun i j h => ⇑(f i j h)) (fun i => ⇑(g i))]
  [IsDirected ι (· ≤ ·)]

instance [DecidableEq ι] [Nonempty ι] :
    IsDirectLimit (fun i j h => ⇑(f i j h)) (fun i => ⇑(Module.DirectLimit.of R ι M f i)) where
  surj z := Module.DirectLimit.exists_of (R := R) (ι := ι) (G := M) (f := f) z
  inj := by
    intro i j mi mj h
    apply_fun Module.DirectLimit.linearEquiv (R := R) (ι := ι) (G := M) (f := f) at h
    simp_rw [Module.DirectLimit.linearEquiv_of, Quotient.eq] at h
    exact h
  compatibility := by
    intro i j hij x
    exact Module.DirectLimit.of_f (R := R) (ι := ι) (G := M) (f := f) (hij := hij) (x := x)

end Module
end IsDirectLimit
