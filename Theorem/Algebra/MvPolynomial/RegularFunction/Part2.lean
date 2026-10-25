import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Matrix.Basic
import Def.Algebra.MvPolynomial.RegularFunction.Part2
/-!
# Regular functions between affine spaces

A *regular function* from `k^σ` to `k^τ` is a `τ`-indexed family of polynomials in
the variables `σ`, i.e. a vector valued polynomial function. This file provides
the basic API: the Jacobian matrix, composition, the identity, and evaluation at
a point.
-/


noncomputable section

namespace MvPolynomial

variable {k : Type*} [CommSemiring k]

variable {σ τ ι κ : Type*}

namespace RegularFunction

@[simp]
theorem comp_apply (G : RegularFunction k τ ι) (F : RegularFunction k σ τ) (i : ι) :
    (G.comp F) i = MvPolynomial.bind₁ F (G i) :=
  rfl

@[simp]
theorem id_apply (i : σ) : id k σ i = MvPolynomial.X i :=
  rfl

/-- Composing with the identity on the left is the identity. -/
theorem id_comp (F : RegularFunction k σ τ) : (id k τ).comp F = F := by
  funext j
  simp

/-- Composing with the identity on the right is the identity. -/
theorem comp_id (F : RegularFunction k σ τ) : F.comp (id k σ) = F := by
  funext j
  simp only [comp_apply]
  have hid : (id k σ : σ → MvPolynomial σ k) = MvPolynomial.X :=
    funext fun i => id_apply (k := k) i
  rw [hid, MvPolynomial.bind₁_X_left]
  rfl

/-- Composition of regular functions is associative. -/
theorem comp_assoc (H : RegularFunction k ι κ) (G : RegularFunction k τ ι)
    (F : RegularFunction k σ τ) :
    (H.comp G).comp F = H.comp (G.comp F) := by
  funext i
  simp only [comp_apply]
  exact MvPolynomial.bind₁_bind₁ G F (H i)

end RegularFunction
end MvPolynomial
end
