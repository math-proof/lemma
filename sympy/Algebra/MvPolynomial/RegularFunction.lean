import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.MvPolynomial.PDeriv
import Mathlib.Data.Matrix.Basic

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

variable (k σ τ) in
/-- The type of regular functions from `k^σ` to `k^τ`. -/
abbrev RegularFunction := τ → MvPolynomial σ k

namespace RegularFunction

/-- The Jacobian of a vector valued polynomial function, viewed as a polynomial.

The matrix is indexed as codomain by domain, following Mathlib's matrix
convention: entry `(j, i)` is the partial derivative of the `j`-th component
with respect to the `i`-th variable. -/
noncomputable def Jacobian (F : RegularFunction k σ τ) :
    Matrix τ σ (MvPolynomial σ k) :=
  Matrix.of fun j i => MvPolynomial.pderiv i (F j)

@[simp]
theorem Jacobian_apply (F : RegularFunction k σ τ) (j : τ) (i : σ) :
    F.Jacobian j i = MvPolynomial.pderiv i (F j) :=
  rfl

/-- The composition of two vector valued polynomial functions. -/
noncomputable def comp
    (G : RegularFunction k τ ι) (F : RegularFunction k σ τ) :
    RegularFunction k σ ι :=
  fun (i : ι) ↦ MvPolynomial.bind₁ F (G i)

variable (k σ) in
noncomputable def id : RegularFunction k σ σ := MvPolynomial.X

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

/-- The evaluation of a regular function `f` over `k` at some point `a`
with coordinates in some algebra over `k`. -/
noncomputable def aeval {σ τ : Type*} {S₁ : Type*} [CommSemiring S₁] [Algebra k S₁]
    (F : RegularFunction k σ τ) : (σ → S₁) → τ → S₁ :=
  fun a t ↦ MvPolynomial.aeval a (F t)

/-- `aeval` is compatible with composition of regular functions. -/
theorem comp_aeval
    {σ τ ι S₁ : Type*} [CommSemiring S₁] [Algebra k S₁]
    (G : RegularFunction k τ ι) (F : RegularFunction k σ τ)
    (a : σ → S₁) : (G.comp F).aeval a = G.aeval (F.aeval a) := by
  ext i
  rw [aeval, comp, MvPolynomial.aeval_bind₁, ←aeval]
  rfl

end RegularFunction

end MvPolynomial
