/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/PiFieldQuotient.lean -/

-- MathlibExt/RingTheory/PiFieldQuotient.lean

import Mathlib.Algebra.Algebra.Pi
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Operations
universe u v w

/-!
# Surjective algebra quotients of finite products of fields

Let `K` be a field, `ι` a finite type, `F : ι → Type*` a family of fields with
`K`-algebra structures, and `B` a commutative `K`-algebra. We show that any
surjective `K`-algebra homomorphism `(∀ i, F i) →ₐ[K] B` exhibits `B` as the
coordinate restriction to a subfamily: there is `S : Finset ι` and a
`K`-algebra equivalence `B ≃ₐ[K] (∀ i : S, F i)` commuting with restriction.

The proof analyzes the kernel: ideals of a product of fields are products of
ideals (`Ideal.piOrderIso`), each component ideal is `⊥` or `⊤`
(`Ideal.eq_bot_or_top`), and the first isomorphism theorem
(`Ideal.quotientKerAlgEquivOfSurjective`) identifies both `B` and the
restricted product with the quotient by that kernel. No finite-dimensionality,
separability, or nontriviality hypotheses are needed; the empty subfamily and
trivial targets work uniformly.
-/


namespace PiFieldQuotient

variable {K : Type u} [Field K]

variable {ι : Type*}

variable {F : ι → Type v} [∀ i, Field (F i)] [∀ i, Algebra K (F i)]

variable {B : Type w} [CommRing B] [Algebra K B]

/-- Coordinate restriction to a selected subfamily, as a `K`-algebra map. -/
def restrict (S : Finset ι) : (∀ i, F i) →ₐ[K] (∀ i : S, F i) :=
  AlgHom.pi (A := fun i : S => F (i : ι))
    (fun i : S => Pi.evalAlgHom K F (i : ι))

/-- The indices where the kernel of `φ` vanishes componentwise. -/
noncomputable def selected (φ : (∀ i, F i) →ₐ[K] B) : Finset ι := by
  classical
  haveI := Fintype.ofFinite ι
  exact Finset.univ.filter
    fun i => Ideal.map (Pi.evalRingHom _ i) (RingHom.ker φ) = ⊥

end PiFieldQuotient
