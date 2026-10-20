/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/Finite/PrimitivePolynomial.lean -/

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Primitive polynomials over finite fields

Reusable finite-field version of ATLAS Definition 3.14.
Distinct from `Polynomial.IsPrimitive`, which means primitive content.
-/

set_option autoImplicit false

open scoped Polynomial

namespace Polynomial

variable {F : Type*} [Field F]

/-- Monic irreducible polynomial whose root has maximal order. -/
def IsPrimitivePolynomial [Finite F] (f : F[X]) : Prop :=
  f.Monic ∧ Irreducible f ∧
    orderOf (AdjoinRoot.root f) = Nat.card F ^ f.natDegree - 1

variable [Finite F]

/-- A primitive polynomial is monic. -/
theorem IsPrimitivePolynomial.monic {f : F[X]}
    (hf : f.IsPrimitivePolynomial) : f.Monic :=
  hf.1

/-- A primitive polynomial is irreducible. -/
theorem IsPrimitivePolynomial.irreducible {f : F[X]}
    (hf : f.IsPrimitivePolynomial) : Irreducible f :=
  hf.2.1

/-- The root of a primitive polynomial has maximal order. -/
theorem IsPrimitivePolynomial.root_orderOf {f : F[X]}
    (hf : f.IsPrimitivePolynomial) :
    orderOf (AdjoinRoot.root f) = Nat.card F ^ f.natDegree - 1 :=
  hf.2.2

/-- Restatement of the defining conjunction. -/
theorem IsPrimitivePolynomial.iff {f : F[X]} :
    f.IsPrimitivePolynomial ↔ f.Monic ∧ Irreducible f ∧
      orderOf (AdjoinRoot.root f) = Nat.card F ^ f.natDegree - 1 :=
  Iff.rfl

/-- Characterization via primitive roots. -/
theorem IsPrimitivePolynomial.iff_isPrimitiveRoot {f : F[X]} :
    f.IsPrimitivePolynomial ↔ f.Monic ∧ Irreducible f ∧
      IsPrimitiveRoot (AdjoinRoot.root f)
        (Nat.card F ^ f.natDegree - 1) := by
  unfold IsPrimitivePolynomial
  exact and_congr Iff.rfl
    (and_congr Iff.rfl (IsPrimitiveRoot.iff_orderOf).symm)

variable (p : ℕ) [Fact p.Prime]

/-- Exact `ZMod p` specialization recovering ATLAS Definition 3.14. -/
theorem IsPrimitivePolynomial.zmod_iff (f : (ZMod p)[X]) :
    f.IsPrimitivePolynomial ↔ f.Monic ∧ Irreducible f ∧
      orderOf (AdjoinRoot.root f) = p ^ f.natDegree - 1 := by
  unfold IsPrimitivePolynomial
  rw [Nat.card_eq_fintype_card, ZMod.card p]

end Polynomial
