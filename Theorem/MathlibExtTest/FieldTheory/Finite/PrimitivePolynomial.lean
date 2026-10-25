/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/FieldTheory/Finite/PrimitivePolynomial.lean -/


import Def.FieldTheory.Finite.PrimitivePolynomial
import Lemma.Polynomial.Finite.PrimitivePolynomial
import Mathlib.FieldTheory.Finite.GaloisField
set_option autoImplicit false

open scoped Polynomial


namespace Polynomial

variable {F : Type*} [Field F] [Finite F]

/-- Reconstruct from the three defining conditions. -/
example (f : F[X]) (h1 : f.Monic) (h2 : Irreducible f)
    (h3 : orderOf (AdjoinRoot.root f) = Nat.card F ^ f.natDegree - 1) :
    f.IsPrimitivePolynomial :=
  ⟨h1, h2, h3⟩

/-- Project the monic condition. -/
example (f : F[X]) (hf : f.IsPrimitivePolynomial) : f.Monic :=
  hf.monic

/-- Project the irreducible condition. -/
example (f : F[X]) (hf : f.IsPrimitivePolynomial) : Irreducible f :=
  hf.irreducible

/-- Project the root order condition. -/
example (f : F[X]) (hf : f.IsPrimitivePolynomial) :
    orderOf (AdjoinRoot.root f) = Nat.card F ^ f.natDegree - 1 :=
  hf.root_orderOf

/-- Rewrite through the defining equivalence. -/
example (f : F[X]) :
    f.IsPrimitivePolynomial ↔ f.Monic ∧ Irreducible f ∧
      orderOf (AdjoinRoot.root f) = Nat.card F ^ f.natDegree - 1 :=
  IsPrimitivePolynomial.iff

/-- Use the primitive-root characterization. -/
example (f : F[X]) :
    f.IsPrimitivePolynomial ↔ f.Monic ∧ Irreducible f ∧
      IsPrimitiveRoot (AdjoinRoot.root f)
        (Nat.card F ^ f.natDegree - 1) :=
  IsPrimitivePolynomial.iff_isPrimitiveRoot

variable (p : ℕ) [Fact p.Prime]

/-- Check the exact `ZMod p` specialization. -/
example (f : (ZMod p)[X]) (hf : f.IsPrimitivePolynomial) :
    f.Monic ∧ Irreducible f ∧
      orderOf (AdjoinRoot.root f) = p ^ f.natDegree - 1 :=
  (IsPrimitivePolynomial.zmod_iff p f).mp hf

variable (n : ℕ)

/-- The public predicate instantiates for a Galois field without choosing a `Fintype`. -/
example (f : (GaloisField p n)[X]) :
    f.IsPrimitivePolynomial ↔ f.Monic ∧ Irreducible f ∧
      orderOf (AdjoinRoot.root f) =
        Nat.card (GaloisField p n) ^ f.natDegree - 1 :=
  IsPrimitivePolynomial.iff

end Polynomial
