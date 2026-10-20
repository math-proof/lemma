import Mathlib
import sympy.Basic
import sympy.atlas.FieldTheory.Finite.PrimitivePolynomial
open scoped Polynomial
open Polynomial


/--
[IsPrimitivePolynomial.monic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/Finite/PrimitivePolynomial.lean)
-/
@[path]
private lemma IsPrimitivePolynomial_monic_eq
  [Field F] [Finite F]
  {f : F[X]}
-- given
  (hf : f.IsPrimitivePolynomial) :
-- imply
  f.Monic := by
-- proof
  apply Polynomial.IsPrimitivePolynomial.monic hf

/--
[IsPrimitivePolynomial.irreducible](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/Finite/PrimitivePolynomial.lean)
-/
@[path]
private lemma IsPrimitivePolynomial_irreducible_eq
  [Field F] [Finite F]
  {f : F[X]}
-- given
  (hf : f.IsPrimitivePolynomial) :
-- imply
  Irreducible f := by
-- proof
  apply Polynomial.IsPrimitivePolynomial.irreducible hf

/--
[IsPrimitivePolynomial.root_orderOf](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/Finite/PrimitivePolynomial.lean)
-/
@[path]
private lemma IsPrimitivePolynomial_root_orderOf_eq
  [Field F] [Finite F]
  {f : F[X]}
-- given
  (hf : f.IsPrimitivePolynomial) :
-- imply
  orderOf (AdjoinRoot.root f) = Nat.card F ^ f.natDegree - 1 := by
-- proof
  apply Polynomial.IsPrimitivePolynomial.root_orderOf hf

/--
[IsPrimitivePolynomial.iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/Finite/PrimitivePolynomial.lean)
-/
@[path]
private lemma IsPrimitivePolynomial_iff_eq
  [Field F] [Finite F]
  {f : F[X]} :
-- imply
  f.IsPrimitivePolynomial ↔ f.Monic ∧ Irreducible f ∧
      orderOf (AdjoinRoot.root f) = Nat.card F ^ f.natDegree - 1 := by
-- proof
  apply Polynomial.IsPrimitivePolynomial.iff

/--
[IsPrimitivePolynomial.iff_isPrimitiveRoot](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/Finite/PrimitivePolynomial.lean)
-/
@[path]
private lemma IsPrimitivePolynomial_iff_isPrimitiveRoot_eq
  [Field F] [Finite F]
  {f : F[X]} :
-- imply
  f.IsPrimitivePolynomial ↔ f.Monic ∧ Irreducible f ∧
      IsPrimitiveRoot (AdjoinRoot.root f)
        (Nat.card F ^ f.natDegree - 1) := by
-- proof
  apply Polynomial.IsPrimitivePolynomial.iff_isPrimitiveRoot

/--
[IsPrimitivePolynomial.zmod_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/Finite/PrimitivePolynomial.lean)
-/
@[path]
private lemma IsPrimitivePolynomial_zmod_iff_eq
  [Field F] [Finite F]
  {p : ℕ} [Fact p.Prime]
  {f : (ZMod p)[X]} :
-- imply
  f.IsPrimitivePolynomial ↔ f.Monic ∧ Irreducible f ∧
      orderOf (AdjoinRoot.root f) = p ^ f.natDegree - 1 := by
-- proof
  apply Polynomial.IsPrimitivePolynomial.zmod_iff p f


-- created on 2026-10-20
