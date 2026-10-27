import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.FieldTheory.Finite.PrimitivePolynomial
open scoped Polynomial
open Polynomial


namespace Polynomial

/--
[IsPrimitivePolynomial.monic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/Finite/PrimitivePolynomial.lean)
-/
@[path]
lemma IsPrimitivePolynomial.monic
  [Field F] [Finite F]
  {f : F[X]}
-- given
  (hf : f.IsPrimitivePolynomial) :
-- imply
  f.Monic :=
-- proof
  hf.1

end Polynomial

namespace Polynomial

/--
[IsPrimitivePolynomial.irreducible](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/Finite/PrimitivePolynomial.lean)
-/
@[path]
lemma IsPrimitivePolynomial.irreducible
  [Field F] [Finite F]
  {f : F[X]}
-- given
  (hf : f.IsPrimitivePolynomial) :
-- imply
  Irreducible f :=
-- proof
  hf.2.1

end Polynomial

namespace Polynomial

/--
[IsPrimitivePolynomial.root_orderOf](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/Finite/PrimitivePolynomial.lean)
-/
@[path]
lemma IsPrimitivePolynomial.root_orderOf
  [Field F] [Finite F]
  {f : F[X]}
-- given
  (hf : f.IsPrimitivePolynomial) :
-- imply
  orderOf (AdjoinRoot.root f) = Nat.card F ^ f.natDegree - 1 :=
-- proof
  hf.2.2

end Polynomial

namespace Polynomial

/--
[IsPrimitivePolynomial.iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/Finite/PrimitivePolynomial.lean)
-/
@[path]
lemma IsPrimitivePolynomial.iff
  [Field F] [Finite F]
  {f : F[X]} :
-- imply
  f.IsPrimitivePolynomial ↔ f.Monic ∧ Irreducible f ∧
      orderOf (AdjoinRoot.root f) = Nat.card F ^ f.natDegree - 1 :=
-- proof
  Iff.rfl

end Polynomial

namespace Polynomial

/--
[IsPrimitivePolynomial.iff_isPrimitiveRoot](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/Finite/PrimitivePolynomial.lean)
-/
@[path]
lemma IsPrimitivePolynomial.iff_isPrimitiveRoot
  [Field F] [Finite F]
  {f : F[X]} :
-- imply
  f.IsPrimitivePolynomial ↔ f.Monic ∧ Irreducible f ∧
      IsPrimitiveRoot (AdjoinRoot.root f)
        (Nat.card F ^ f.natDegree - 1) := by
-- proof
  unfold IsPrimitivePolynomial
  exact and_congr Iff.rfl
    (and_congr Iff.rfl (IsPrimitiveRoot.iff_orderOf).symm)

end Polynomial

namespace Polynomial

/--
[IsPrimitivePolynomial.zmod_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/Finite/PrimitivePolynomial.lean)
-/
@[path]
lemma IsPrimitivePolynomial.zmod_iff
  [Field F] [Finite F]
  {p : ℕ} [Fact p.Prime]
  {f : (ZMod p)[X]} :
-- imply
  f.IsPrimitivePolynomial ↔ f.Monic ∧ Irreducible f ∧
      orderOf (AdjoinRoot.root f) = p ^ f.natDegree - 1 := by
-- proof
  unfold IsPrimitivePolynomial
  rw [Nat.card_eq_fintype_card, ZMod.card p]

end Polynomial


-- created on 2026-10-20
-- updated on 2026-10-26
