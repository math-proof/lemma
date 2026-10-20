/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matroid/Algebraic.lean -/

import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-! # Algebraic matroids

Following Matt Larson and Tuong Le, _Duals of algebraic matroids need not
be algebraic_ (arXiv:2609.02834v1), Introduction lines 57-59: a matroid is
algebraic if its independent sets are the algebraically independent subsets
of a field extension under a realization of the ground set.
-/

universe u v w

namespace Matroid

/-- Realization of `M` over `K` with values in an extension `L`. -/
structure AlgebraicRepresentation (K : Type u) [Field K] {E : Type v}
    (M : Matroid E) where
  /-- Ambient extension field holding the realization. -/
  L : Type w
  /-- Field structure on the ambient extension. -/
  [field : Field L]
  /-- `K`-algebra structure on the ambient extension. -/
  [algebra : Algebra K L]
  /-- Faithfulness of the scalar action of `K` on `L`. -/
  [faithful : FaithfulSMul K L]
  /-- Map sending each ground-set element to `L`. -/
  realize : E → L
  /-- The realized ground set generates `L` over `K`. -/
  generates : IntermediateField.adjoin K (realize '' M.E) = ⊤
  /-- Independence in `M` matches algebraic independence in `L`. -/
  matroid_eq : M = (AlgebraicIndependent.matroid K L).comapOn M.E realize

attribute [instance] AlgebraicRepresentation.field AlgebraicRepresentation.algebra
  AlgebraicRepresentation.faithful

/-- `M` is algebraic over `K` if a representation exists in `max u v`.

Universe encoding: Lean fixes universes, so the witness extension is
required to live in `max u v`, holding both `K` and `E`. -/
def IsAlgebraicOver (K : Type u) [Field K] {E : Type v}
    (M : Matroid E) : Prop :=
  Nonempty (AlgebraicRepresentation.{u, v, max u v} K M)

/-- Self-contained realization with all field data in `Type v`.

Universe encoding: both base field `K` and extension `L` live in `Type v`,
so matroids on `E : Type v` need no larger universes. -/
structure AlgebraicRepresentationSomeField {E : Type v}
    (M : Matroid E) where
  /-- Base field of the realization, in the same universe as `E`. -/
  K : Type v
  /-- Field structure on the base field. -/
  [fieldK : Field K]
  /-- Extension field holding the realization. -/
  L : Type v
  /-- Field structure on the extension. -/
  [fieldL : Field L]
  /-- `K`-algebra structure on the extension. -/
  [algebra : Algebra K L]
  /-- Faithfulness of the scalar action of `K` on `L`. -/
  [faithful : FaithfulSMul K L]
  /-- Map sending each ground-set element to `L`. -/
  realize : E → L
  /-- The realized ground set generates `L` over `K`. -/
  generates : IntermediateField.adjoin K (realize '' M.E) = ⊤
  /-- Independence in `M` matches algebraic independence in `L`. -/
  matroid_eq : M = (AlgebraicIndependent.matroid K L).comapOn M.E realize

attribute [instance] AlgebraicRepresentationSomeField.fieldK
  AlgebraicRepresentationSomeField.fieldL AlgebraicRepresentationSomeField.algebra
  AlgebraicRepresentationSomeField.faithful

/-- `M` is algebraic if some same-universe realization exists.

Universe encoding: witness base and extension lie in `Type v`, giving the
universe-local form of algebraicity for `E : Type v`. -/
def IsAlgebraic {E : Type v} (M : Matroid E) : Prop :=
  Nonempty (AlgebraicRepresentationSomeField M)

/-- A representation in `max u v` witnesses algebraicity over `K`. -/
theorem AlgebraicRepresentation.toIsAlgebraicOver {K : Type u} [Field K]
    {E : Type v} {M : Matroid E}
    (self : AlgebraicRepresentation.{u, v, max u v} K M) :
    IsAlgebraicOver K M :=
  ⟨self⟩

/-- A same-universe package witnesses algebraicity of `M`. -/
theorem AlgebraicRepresentationSomeField.toIsAlgebraic {E : Type v}
    {M : Matroid E} (self : AlgebraicRepresentationSomeField M) :
    IsAlgebraic M :=
  ⟨self⟩

end Matroid
