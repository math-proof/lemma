/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matroid/Algebraic.lean -/

import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Def.Combinatorics.Matroid.Algebraic
universe u v w

/-! # Algebraic matroids

Following Matt Larson and Tuong Le, _Duals of algebraic matroids need not
be algebraic_ (arXiv:2609.02834v1), Introduction lines 57-59: a matroid is
algebraic if its independent sets are the algebraically independent subsets
of a field extension under a realization of the ground set.
-/


namespace Matroid

attribute [instance] AlgebraicRepresentation.field AlgebraicRepresentation.algebra
  AlgebraicRepresentation.faithful

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

end Matroid
