/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matroid/Algebraic.lean -/

import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Structure.Combinatorics.Matroid.Algebraic.Part2
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

attribute [instance] AlgebraicRepresentationSomeField.fieldK
  AlgebraicRepresentationSomeField.fieldL AlgebraicRepresentationSomeField.algebra
  AlgebraicRepresentationSomeField.faithful

/-- `M` is algebraic if some same-universe realization exists.

Universe encoding: witness base and extension lie in `Type v`, giving the
universe-local form of algebraicity for `E : Type v`. -/
def IsAlgebraic {E : Type v} (M : Matroid E) : Prop :=
  Nonempty (AlgebraicRepresentationSomeField M)

end Matroid
