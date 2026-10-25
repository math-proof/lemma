/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matroid/Algebraic.lean -/

import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Structure.Combinatorics.Matroid.Algebraic
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

/-- `M` is algebraic over `K` if a representation exists in `max u v`.

Universe encoding: Lean fixes universes, so the witness extension is
required to live in `max u v`, holding both `K` and `E`. -/
def IsAlgebraicOver (K : Type u) [Field K] {E : Type v}
    (M : Matroid E) : Prop :=
  Nonempty (AlgebraicRepresentation.{u, v, max u v} K M)

end Matroid
