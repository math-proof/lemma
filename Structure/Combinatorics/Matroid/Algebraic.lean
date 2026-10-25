/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matroid/Algebraic.lean -/

import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
universe u v w

/-! # Algebraic matroids

Following Matt Larson and Tuong Le, _Duals of algebraic matroids need not
be algebraic_ (arXiv:2609.02834v1), Introduction lines 57-59: a matroid is
algebraic if its independent sets are the algebraically independent subsets
of a field extension under a realization of the ground set.
-/


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

end Matroid
