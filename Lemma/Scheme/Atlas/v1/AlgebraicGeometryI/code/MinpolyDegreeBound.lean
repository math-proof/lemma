import Mathlib
import Initialize.Tactic.Attr.Basic
open Polynomial IntermediateField Module


/--
[minpoly_natDegree_le_finrank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/MinpolyDegreeBound.lean)
-/
@[path]
lemma minpoly_natDegree_le_finrank
  [Field K]
  [Field L]
  [Algebra K L]
  {α : L}
  [FiniteDimensional K L] :
-- imply
  (minpoly K α).natDegree ≤ finrank K L :=
-- proof
  minpoly.natDegree_le α

/--
[minpoly_degree_le_finrank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/MinpolyDegreeBound.lean)
-/
@[path]
lemma minpoly_degree_le_finrank
  [Field K]
  [Field L]
  [Algebra K L]
  {α : L}
  [FiniteDimensional K L] :
-- imply
  (minpoly K α).degree ≤ ↑(finrank K L) :=
-- proof
  minpoly.degree_le α

/--
[minpoly_natDegree_dvd_finrank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/MinpolyDegreeBound.lean)
-/
@[path]
lemma minpoly_natDegree_dvd_finrank
  [Field K]
  [Field L]
  [Algebra K L]
  {α : L}
  [FiniteDimensional K L] :
-- imply
  (minpoly K α).natDegree ∣ finrank K L :=
-- proof
  minpoly.degree_dvd (IsIntegral.of_finite K α)


-- created on 2026-10-23
