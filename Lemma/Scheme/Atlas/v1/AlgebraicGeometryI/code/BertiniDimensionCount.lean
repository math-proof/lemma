import Mathlib
import sympy.Basic
import Structure.v1.Atlas.AlgebraicGeometryI.code.BertiniDimensionCount.Part2
open BertiniArithmetic


namespace BertiniArithmetic

/--
[incidence_dim_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BertiniDimensionCount.lean)
-/
@[path]
lemma incidence_dim_eq
  {d n : ℕ}
-- given
  (hdn : d < n) :
-- imply
  incidenceDim d n = n - 1 := by
-- proof
  simp [incidenceDim, fiberDim]; omega

end BertiniArithmetic

namespace BertiniArithmetic

/--
[incidence_dim_lt_dual](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BertiniDimensionCount.lean)
-/
@[path]
lemma incidence_dim_lt_dual
  {d n : ℕ}
-- given
  (hdn : d < n) :
-- imply
  incidenceDim d n < dualDim n := by
-- proof
  simp [incidenceDim, fiberDim, dualDim]; omega

end BertiniArithmetic

namespace BertiniArithmetic

/--
[bertini_codimension_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BertiniDimensionCount.lean)
-/
@[path]
lemma bertini_codimension_bound
  {d n : ℕ}
-- given
  (hdn : d < n) :
-- imply
  dualDim n - incidenceDim d n ≥ 1 := by
-- proof
  simp [dualDim, incidenceDim, fiberDim]; omega

end BertiniArithmetic

namespace BertiniArithmetic

/--
[pred_lt_of_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BertiniDimensionCount.lean)
-/
@[path]
lemma pred_lt_of_pos
  {n : ℕ}
-- given
  (hn : 0 < n) :
-- imply
  n - 1 < n := by
-- proof
omega

end BertiniArithmetic

/--
[exists_not_mem_of_ne_univ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BertiniDimensionCount.lean)
-/
@[path]
lemma exists_not_mem_of_ne_univ
  {Z : Set X}
-- given
  (hne : Z ≠ Set.univ) :
-- imply
  ∃ x : X, x ∉ Z := by
-- proof
  by_contra h
  push Not at h
  exact hne (Set.eq_univ_of_forall h)
set_option linter.unusedVariables false in

/--
[bertini_projective_chevalley_gap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BertiniDimensionCount.lean)
-/
@[path]
lemma bertini_projective_chevalley_gap
  {HyperplaneIndex : Type}
  {n d : ℕ}
-- given
  (isBadLocus : HyperplaneIndex → Prop)
  (hdn : d < n)
  (h_incidence_dim : d + (n - d - 1) = n - 1)
  (h_incidence_lt : n - 1 < n)
  (h_bad_proper : {H | isBadLocus H} ≠ Set.univ) :
-- imply
  ∃ H : HyperplaneIndex, ¬ isBadLocus H :=
-- proof
  exists_not_mem_of_ne_univ h_bad_proper


-- created on 2026-10-23
