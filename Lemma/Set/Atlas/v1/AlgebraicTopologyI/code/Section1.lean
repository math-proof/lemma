import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicTopologyI.code.Section1
open AlgebraicTopologyI
open Finset AlgebraicTopology CategoryTheory


namespace AlgebraicTopologyI

/--
[singularChainsZ_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section1.lean)
-/
@[path]
lemma singularChainsZ_neg
  {n : ℤ}
  {X : Type*}
  [TopologicalSpace X]
-- given
  (hn : n < 0) :
-- imply
  SingularChainsZ n X = PUnit := by
-- proof
  simp [SingularChainsZ, show ¬(n ≥ 0) from not_le.mpr hn]

end AlgebraicTopologyI

namespace AlgebraicTopologyI

/--
[singular_d_comp_d](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section1.lean)
-/
@[path]
lemma singular_d_comp_d
  {X : TopCat.{0}}
  {i j k : ℕ} :
-- imply
  (singularChainComplexZ X).d i j ≫ (singularChainComplexZ X).d j k = 0 :=
-- proof
  (singularChainComplexZ X).d_comp_d i j k

end AlgebraicTopologyI

namespace AlgebraicTopologyI

/--
[singularHomologyGroup_eq_homology](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section1.lean)
-/
@[path]
lemma singularHomologyGroup_eq_homology
  {n : ℕ}
  {X : Type}
  [TopologicalSpace X] :
-- imply
  SingularHomologyGroup n X = (singularChainComplexZ (TopCat.of X)).homology n :=
-- proof
  rfl

end AlgebraicTopologyI


-- created on 2026-10-23
