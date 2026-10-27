import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.BlowupReesConnection
open Polynomial BlowupReesConnection


namespace BlowupReesConnection

/--
[x_mem_originIdeal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BlowupReesConnection.lean)
-/
@[path]
lemma x_mem_originIdeal
  {k : Type*}
  [CommRing k] :
-- imply
  (C (X : Polynomial k) : Polynomial (Polynomial k)) ∈ originIdeal k :=
-- proof
  Ideal.subset_span (Set.mem_insert _ _)

end BlowupReesConnection

namespace BlowupReesConnection

/--
[y_mem_originIdeal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BlowupReesConnection.lean)
-/
@[path]
lemma y_mem_originIdeal
  {k : Type*}
  [CommRing k] :
-- imply
  (X : Polynomial (Polynomial k)) ∈ originIdeal k :=
-- proof
  Ideal.subset_span (Set.mem_insert_iff.mpr (Or.inr rfl))

end BlowupReesConnection

namespace BlowupReesConnection

/--
[xt_mem_reesAlgebra](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BlowupReesConnection.lean)
-/
@[path]
lemma xt_mem_reesAlgebra
  {k : Type*}
  [CommRing k] :
-- imply
  Polynomial.monomial 1 (C (X : Polynomial k) : Polynomial (Polynomial k)) ∈ reesAlgebra (originIdeal k) := by
-- proof
  rw [reesAlgebra.monomial_mem, pow_one]
  exact x_mem_originIdeal k

end BlowupReesConnection

namespace BlowupReesConnection

/--
[yt_mem_reesAlgebra](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BlowupReesConnection.lean)
-/
@[path]
lemma yt_mem_reesAlgebra
  {k : Type*}
  [CommRing k] :
-- imply
  Polynomial.monomial 1 (X : Polynomial (Polynomial k)) ∈ reesAlgebra (originIdeal k) := by
-- proof
  rw [reesAlgebra.monomial_mem, pow_one]
  exact y_mem_originIdeal k

end BlowupReesConnection

namespace BlowupReesConnection

/--
[CX_mul_X_eq_monomial](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BlowupReesConnection.lean)
-/
@[path]
lemma CX_mul_X_eq_monomial
  {k : Type*}
  [CommRing k] :
-- imply
  (C (X : Polynomial (Polynomial k)) : Polynomial (Polynomial (Polynomial k))) * (X : Polynomial (Polynomial (Polynomial k))) = Polynomial.monomial 1 (X : Polynomial (Polynomial k)) :=
-- proof
  C_mul_X_eq_monomial

end BlowupReesConnection

namespace BlowupReesConnection

/--
[yt_product_mem_reesAlgebra](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BlowupReesConnection.lean)
-/
@[path]
lemma yt_product_mem_reesAlgebra
  {k : Type*}
  [CommRing k] :
-- imply
  (C (X : Polynomial (Polynomial k)) : Polynomial (Polynomial (Polynomial k))) * (X : Polynomial (Polynomial (Polynomial k))) ∈ reesAlgebra (originIdeal k) := by
-- proof
  rw [CX_mul_X_eq_monomial]
  exact yt_mem_reesAlgebra k

end BlowupReesConnection

namespace BlowupReesConnection

/--
[coeffEmbed_mem_reesAlgebra](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BlowupReesConnection.lean)
-/
@[path]
lemma coeffEmbed_mem_reesAlgebra
  {k : Type*}
  [CommRing k]
  {a : Polynomial k} :
-- imply
  coeffEmbed k a ∈ reesAlgebra (originIdeal k) :=
-- proof
  Subalgebra.algebraMap_mem (reesAlgebra (originIdeal k)) (C a)

end BlowupReesConnection

namespace BlowupReesConnection

/--
[reesLift_mem_reesAlgebra](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BlowupReesConnection.lean)
-/
@[path]
lemma reesLift_mem_reesAlgebra
  {k : Type*}
  [CommRing k]
  {f : Polynomial (Polynomial k)} :
-- imply
  reesLift k f ∈ reesAlgebra (originIdeal k) := by
-- proof
  induction f using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add]
    exact (reesAlgebra (originIdeal k)).add_mem hp hq
  | monomial n a =>
    show eval₂ (coeffEmbed k) _ (monomial n a) ∈ _
    rw [eval₂_monomial]
    exact (reesAlgebra (originIdeal k)).mul_mem
      (coeffEmbed_mem_reesAlgebra k a)
      ((reesAlgebra (originIdeal k)).pow_mem (yt_product_mem_reesAlgebra k) n)

end BlowupReesConnection

namespace BlowupReesConnection

/--
[blowup_chart_factors_through_rees](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BlowupReesConnection.lean)
-/
@[path]
lemma blowup_chart_factors_through_rees
  {k : Type*}
  [CommRing k] :
-- imply
  (evalAtX k).comp (reesLift k) = blowupChartMap k := by
-- proof
  apply Polynomial.ringHom_ext
  ·
    intro a
    simp [evalAtX, reesLift, coeffEmbed, blowupChartMap]
  ·
    simp [evalAtX, reesLift, coeffEmbed, blowupChartMap]

end BlowupReesConnection

namespace BlowupReesConnection

/--
[blowup_chart_eq_eval_reesLift](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BlowupReesConnection.lean)
-/
@[path]
lemma blowup_chart_eq_eval_reesLift
  {k : Type*}
  [CommRing k]
  {f : Polynomial (Polynomial k)} :
-- imply
  blowupChartMap k f = evalAtX k (reesLift k f) :=
-- proof
  RingHom.congr_fun (blowup_chart_factors_through_rees k).symm f

end BlowupReesConnection

namespace BlowupReesConnection

/--
[reesLift_x](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BlowupReesConnection.lean)
-/
@[path]
lemma reesLift_x
  {k : Type*}
  [CommRing k] :
-- imply
  reesLift k (C (X : Polynomial k)) = coeffEmbed k (X : Polynomial k) := by
-- proof
  simp [reesLift, coeffEmbed]

end BlowupReesConnection

namespace BlowupReesConnection

/--
[reesLift_y](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BlowupReesConnection.lean)
-/
@[path]
lemma reesLift_y
  {k : Type*}
  [CommRing k] :
-- imply
  reesLift k (X : Polynomial (Polynomial k)) = (C (X : Polynomial (Polynomial k)) : Polynomial (Polynomial (Polynomial k))) * (X : Polynomial (Polynomial (Polynomial k))) := by
-- proof
  simp [reesLift, coeffEmbed]

end BlowupReesConnection

namespace BlowupReesConnection

/--
[reesLift_y_eq_monomial](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BlowupReesConnection.lean)
-/
@[path]
lemma reesLift_y_eq_monomial
  {k : Type*}
  [CommRing k] :
-- imply
  reesLift k (X : Polynomial (Polynomial k)) = Polynomial.monomial 1 (X : Polynomial (Polynomial k)) := by
-- proof
  rw [reesLift_y, CX_mul_X_eq_monomial]

end BlowupReesConnection


-- created on 2026-10-23
