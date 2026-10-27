import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.BezoutIntersection
open Polynomial Module


namespace BezoutIntersection

/--
[totalIntersectionNumber_eq_sup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BezoutIntersection.lean)
-/
@[path]
lemma totalIntersectionNumber_eq_sup
  {k : Type*}
  [Field k]
  {f g : Polynomial (Polynomial k)} :
-- imply
  totalIntersectionNumber k f g = finrank k (Polynomial (Polynomial k) ⧸ (Ideal.span {f} ⊔ Ideal.span {g})) :=
-- proof
  LinearEquiv.finrank_eq
    (Ideal.quotientEquivAlgOfEq k (ideal_span_pair_eq_sup f g)).toLinearEquiv
set_option synthInstance.maxHeartbeats 80000 in

end BezoutIntersection

namespace BezoutIntersection

/--
[bezout_irreducible_base](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BezoutIntersection.lean)
-/
@[path]
lemma bezout_irreducible_base
  {k : Type*}
  [Field k]
  {g : Polynomial (Polynomial k)}
  {p : Polynomial k}
-- given
  (hg : g.Monic)
  (hirr : Irreducible g)
  (hp : algebraMap (Polynomial k) (AdjoinRoot g) p ≠ 0) :
-- imply
  totalIntersectionNumber k g (Polynomial.C p) = g.natDegree * p.natDegree := by
-- proof
  haveI : IsDomain (AdjoinRoot g) := AdjoinRoot.isDomain_of_prime hirr.prime
  unfold totalIntersectionNumber
  rw [ideal_span_pair_eq_sup]
  exact bezout_bivariate_base k g hg p hp

end BezoutIntersection

namespace BezoutIntersection

/--
[intersection_additivity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BezoutIntersection.lean)
-/
@[path]
lemma intersection_additivity
  {k : Type*}
  [Field k]
  {g : Polynomial (Polynomial k)}
  [IsDomain (AdjoinRoot g)]
  {f₁ f₂ : Polynomial k}
-- given
  (hg : g.Monic)
  (hf₁ : f₁ ≠ 0)
  (hf₂ : f₂ ≠ 0) :
-- imply
  finrank k (AdjoinRoot g ⧸ Ideal.span {algebraMap (Polynomial k) (AdjoinRoot g) (f₁ * f₂)}) = finrank k (AdjoinRoot g ⧸ Ideal.span {algebraMap (Polynomial k) (AdjoinRoot g) f₁}) + finrank k (AdjoinRoot g ⧸ Ideal.span {algebraMap (Polynomial k) (AdjoinRoot g) f₂}) := by
-- proof
  have b := (AdjoinRoot.powerBasis' hg).basis
  have hinj : Function.Injective (algebraMap (Polynomial k) (AdjoinRoot g)) :=
    b.algebraMap_injective
  have hf₁' : algebraMap (Polynomial k) (AdjoinRoot g) f₁ ≠ 0 :=
    fun h => hf₁ (hinj (h.trans (map_zero _).symm))
  have hf₂' : algebraMap (Polynomial k) (AdjoinRoot g) f₂ ≠ 0 :=
    fun h => hf₂ (hinj (h.trans (map_zero _).symm))
  have hf₁₂ : f₁ * f₂ ≠ 0 := mul_ne_zero hf₁ hf₂
  have hf₁₂' : algebraMap (Polynomial k) (AdjoinRoot g) (f₁ * f₂) ≠ 0 :=
    fun h => hf₁₂ (hinj (h.trans (map_zero _).symm))
  rw [finrank_quotient_span_eq_natDegree_norm b hf₁₂',
    Algebra.norm_algebraMap_of_basis b, Polynomial.natDegree_pow,
    finrank_quotient_span_eq_natDegree_norm b hf₁',
    Algebra.norm_algebraMap_of_basis b, Polynomial.natDegree_pow,
    finrank_quotient_span_eq_natDegree_norm b hf₂',
    Algebra.norm_algebraMap_of_basis b, Polynomial.natDegree_pow,
    Polynomial.natDegree_mul hf₁ hf₂,
    Fintype.card_fin, AdjoinRoot.powerBasis'_dim]
  ring

end BezoutIntersection

namespace BezoutIntersection

/--
[intersection_depends_only_on_degree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BezoutIntersection.lean)
-/
@[path]
lemma intersection_depends_only_on_degree
  {k : Type*}
  [Field k]
  {g : Polynomial (Polynomial k)}
  [IsDomain (AdjoinRoot g)]
  {p q : Polynomial k}
-- given
  (hg : g.Monic)
  (hp : p ≠ 0)
  (hq : q ≠ 0)
  (hdeg : p.natDegree = q.natDegree) :
-- imply
  finrank k (AdjoinRoot g ⧸ Ideal.span {algebraMap (Polynomial k) (AdjoinRoot g) p}) = finrank k (AdjoinRoot g ⧸ Ideal.span {algebraMap (Polynomial k) (AdjoinRoot g) q}) := by
-- proof
  have b := (AdjoinRoot.powerBasis' hg).basis
  have hinj := b.algebraMap_injective (R := Polynomial k)
  have hp' : algebraMap (Polynomial k) (AdjoinRoot g) p ≠ 0 :=
    fun h => hp (hinj (h.trans (map_zero _).symm))
  have hq' : algebraMap (Polynomial k) (AdjoinRoot g) q ≠ 0 :=
    fun h => hq (hinj (h.trans (map_zero _).symm))
  rw [finrank_quotient_span_eq_natDegree_norm b hp',
    finrank_quotient_span_eq_natDegree_norm b hq',
    Algebra.norm_algebraMap_of_basis b,
    Algebra.norm_algebraMap_of_basis b,
    Polynomial.natDegree_pow,
    Polynomial.natDegree_pow,
    hdeg]

end BezoutIntersection

namespace BezoutIntersection

/--
[divisor_degree_of_intersection](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BezoutIntersection.lean)
-/
@[path]
lemma divisor_degree_of_intersection
  {k : Type*}
  [Field k]
  {g : Polynomial (Polynomial k)}
  [IsDomain (AdjoinRoot g)]
  {p : Polynomial k}
-- given
  (hg : g.Monic)
  (hp : p ≠ 0) :
-- imply
  finrank k (AdjoinRoot g ⧸ Ideal.span {algebraMap (Polynomial k) (AdjoinRoot g) p}) = g.natDegree * p.natDegree := by
-- proof
  have b := (AdjoinRoot.powerBasis' hg).basis
  have hinj := b.algebraMap_injective (R := Polynomial k)
  have hp' : algebraMap (Polynomial k) (AdjoinRoot g) p ≠ 0 :=
    fun h => hp (hinj (h.trans (map_zero _).symm))
  rw [finrank_quotient_algebraMap k b p hp', Fintype.card_fin,
    AdjoinRoot.powerBasis'_dim]

end BezoutIntersection

namespace BezoutIntersection

/--
[bezout_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BezoutIntersection.lean)
-/
@[path]
lemma bezout_theorem
  {k : Type*}
  [Field k]
  {g : Polynomial (Polynomial k)}
  {p : Polynomial k}
-- given
  (hg : g.Monic)
  (hirr : Irreducible g)
  (hp : algebraMap (Polynomial k) (AdjoinRoot g) p ≠ 0) :
-- imply
  totalIntersectionNumber k g (Polynomial.C p) = g.natDegree * p.natDegree :=
-- proof
  bezout_irreducible_base k g hg hirr p hp

end BezoutIntersection


-- created on 2026-10-23
