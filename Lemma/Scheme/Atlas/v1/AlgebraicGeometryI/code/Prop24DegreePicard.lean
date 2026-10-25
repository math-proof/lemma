import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.Prop24DegreePicard
open Polynomial Prop24Picard


namespace Prop24Picard

/--
[fiber_dimension_formula](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Prop24DegreePicard.lean)
-/
@[path]
lemma fiber_dimension_formula
  {k : Type*}
  [Field k]
  [CommRing S]
  [IsDomain S]
  [Fintype ι]
  [Algebra (Polynomial k) S]
  [Algebra k S]
  [IsScalarTower k (Polynomial k) S]
  {b : Module.Basis ι (Polynomial k) S}
  {p : Polynomial k}
-- given
  (hp : p ≠ 0) :
-- imply
  Module.finrank k (S ⧸ Ideal.span {algebraMap (Polynomial k) S p}) = Fintype.card ι * p.natDegree := by
-- proof
  have hpne : algebraMap (Polynomial k) S p ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap (Polynomial k) S)]
    exact (b.algebraMap_injective (R := Polynomial k)).ne hp
  rw [finrank_quotient_span_eq_natDegree_norm b hpne,
    Algebra.norm_algebraMap_of_basis b,
    Polynomial.natDegree_pow]

end Prop24Picard

namespace Prop24Picard

/--
[prop24_degree_principal_divisor_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Prop24DegreePicard.lean)
-/
@[path]
lemma prop24_degree_principal_divisor_eq_zero
  {k : Type*}
  [Field k]
  [CommRing S]
  [IsDomain S]
  [Fintype ι]
  [Algebra (Polynomial k) S]
  [Algebra k S]
  [IsScalarTower k (Polynomial k) S]
  {b : Module.Basis ι (Polynomial k) S}
  {p q : Polynomial k}
-- given
  (hp : p ≠ 0)
  (hq : q ≠ 0)
  (hdeg : p.natDegree = q.natDegree) :
-- imply
  (Module.finrank k (S ⧸ Ideal.span {algebraMap (Polynomial k) S p}) : ℤ) - (Module.finrank k (S ⧸ Ideal.span {algebraMap (Polynomial k) S q}) : ℤ) = 0 := by
-- proof
  rw [fiber_dimension_formula k b hp, fiber_dimension_formula k b hq, hdeg, sub_self]

end Prop24Picard

namespace Prop24Picard

/--
[fiber_dimension_eq_rank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Prop24DegreePicard.lean)
-/
@[path]
lemma fiber_dimension_eq_rank
  {k : Type*}
  [Field k]
  [CommRing S]
  [IsDomain S]
  [Fintype ι]
  [Algebra (Polynomial k) S]
  [Algebra k S]
  [IsScalarTower k (Polynomial k) S]
  {b : Module.Basis ι (Polynomial k) S}
  {c : k} :
-- imply
  Module.finrank k (S ⧸ Ideal.span {algebraMap (Polynomial k) S (X - C c)}) = Fintype.card ι := by
-- proof
  rw [fiber_dimension_formula k b (X_sub_C_ne_zero c), natDegree_X_sub_C, mul_one]

end Prop24Picard

namespace Prop24Picard

/--
[fiber_dimension_constant](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Prop24DegreePicard.lean)
-/
@[path]
lemma fiber_dimension_constant
  {k : Type*}
  [Field k]
  [CommRing S]
  [IsDomain S]
  [Fintype ι]
  [Algebra (Polynomial k) S]
  [Algebra k S]
  [IsScalarTower k (Polynomial k) S]
  {b : Module.Basis ι (Polynomial k) S}
  {c₁ c₂ : k} :
-- imply
  Module.finrank k (S ⧸ Ideal.span {algebraMap (Polynomial k) S (X - C c₁)}) = Module.finrank k (S ⧸ Ideal.span {algebraMap (Polynomial k) S (X - C c₂)}) := by
-- proof
  rw [fiber_dimension_eq_rank k b c₁, fiber_dimension_eq_rank k b c₂]

end Prop24Picard

namespace Prop24Picard

/--
[degPic_mk](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Prop24DegreePicard.lean)
-/
@[path]
lemma degPic_mk
  {P : AddSubgroup (WeilDiv Y)}
  {D : WeilDiv Y}
-- given
  (hP : ∀ D ∈ P, weilDegree D = 0) :
-- imply
  degPic P hP (QuotientAddGroup.mk D) = weilDegree D := by
-- proof
  simp [degPic, QuotientAddGroup.lift_mk]

end Prop24Picard


-- created on 2026-10-23
