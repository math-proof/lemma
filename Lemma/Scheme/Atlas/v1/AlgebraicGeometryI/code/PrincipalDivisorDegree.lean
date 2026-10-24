import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.PrincipalDivisorDegree
open Polynomial PrincipalDivisorDegZero
open Module


/--
[fiber_dimension_eq_rank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PrincipalDivisorDegree.lean)
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
  have hp : algebraMap (Polynomial k) S (X - C c) ≠ 0 := by
    intro h
    exact absurd (Module.Basis.algebraMap_injective b (h.trans (map_zero _).symm))
      (by intro heq; exact absurd (congr_arg natDegree heq) (by simp))
  rw [finrank_quotient_span_eq_natDegree_norm b hp,
    Algebra.norm_algebraMap_of_basis b,
    Polynomial.natDegree_pow, natDegree_X_sub_C, mul_one]

/--
[fiber_dimension_constant](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PrincipalDivisorDegree.lean)
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

namespace PrincipalDivisorDegZero

/--
[algebraMap_ne_zero_of_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PrincipalDivisorDegree.lean)
-/
@[path]
lemma algebraMap_ne_zero_of_ne_zero
  {k : Type*}
  [Field k]
  [CommRing S]
  [IsDomain S]
  [Algebra (Polynomial k) S]
  [Algebra k S]
  [IsScalarTower k (Polynomial k) S]
  {b : Basis ι (Polynomial k) S}
  {p : Polynomial k}
-- given
  (hp : p ≠ 0) :
-- imply
  algebraMap (Polynomial k) S p ≠ 0 := by
-- proof
  rw [Ne, ← map_zero (algebraMap (Polynomial k) S)]
  exact (b.algebraMap_injective (R := Polynomial k)).ne hp

end PrincipalDivisorDegZero

namespace PrincipalDivisorDegZero

/--
[fiber_dimension_eq_rank_mul_natDegree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PrincipalDivisorDegree.lean)
-/
@[path]
lemma fiber_dimension_eq_rank_mul_natDegree
  {k : Type*}
  [Field k]
  [CommRing S]
  [IsDomain S]
  [Fintype ι]
  [Algebra (Polynomial k) S]
  [Algebra k S]
  [IsScalarTower k (Polynomial k) S]
  {b : Basis ι (Polynomial k) S}
  {p : Polynomial k}
-- given
  (hp : p ≠ 0) :
-- imply
  finrank k (S ⧸ Ideal.span {algebraMap (Polynomial k) S p}) = Fintype.card ι * p.natDegree := by
-- proof
  rw [finrank_quotient_span_eq_natDegree_norm b (algebraMap_ne_zero_of_ne_zero k b hp),
    Algebra.norm_algebraMap_of_basis b,
    Polynomial.natDegree_pow]

end PrincipalDivisorDegZero

namespace PrincipalDivisorDegZero

/--
[fiber_dimension_linear_eq_rank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PrincipalDivisorDegree.lean)
-/
@[path]
lemma fiber_dimension_linear_eq_rank
  {k : Type*}
  [Field k]
  [CommRing S]
  [IsDomain S]
  [Fintype ι]
  [Algebra (Polynomial k) S]
  [Algebra k S]
  [IsScalarTower k (Polynomial k) S]
  {b : Basis ι (Polynomial k) S}
  {c : k} :
-- imply
  finrank k (S ⧸ Ideal.span {algebraMap (Polynomial k) S (X - C c)}) = Fintype.card ι := by
-- proof
  rw [fiber_dimension_eq_rank_mul_natDegree k b (X_sub_C_ne_zero c),
    natDegree_X_sub_C, mul_one]

end PrincipalDivisorDegZero

namespace PrincipalDivisorDegZero

/--
[fiber_dimension_linear_constant](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PrincipalDivisorDegree.lean)
-/
@[path]
lemma fiber_dimension_linear_constant
  {k : Type*}
  [Field k]
  [CommRing S]
  [IsDomain S]
  [Fintype ι]
  [Algebra (Polynomial k) S]
  [Algebra k S]
  [IsScalarTower k (Polynomial k) S]
  {b : Basis ι (Polynomial k) S}
  {c₁ c₂ : k} :
-- imply
  finrank k (S ⧸ Ideal.span {algebraMap (Polynomial k) S (X - C c₁)}) = finrank k (S ⧸ Ideal.span {algebraMap (Polynomial k) S (X - C c₂)}) := by
-- proof
  rw [fiber_dimension_linear_eq_rank k b c₁, fiber_dimension_linear_eq_rank k b c₂]

end PrincipalDivisorDegZero

namespace PrincipalDivisorDegZero

/--
[fiber_dimension_eq_of_natDegree_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PrincipalDivisorDegree.lean)
-/
@[path]
lemma fiber_dimension_eq_of_natDegree_eq
  {k : Type*}
  [Field k]
  [CommRing S]
  [IsDomain S]
  [Fintype ι]
  [Algebra (Polynomial k) S]
  [Algebra k S]
  [IsScalarTower k (Polynomial k) S]
  {b : Basis ι (Polynomial k) S}
  {p q : Polynomial k}
-- given
  (hp : p ≠ 0)
  (hq : q ≠ 0)
  (hdeg : p.natDegree = q.natDegree) :
-- imply
  finrank k (S ⧸ Ideal.span {algebraMap (Polynomial k) S p}) = finrank k (S ⧸ Ideal.span {algebraMap (Polynomial k) S q}) := by
-- proof
  rw [fiber_dimension_eq_rank_mul_natDegree k b hp,
    fiber_dimension_eq_rank_mul_natDegree k b hq,
    hdeg]

end PrincipalDivisorDegZero

namespace PrincipalDivisorDegZero

/--
[principalDivisorDeg_eq_rank_mul_degDiff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PrincipalDivisorDegree.lean)
-/
@[path]
lemma principalDivisorDeg_eq_rank_mul_degDiff
  {k : Type*}
  [Field k]
  [CommRing S]
  [IsDomain S]
  [Fintype ι]
  [Algebra (Polynomial k) S]
  [Algebra k S]
  [IsScalarTower k (Polynomial k) S]
  {b : Basis ι (Polynomial k) S}
  {p q : Polynomial k}
-- given
  (hp : p ≠ 0)
  (hq : q ≠ 0) :
-- imply
  principalDivisorDeg k S (Ideal.span {algebraMap (Polynomial k) S p}) (Ideal.span {algebraMap (Polynomial k) S q}) = (Fintype.card ι : ℤ) * ((p.natDegree : ℤ) - (q.natDegree : ℤ)) := by
-- proof
  unfold principalDivisorDeg
  rw [fiber_dimension_eq_rank_mul_natDegree k b hp,
    fiber_dimension_eq_rank_mul_natDegree k b hq]
  push_cast; ring

end PrincipalDivisorDegZero

namespace PrincipalDivisorDegZero

/--
[principal_divisor_deg_zero_of_natDegree_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PrincipalDivisorDegree.lean)
-/
@[path]
lemma principal_divisor_deg_zero_of_natDegree_eq
  {k : Type*}
  [Field k]
  [CommRing S]
  [IsDomain S]
  [Fintype ι]
  [Algebra (Polynomial k) S]
  [Algebra k S]
  [IsScalarTower k (Polynomial k) S]
  {b : Basis ι (Polynomial k) S}
  {p q : Polynomial k}
-- given
  (hp : p ≠ 0)
  (hq : q ≠ 0)
  (hdeg : p.natDegree = q.natDegree) :
-- imply
  principalDivisorDeg k S (Ideal.span {algebraMap (Polynomial k) S p}) (Ideal.span {algebraMap (Polynomial k) S q}) = 0 := by
-- proof
  rw [principalDivisorDeg_eq_rank_mul_degDiff k b hp hq, hdeg, sub_self, mul_zero]

end PrincipalDivisorDegZero

namespace PrincipalDivisorDegZero

/--
[principal_divisor_deg_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PrincipalDivisorDegree.lean)
-/
@[path]
lemma principal_divisor_deg_zero
  {k : Type*}
  [Field k]
  [CommRing S]
  [IsDomain S]
  [Fintype ι]
  [Algebra (Polynomial k) S]
  [Algebra k S]
  [IsScalarTower k (Polynomial k) S]
  [IsCompleteCurveAlg k S]
  {b : Basis ι (Polynomial k) S}
  {p q : Polynomial k}
-- given
  (hp : p ≠ 0)
  (hq : q ≠ 0)
  (hpd : IsPrincipalDivisorData k S p q) :
-- imply
  principalDivisorDeg k S (Ideal.span {algebraMap (Polynomial k) S p}) (Ideal.span {algebraMap (Polynomial k) S q}) = 0 :=
-- proof
  principal_divisor_deg_zero_of_natDegree_eq k b hp hq
    (IsCompleteCurveAlg.deg_eq_of_principal p q hp hq hpd)

end PrincipalDivisorDegZero

namespace PrincipalDivisorDegZero

/--
[principal_divisor_deg_zero_linear](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PrincipalDivisorDegree.lean)
-/
@[path]
lemma principal_divisor_deg_zero_linear
  {k : Type*}
  [Field k]
  [CommRing S]
  [IsDomain S]
  [Fintype ι]
  [Algebra (Polynomial k) S]
  [Algebra k S]
  [IsScalarTower k (Polynomial k) S]
  {b : Basis ι (Polynomial k) S}
  {c₁ c₂ : k} :
-- imply
  principalDivisorDeg k S (Ideal.span {algebraMap (Polynomial k) S (X - C c₁)}) (Ideal.span {algebraMap (Polynomial k) S (X - C c₂)}) = 0 :=
-- proof
  principal_divisor_deg_zero_of_natDegree_eq k b (X_sub_C_ne_zero c₁) (X_sub_C_ne_zero c₂)
    (by simp)

end PrincipalDivisorDegZero

namespace PrincipalDivisorDegZero

/--
[principalDivisorDeg_affine_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PrincipalDivisorDegree.lean)
-/
@[path]
lemma principalDivisorDeg_affine_eq
  {k : Type*}
  [Field k]
  {p q : Polynomial k} :
-- imply
  principalDivisorDeg k (Polynomial k) (Ideal.span {p}) (Ideal.span {q}) = (p.natDegree : ℤ) - (q.natDegree : ℤ) := by
-- proof
  unfold principalDivisorDeg
  rw [finrank_quotient_span_eq_natDegree (f := p),
    finrank_quotient_span_eq_natDegree (f := q)]

end PrincipalDivisorDegZero

/--
[proposition_25_fiber_dimension_formula](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PrincipalDivisorDegree.lean)
-/
@[path]
lemma proposition_25_fiber_dimension_formula
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
  Module.finrank k (S ⧸ Ideal.span {algebraMap (Polynomial k) S p}) = Fintype.card ι * p.natDegree :=
-- proof
  PrincipalDivisorDegZero.fiber_dimension_eq_rank_mul_natDegree k b hp

/--
[proposition_25_principal_divisor_deg_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PrincipalDivisorDegree.lean)
-/
@[path]
lemma proposition_25_principal_divisor_deg_zero
  {k : Type*}
  [Field k]
  [CommRing S]
  [IsDomain S]
  [Fintype ι]
  [Algebra (Polynomial k) S]
  [Algebra k S]
  [IsScalarTower k (Polynomial k) S]
  [IsCompleteCurveAlg k S]
  {b : Module.Basis ι (Polynomial k) S}
  {p q : Polynomial k}
-- given
  (hp : p ≠ 0)
  (hq : q ≠ 0)
  (hpd : IsPrincipalDivisorData k S p q) :
-- imply
  (Module.finrank k (S ⧸ Ideal.span {algebraMap (Polynomial k) S p}) : ℤ) - (Module.finrank k (S ⧸ Ideal.span {algebraMap (Polynomial k) S q}) : ℤ) = 0 := by
-- proof
  have hdeg := IsCompleteCurveAlg.deg_eq_of_principal p q hp hq hpd
  rw [proposition_25_fiber_dimension_formula k b hp,
    proposition_25_fiber_dimension_formula k b hq, hdeg]
  simp


-- created on 2026-10-23
