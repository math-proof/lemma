import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.Lec15PicardDivisorClass.Part3
open Lec15PicardDivisorClass
open Module Polynomial LinearEquivDivisors


namespace Lec15PicardDivisorClass

/--
[picard_projective_generated_by_O1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec15PicardDivisorClass.lean)
-/
@[path]
lemma picard_projective_generated_by_O1
  {k : Type*}
  [Field k]
  {n : ℕ}
  {L : PicardProjective.GradedPicardGroup (Fin (n + 1)) k} :
-- imply
  ∃ d : ℤ, L = PicardProjective.twistingSheafPow n k d :=
-- proof
  PicardProjective.picardGroup_generated_by_O1 k n L

end Lec15PicardDivisorClass

namespace Lec15PicardDivisorClass

/--
[degree_O1_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec15PicardDivisorClass.lean)
-/
@[path]
lemma degree_O1_eq_one
  {k : Type*}
  [Field k]
  {n : ℕ} :
-- imply
  (PicardProjective.gradedPicardGroup_equiv_int k n) (PicardProjective.twistingSheaf n k) = 1 :=
-- proof
  PicardProjective.degree_twistingSheaf k n

end Lec15PicardDivisorClass

namespace Lec15PicardDivisorClass

/--
[prop23a_powerSeries_ufd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec15PicardDivisorClass.lean)
-/
@[path]
lemma prop23a_powerSeries_ufd
  {k : Type*}
  [Field k]
  {n : ℕ} :
-- imply
  UniqueFactorizationMonoid (MvPowerSeries (Fin n) k) :=
-- proof
  PowerSeriesUFD.mvPowerSeries_isUFD k n

end Lec15PicardDivisorClass

namespace Lec15PicardDivisorClass

/--
[prop23b_noetherian_local_completion_ufd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec15PicardDivisorClass.lean)
-/
@[path]
lemma prop23b_noetherian_local_completion_ufd
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsLocalRing A]
  [IsNoetherianRing A]
-- given
  (hcompl : UniqueFactorizationMonoid (AdicCompletion (IsLocalRing.maximalIdeal A) A)) :
-- imply
  UniqueFactorizationMonoid A :=
-- proof
  PowerSeriesUFD.ufd_of_completion_ufd A hcompl

end Lec15PicardDivisorClass

namespace Lec15PicardDivisorClass

/--
[lD_dim_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec15PicardDivisorClass.lean)
-/
@[path]
lemma lD_dim_nonneg
  {k : Type*}
  [Field k]
  {V : Type*}
  [AddCommGroup V]
  [Module k V] :
-- imply
  0 ≤ lD_dim k V :=
-- proof
  Nat.zero_le _

end Lec15PicardDivisorClass

namespace Lec15PicardDivisorClass

/--
[lD_dim_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec15PicardDivisorClass.lean)
-/
@[path]
lemma lD_dim_eq_zero_iff
  {k : Type*}
  [Field k]
  {V : Type*}
  [AddCommGroup V]
  [Module k V] :
-- imply
  lD_dim k V = 0 ↔ Module.finrank k V = 0 := by
-- proof
  rfl

end Lec15PicardDivisorClass

namespace Lec15PicardDivisorClass

/--
[divisorDegree_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec15PicardDivisorClass.lean)
-/
@[path]
lemma divisorDegree_zero
-- imply
  divisorDegree (0 : DivisorsPicard.WeilDivisorGroup Y) = 0 :=
-- proof
  WeilDivisor.degree_zero

end Lec15PicardDivisorClass

namespace Lec15PicardDivisorClass

/--
[divisorDegree_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec15PicardDivisorClass.lean)
-/
@[path]
lemma divisorDegree_add
  [DecidableEq Y]
  {D₁ D₂ : DivisorsPicard.WeilDivisorGroup Y} :
-- imply
  divisorDegree (D₁ + D₂) = divisorDegree D₁ + divisorDegree D₂ :=
-- proof
  WeilDivisor.degree_add D₁ D₂

end Lec15PicardDivisorClass

namespace Lec15PicardDivisorClass

/--
[divisorDegree_eq_of_linearlyEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec15PicardDivisorClass.lean)
-/
@[path]
lemma divisorDegree_eq_of_linearlyEquiv
  [DecidableEq Y]
  {P : PrincipalDivisors Y}
  {D₁ D₂ : DivisorsPicard.WeilDivisorGroup Y}
-- given
  (hP : ∀ D ∈ P, WeilDivisor.degree D = 0)
  (h : WeilLinearlyEquivalent P D₁ D₂) :
-- imply
  divisorDegree D₁ = divisorDegree D₂ :=
-- proof
  WeilDivisor.degree_eq_of_linearlyEquiv hP h

end Lec15PicardDivisorClass

namespace Lec15PicardDivisorClass

/--
[bezout_thm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec15PicardDivisorClass.lean)
-/
@[path]
lemma bezout_thm
  {k : Type*}
  [Field k]
  {g : Polynomial (Polynomial k)}
  {f : Polynomial k}
-- given
  (hg_monic : g.Monic)
  (hg_irred : Irreducible g)
  (hf : algebraMap (Polynomial k) (AdjoinRoot g) f ≠ 0) :
-- imply
  Module.finrank k (AdjoinRoot g ⧸ Ideal.span {algebraMap (Polynomial k) (AdjoinRoot g) f}) = g.natDegree * f.natDegree :=
-- proof
  bezout_algebraic_irreducible k g hg_monic hg_irred f hf

end Lec15PicardDivisorClass

namespace Lec15PicardDivisorClass

/--
[line_line_bezout](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec15PicardDivisorClass.lean)
-/
@[path]
lemma line_line_bezout
  {k : Type*}
  [Field k] :
-- imply
  Module.finrank k (Polynomial (Polynomial k) ⧸ Ideal.span {Polynomial.C (Polynomial.X : Polynomial k), (Polynomial.X : Polynomial (Polynomial k))}) = 1 :=
-- proof
  line_line_intersection_dim k

end Lec15PicardDivisorClass

namespace Lec15PicardDivisorClass

/--
[prop24_principal_divisor_degree_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec15PicardDivisorClass.lean)
-/
@[path]
lemma prop24_principal_divisor_degree_zero
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
  PrincipalDivisorDegZero.principalDivisorDeg k S (Ideal.span {algebraMap (Polynomial k) S p}) (Ideal.span {algebraMap (Polynomial k) S q}) = 0 :=
-- proof
  PrincipalDivisorDegZero.principal_divisor_deg_zero k b hp hq hpd

end Lec15PicardDivisorClass

namespace Lec15PicardDivisorClass

/--
[prop24_degree_formula](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec15PicardDivisorClass.lean)
-/
@[path]
lemma prop24_degree_formula
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
  PrincipalDivisorDegZero.principalDivisorDeg k S (Ideal.span {algebraMap (Polynomial k) S p}) (Ideal.span {algebraMap (Polynomial k) S q}) = (Fintype.card ι : ℤ) * ((p.natDegree : ℤ) - (q.natDegree : ℤ)) :=
-- proof
  PrincipalDivisorDegZero.principalDivisorDeg_eq_rank_mul_degDiff k b hp hq

end Lec15PicardDivisorClass

namespace Lec15PicardDivisorClass

/--
[prop24_affine_formula](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec15PicardDivisorClass.lean)
-/
@[path]
lemma prop24_affine_formula
  {k : Type*}
  [Field k]
  {p q : Polynomial k} :
-- imply
  PrincipalDivisorDegZero.principalDivisorDeg k (Polynomial k) (Ideal.span {p}) (Ideal.span {q}) = (p.natDegree : ℤ) - (q.natDegree : ℤ) :=
-- proof
  PrincipalDivisorDegZero.principalDivisorDeg_affine_eq k p q

end Lec15PicardDivisorClass

namespace Lec15PicardDivisorClass

/--
[prop25_principal_divisor_degree_zero_curve](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec15PicardDivisorClass.lean)
-/
@[path]
lemma prop25_principal_divisor_degree_zero_curve
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
  PrincipalDivisorDegZero.principalDivisorDeg k S (Ideal.span {algebraMap (Polynomial k) S (Polynomial.X - Polynomial.C c₁)}) (Ideal.span {algebraMap (Polynomial k) S (Polynomial.X - Polynomial.C c₂)}) = 0 :=
-- proof
  PrincipalDivisorDegZero.principal_divisor_deg_zero_linear k b c₁ c₂

end Lec15PicardDivisorClass

namespace Lec15PicardDivisorClass

/--
[prop25_fiber_dimension_eq_rank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec15PicardDivisorClass.lean)
-/
@[path]
lemma prop25_fiber_dimension_eq_rank
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
  Module.finrank k (S ⧸ (Ideal.span {algebraMap (Polynomial k) S (Polynomial.X - Polynomial.C c)})) = Fintype.card ι :=
-- proof
  PrincipalDivisorDegZero.fiber_dimension_linear_eq_rank k b c

end Lec15PicardDivisorClass

namespace Lec15PicardDivisorClass

/--
[prop25_fiber_dimension_constant](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec15PicardDivisorClass.lean)
-/
@[path]
lemma prop25_fiber_dimension_constant
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
  Module.finrank k (S ⧸ (Ideal.span {algebraMap (Polynomial k) S (Polynomial.X - Polynomial.C c₁)})) = Module.finrank k (S ⧸ (Ideal.span {algebraMap (Polynomial k) S (Polynomial.X - Polynomial.C c₂)})) :=
-- proof
  PrincipalDivisorDegZero.fiber_dimension_linear_constant k b c₁ c₂

end Lec15PicardDivisorClass

namespace Lec15PicardDivisorClass

/--
[prop25_fiber_dimension_formula](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec15PicardDivisorClass.lean)
-/
@[path]
lemma prop25_fiber_dimension_formula
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
  Module.finrank k (S ⧸ Ideal.span {algebraMap (Polynomial k) S p}) = Fintype.card ι * p.natDegree :=
-- proof
  PrincipalDivisorDegZero.fiber_dimension_eq_rank_mul_natDegree k b hp

end Lec15PicardDivisorClass

namespace Lec15PicardDivisorClass

/--
[completeLinearSystemProjDim_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec15PicardDivisorClass.lean)
-/
@[path]
lemma completeLinearSystemProjDim_eq
  {k : Type*}
  [Field k]
  {V : Type*}
  [AddCommGroup V]
  [Module k V] :
-- imply
  completeLinearSystemProjDim k V = (lD_dim k V : ℤ) - 1 := by
-- proof
  rfl

end Lec15PicardDivisorClass

namespace Lec15PicardDivisorClass

/--
[completeLinearSystem_nonempty_of_lD_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec15PicardDivisorClass.lean)
-/
@[path]
lemma completeLinearSystem_nonempty_of_lD_pos
  {k : Type*}
  [Field k]
  {V : Type*}
  [AddCommGroup V]
  [Module k V]
-- given
  (h : 1 ≤ lD_dim k V) :
-- imply
  completeLinearSystemProjDim k V ≥ 0 := by
-- proof
  unfold completeLinearSystemProjDim lD_dim at *
  omega
end Lec15PicardDivisorClass



-- created on 2026-10-23
