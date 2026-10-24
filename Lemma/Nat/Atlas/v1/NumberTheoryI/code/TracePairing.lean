import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.NumberTheoryI.code.TracePairing
open Algebra


/--
[prop_5_17_isFractionRing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/TracePairing.lean)
-/
@[path]
lemma prop_5_17_isFractionRing
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra A L]
  [IsScalarTower A K L]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [Algebra B L]
  [IsIntegralClosure B A L] :
-- imply
  IsFractionRing B L :=
-- proof
  IsIntegralClosure.isFractionRing_of_finite_extension A K L B

/--
[prop_5_18_norm_isIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/TracePairing.lean)
-/
@[path]
lemma prop_5_18_norm_isIntegral
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra A L]
  [IsScalarTower A K L]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [Algebra B L]
  [IsIntegralClosure B A L]
  {b : B} :
-- imply
  IsIntegral A (Algebra.norm K (algebraMap B L b)) :=
-- proof
  Algebra.isIntegral_norm K ((IsIntegralClosure.isIntegral A L b).algebraMap)

/--
[prop_5_18_trace_isIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/TracePairing.lean)
-/
@[path]
lemma prop_5_18_trace_isIntegral
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra A L]
  [IsScalarTower A K L]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [Algebra B L]
  [IsIntegralClosure B A L]
  {b : B} :
-- imply
  IsIntegral A (Algebra.trace K L (algebraMap B L b)) :=
-- proof
  Algebra.isIntegral_trace ((IsIntegralClosure.isIntegral A L b).algebraMap)

/--
[thm_5_20_traceForm_symmetric](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/TracePairing.lean)
-/
@[path]
lemma thm_5_20_traceForm_symmetric
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra A L]
  [IsScalarTower A K L]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [Algebra B L]
  [IsIntegralClosure B A L] :
-- imply
  (Algebra.traceForm K L).IsSymm :=
-- proof
  Algebra.traceForm_isSymm K
variable [Algebra.IsSeparable K L] in

/--
[thm_5_20_nondegenerate_of_separable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/TracePairing.lean)
-/
@[path]
lemma thm_5_20_nondegenerate_of_separable
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra A L]
  [IsScalarTower A K L]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [Algebra B L]
  [IsIntegralClosure B A L]
  [Algebra.IsSeparable K L] :
-- imply
  (Algebra.traceForm K L).Nondegenerate :=
-- proof
  traceForm_nondegenerate K L

/--
[thm_5_20_separable_of_nondegenerate](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/TracePairing.lean)
-/
@[path]
lemma thm_5_20_separable_of_nondegenerate
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra A L]
  [IsScalarTower A K L]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [Algebra B L]
  [IsIntegralClosure B A L]
  [Algebra.IsSeparable K L]
-- given
  (hnd : (Algebra.traceForm K L).Nondegenerate) :
-- imply
  Algebra.IsSeparable K L :=
-- proof
  ((traceForm_nondegenerate_tfae K L).out 2 0).mp hnd

/--
[thm_5_20_nondegenerate_iff_separable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/TracePairing.lean)
-/
@[path]
lemma thm_5_20_nondegenerate_iff_separable
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra A L]
  [IsScalarTower A K L]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [Algebra B L]
  [IsIntegralClosure B A L]
  [Algebra.IsSeparable K L] :
-- imply
  [Algebra.IsSeparable K L, Algebra.trace K L ≠ 0, (Algebra.traceForm K L).Nondegenerate].TFAE :=
-- proof
  traceForm_nondegenerate_tfae K L
omit [IsDomain B] in
include K L in
variable [IsDedekindDomain A] [Algebra.IsSeparable K L] in

/--
[prop_5_22_finite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/TracePairing.lean)
-/
@[path]
lemma prop_5_22_finite
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra A L]
  [IsScalarTower A K L]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [Algebra B L]
  [IsIntegralClosure B A L]
  [Algebra.IsSeparable K L]
  [IsDedekindDomain A]
  [Algebra.IsSeparable K L] :
-- imply
  Module.Finite A B :=
-- proof
  IsIntegralClosure.finite A K L B
omit [IsDomain B] in
include K L in
variable [IsDedekindDomain A] [Algebra.IsSeparable K L] in

/--
[prop_5_22_isNoetherian](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/TracePairing.lean)
-/
@[path]
lemma prop_5_22_isNoetherian
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra A L]
  [IsScalarTower A K L]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [Algebra B L]
  [IsIntegralClosure B A L]
  [Algebra.IsSeparable K L]
  [IsDedekindDomain A]
  [Algebra.IsSeparable K L]
  [IsDedekindDomain A]
  [Algebra.IsSeparable K L] :
-- imply
  IsNoetherian A B :=
-- proof
  IsIntegralClosure.isNoetherian A K L B
alias traceForm_symmetric := thm_5_20_traceForm_symmetric


-- created on 2026-10-23
