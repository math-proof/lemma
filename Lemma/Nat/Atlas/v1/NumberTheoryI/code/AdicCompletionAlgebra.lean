import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.NumberTheoryI.code.AdicCompletionAlgebra.Part3
open IsDedekindDomain UniformSpace AdicCompletionAlgebra


/--
[algebraMap_withVal_continuous_general](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/AdicCompletionAlgebra.lean)
-/
@[path]
private lemma algebraMap_withVal_continuous_general_eq
  [CommRing A]
  [IsDedekindDomain A]
  [IsDomain A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [Field L]
  [Algebra A L]
  [Algebra K L]
  [IsScalarTower A K L]
  [CommRing B]
  [IsDomain B]
  [IsDedekindDomain B]
  [Algebra A B]
  [Algebra B L]
  [IsScalarTower A B L]
  [IsIntegralClosure B A L]
  [IsFractionRing B L]
  {𝔭 : HeightOneSpectrum A}
  {𝔮 : HeightOneSpectrum B}
-- given
  (h𝔮_over_𝔭 : 𝔭.asIdeal ≤ Ideal.comap (algebraMap A B) 𝔮.asIdeal) :
-- imply
  Continuous ((WithVal.equiv (𝔮.valuation L)).symm ∘ (algebraMap K L) ∘ (WithVal.equiv (𝔭.valuation K)) : WithVal (𝔭.valuation K) → WithVal (𝔮.valuation L)) := by
-- proof
  apply algebraMap_withVal_continuous_general K 𝔭 𝔮 h𝔮_over_𝔭

/--
[continuous_algebraMap_adicCompletion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/AdicCompletionAlgebra.lean)
-/
@[path]
private lemma continuous_algebraMap_adicCompletion_eq
  [CommRing A]
  [IsDedekindDomain A]
  [IsDomain A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [Field L]
  [Algebra A L]
  [Algebra K L]
  [IsScalarTower A K L]
  [CommRing B]
  [IsDomain B]
  [IsDedekindDomain B]
  [Algebra A B]
  [Algebra B L]
  [IsScalarTower A B L]
  [IsIntegralClosure B A L]
  [IsFractionRing B L]
  {𝔭 : HeightOneSpectrum A}
  {𝔮 : HeightOneSpectrum B}
-- given
  (h𝔮_over_𝔭 : 𝔭.asIdeal ≤ Ideal.comap (algebraMap A B) 𝔮.asIdeal) :
-- imply
  Continuous ((algebraMap L (𝔮.adicCompletion L)).comp ((algebraMap K L).comp (WithVal.equiv (𝔭.valuation K)).toRingHom) : WithVal (𝔭.valuation K) → 𝔮.adicCompletion L) := by
-- proof
  apply AdicCompletionAlgebra.continuous_algebraMap_adicCompletion K 𝔭 𝔮 h𝔮_over_𝔭

/--
[adicCompletionMap_comp_algebraMap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/AdicCompletionAlgebra.lean)
-/
@[path]
private lemma adicCompletionMap_comp_algebraMap_eq
  [CommRing A]
  [IsDedekindDomain A]
  [IsDomain A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [Field L]
  [Algebra A L]
  [Algebra K L]
  [IsScalarTower A K L]
  [CommRing B]
  [IsDomain B]
  [IsDedekindDomain B]
  [Algebra A B]
  [Algebra B L]
  [IsScalarTower A B L]
  [IsIntegralClosure B A L]
  [IsFractionRing B L]
  {𝔭 : HeightOneSpectrum A}
  {𝔮 : HeightOneSpectrum B}
-- given
  (h𝔮_over_𝔭 : 𝔭.asIdeal ≤ Ideal.comap (algebraMap A B) 𝔮.asIdeal) :
-- imply
  (adicCompletionMap K 𝔭 𝔮 h𝔮_over_𝔭).comp (algebraMap K (𝔭.adicCompletion K)) = (algebraMap L (𝔮.adicCompletion L)).comp (algebraMap K L) := by
-- proof
  apply AdicCompletionAlgebra.adicCompletionMap_comp_algebraMap K 𝔭 𝔮 h𝔮_over_𝔭

/--
[isScalarTower_adicCompletion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/AdicCompletionAlgebra.lean)
-/
@[path]
private lemma isScalarTower_adicCompletion_eq
  [CommRing A]
  [IsDedekindDomain A]
  [IsDomain A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [Field L]
  [Algebra A L]
  [Algebra K L]
  [IsScalarTower A K L]
  [CommRing B]
  [IsDomain B]
  [IsDedekindDomain B]
  [Algebra A B]
  [Algebra B L]
  [IsScalarTower A B L]
  [IsIntegralClosure B A L]
  [IsFractionRing B L]
  {𝔭 : HeightOneSpectrum A}
  {𝔮 : HeightOneSpectrum B}
-- given
  (h𝔮_over_𝔭 : 𝔭.asIdeal ≤ Ideal.comap (algebraMap A B) 𝔮.asIdeal) :
-- imply
  @IsScalarTower K (𝔭.adicCompletion K) (𝔮.adicCompletion L) _ (instAlgebraAdicCompletionOfLiesOver K 𝔭 𝔮 h𝔮_over_𝔭).toSMul _ := by
-- proof
  apply isScalarTower_adicCompletion K 𝔭 𝔮 h𝔮_over_𝔭


-- created on 2026-10-23
