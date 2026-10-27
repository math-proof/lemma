/- Completed Dedekind zeta package (Gapsw scaffolding).
   Sourced from fermats-last-theorem
   P2M/Sol/S_NumberField_exists_completedDedekindZeta_package.lean
   (properly ordered namespaces). Flattened Lemma/Real copy had forward-ref issues.

   Import: Theorem.NumberTheory.NumberField.CompletedDedekindZeta.Package.Part67
   Outer namespace: P2MW.S_NumberField_exists_completedDedekindZeta_package

   Public API (open the FLT.* subnamespaces under the outer namespace, or use `solution`):
   - gapsw80_t9_completedDedekindZeta
   - gapsw80_t9_differentiableOn_completedDedekindZeta
   - gapsw80_t9_completedDedekindZeta_FE
   - gapsw80_t10_completedDedekindZeta_eq_T1
   - gapsw80_t16_B1_closed
   - gapsw80_t36_D1app_closed
   - gapsw80_t43_SL_closed
-/

import Mathlib
import Lemma.Int.P2MUtil
import Def.NumberTheory.NumberField.CompletedDedekindZeta.Package.Part30


namespace P2MW.S_NumberField_exists_completedDedekindZeta_package

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 800000

set_option maxHeartbeats 999999

namespace Asymptotics

p2m_export "Asymptotics" "IsBigO IsBigO.of_bound isBigO_atTop_natCast_rpow_of_tendsto_div_rpow"

p2m_open "Asymptotics"

end Asymptotics

namespace Classical

p2m_export "Classical" "choose_spec em by_cases choose"

p2m_open "Classical"

end Classical

namespace Complex

p2m_export "Complex" "ofReal_sub log_exp one_re continuous_re measurable_ofReal add_conj one_cpow re sqrt norm_cpow_eq_rpow_re_of_pos re_ofNat ofReal_re add_re ofRealHom sqrt_one natCast_im ofReal_ne_zero lift norm_real intCast_im ofReal_tsum ofReal_prod real_smul one_im im_ofNat ofReal_inv ofReal_zpow cpow_ne_zero_iff re_le_norm Gammaℝ re_sum add_im ofReal_natCast norm_natCast ofReal_eq_one Gamma_nat_eq_factorial re_ofReal_mul ofReal_sum cpow_one Gamma_eq_integral ofReal_neg im hasSum_iff ofReal_intCast exp_sum Gamma_ne_zero normSq_eq_norm_sq ofReal_pow arg log_inv Gamma_ofReal hasSum_re I_sq ofReal_eq_zero normSq_apply Gamma rank_real_complex cpow_zero cpow_neg cpow_natCast exists mk.injEq ofReal ofReal_zero ofReal_mul exp_neg intCast_re im_sum neg_re sub_re inv_cpow I_re div_ofNat_re cpow_add continuous_exp coe_smul cpow_nat_mul' mul_cpow_ofReal_nonneg exp mk arg_ofReal_of_nonneg norm_exp pos_iff sub_im ofReal_add Gammaℝ_ne_zero_of_re_pos exp_zero measurable_exp ofReal_div cpow exp_log natCast_re cpow_intCast Gammaℂ ofReal_cpow continuous_ofReal cpow_neg_one log_zero I_im tsum_exp_neg_quadratic cpow_nat_mul ofReal_one mul_re im_ofReal_mul log_mul GammaIntegral ofReal_im log Gammaℝ_def ofReal_ofNat ofReal_exp div_re Gammaℂ_def ext I Gamma_add_one exp_nat_mul I_mul_I normSq_ofNat mul_im measurable_log hasDerivAt_log exp_add"

p2m_open "Complex"

end Complex

namespace ContinuousLinearMap

p2m_export "ContinuousLinearMap" "proj coe_mk zero_apply apply toLinearMap smulRight_apply comp add coe_proj zero det_pi coe_coe sub_apply mk.injEq restrict bound det snd one_apply mul_apply pi comp_apply sub smul_apply neg smulRight ext sum_apply coe_pi single inl neg_apply ring coe_smul add_apply proj_pi single_apply inr mul mk coe_comp"

p2m_open "ContinuousLinearMap"

end ContinuousLinearMap

namespace ENNReal

p2m_export "ENNReal" "ofReal_pow tsum_const ofReal_zero log_rpow ofReal_ofNat ofReal_add coe_smul ofReal_eq_one ofReal_ne_top ofReal_le_ofReal log_zero continuous_ofReal rpow_two log_inv toReal_mono summable_toReal coe_finset_sum ofReal_pos rpow_neg_one ofReal_mul smul_def continuous_sub_right one_le_rpow inv_rpow toReal_one one_ne_top add_left_inj toReal_prod rpow_le_rpow_of_exponent_ge mul_pos eq_div_iff zpow_pos ofReal_lt_top prod_lt_top log one_lt_two log_pow div_eq_zero_iff tsum_eq_add_tsum_ite measurable_ofReal ofReal_natCast exp_log continuous_exp rpow_le_rpow_of_exponent_le ofReal_prod_of_nonneg log_le_log rpow_one ofReal_tsum_of_nonneg rpow_natCast ofReal_sub measurable_log ofReal_eq_zero one_lt_top toReal_ofReal ofReal_one Icc_mem_nhds rpow_mul rpow_neg"

p2m_open "ENNReal"

end ENNReal

namespace FLT

namespace KwDyf2RealGammaLogBound

end FLT.KwDyf2RealGammaLogBound

namespace FLT

namespace KwDyf2XiEntireOrderDecomp

end FLT.KwDyf2XiEntireOrderDecomp

namespace FLT

namespace KwDyf2XiOrderBoundDecomp

end FLT.KwDyf2XiOrderBoundDecomp

namespace FLT

namespace KwDyf2XiStripBoundAttack

end FLT.KwDyf2XiStripBoundAttack

namespace FLT

namespace Gapsw48T2OdlyzkoDeg24PinCarrier

end FLT.Gapsw48T2OdlyzkoDeg24PinCarrier

namespace FLT

namespace Gapsw50T2ExplicitFormulaDecompositionPin

end FLT.Gapsw50T2ExplicitFormulaDecompositionPin

namespace FLT

namespace Gapsw52T2CarrierContentAtoms

end FLT.Gapsw52T2CarrierContentAtoms

namespace FLT

namespace Gapsw80T10DedekindZetaBridgeA1Discharge

end FLT.Gapsw80T10DedekindZetaBridgeA1Discharge

namespace FLT

namespace Gapsw80T11ExplicitFormulaA34Decomp

end FLT.Gapsw80T11ExplicitFormulaA34Decomp

namespace FLT

namespace Gapsw80T15XiOrderOneB1Decomp

end FLT.Gapsw80T15XiOrderOneB1Decomp

namespace FLT

namespace Gapsw80T16XiRightHalfBoundProof

end FLT.Gapsw80T16XiRightHalfBoundProof

namespace FLT

namespace Gapsw80T1OdlyzkoFoundationAtomDecomposition

end FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition

namespace FLT

namespace Gapsw80T21D2SubDecompWire

end FLT.Gapsw80T21D2SubDecompWire

namespace FLT

namespace Gapsw80T25B4pppStripSinglePointAbsorption

end FLT.Gapsw80T25B4pppStripSinglePointAbsorption

namespace FLT

namespace Gapsw80T2RankNGaussianPoisson

end FLT.Gapsw80T2RankNGaussianPoisson

namespace FLT

namespace Gapsw80T30D2d0cLocalEulerFactorProof

end FLT.Gapsw80T30D2d0cLocalEulerFactorProof

namespace FLT

namespace Gapsw80T31D1HadamardSubDecomp

end FLT.Gapsw80T31D1HadamardSubDecomp

namespace FLT

namespace Gapsw80T32D1aBoundaryCaseDecomp

end FLT.Gapsw80T32D1aBoundaryCaseDecomp

namespace FLT

namespace Gapsw80T35D1apa0ThreeFourOneIneqProof

end FLT.Gapsw80T35D1apa0ThreeFourOneIneqProof

namespace FLT

namespace Gapsw80T36D1appXiEndpointResidueProof

end FLT.Gapsw80T36D1appXiEndpointResidueProof

namespace FLT

namespace Gapsw80T37D1bGenericHadamardDecomp

end FLT.Gapsw80T37D1bGenericHadamardDecomp

namespace FLT

namespace Gapsw80T38D1b1CanonicalProductLogDerivProof

end FLT.Gapsw80T38D1b1CanonicalProductLogDerivProof

namespace FLT

namespace Gapsw80T39D1b0HadamardQuotientDecomp

end FLT.Gapsw80T39D1b0HadamardQuotientDecomp

namespace FLT

namespace Gapsw80T3IdealLatticeThetaTransformation

end FLT.Gapsw80T3IdealLatticeThetaTransformation

namespace FLT

namespace Gapsw80T40D1b0bZeroFreeExpLinearProof

end FLT.Gapsw80T40D1b0bZeroFreeExpLinearProof

namespace FLT

namespace Gapsw80T41D1b0aHadamardFactorSubDecomp

end FLT.Gapsw80T41D1b0aHadamardFactorSubDecomp

namespace FLT

namespace Gapsw80T42D1b0a0XiNonzeroInfZerosProof

end FLT.Gapsw80T42D1b0a0XiNonzeroInfZerosProof

namespace FLT

namespace Gapsw80T4MultiVarIdealThetaTransformation

end FLT.Gapsw80T4MultiVarIdealThetaTransformation

namespace FLT

namespace Gapsw80T5HeckeThetaKernel

end FLT.Gapsw80T5HeckeThetaKernel

namespace FLT

namespace Gapsw80T6TraceDualBridge

end FLT.Gapsw80T6TraceDualBridge

namespace FLT

namespace Gapsw80T7ClosedFEWeakPair

end FLT.Gapsw80T7ClosedFEWeakPair

namespace FLT

namespace Gapsw80T8MellinGammaPartialZeta

end FLT.Gapsw80T8MellinGammaPartialZeta

namespace FLT

namespace Gapsw80T9ClassSumA1Closure

end FLT.Gapsw80T9ClassSumA1Closure

namespace Filter

p2m_export "Filter" "mem_bot ker mk pi Tendsto pi_mono atTop EventuallyEq.rfl eventually_gt_atTop eventually_of_mem unique mk.injEq EventuallyEq map eventually_ge_atTop Eventually.of_forall"

p2m_open "Filter"

end Filter

namespace FourierTransform

p2m_export "FourierTransform" "mk"

p2m_open "FourierTransform"

end FourierTransform

namespace Ideal

p2m_export "Ideal" "absNorm_span_singleton absNorm_eq_zero_iff pi mem_bot span prod Quotient.mk map span_singleton_eq_top absNorm_ne_zero_iff_mem_nonZeroDivisors ext absNorm Quotient.lift finite_setOf_absNorm_eq card_norm_le_eq_card_norm_le_add_one subset_span absNorm_ne_zero_of_nonZeroDivisors absNorm_eq_one_iff"

p2m_open "Ideal"

end Ideal

namespace InnerProductSpace

p2m_export "InnerProductSpace" "mk"

p2m_open "InnerProductSpace"

end InnerProductSpace

namespace Matrix

p2m_export "Matrix" "PosDef.diagonal vecMul_fromBlocks det_smul J stdBasis transpose_one diagonal_one reindex diagonal_eq_diagonal_iff invOf_eq_nonsing_inv ext diagonal_transpose add sub_apply vecMul_sub map_apply smul_mulVec det_diagonal det_reindex_self sub zero fromBlocks_apply₁₁ exp_neg fromBlocks_apply₂₂ conjTranspose_eq_transpose_of_trivial det_one repr fromBlocks₂₂Invertible one_mulVec gram dotProduct_mulVec fromBlocks_apply₁₂ det_fin_zero IsHermitian transpose_apply fromBlocks_mulVec gram_eq_conjTranspose_mul nonsing_inv_mul transpose_transpose comp submatrix_apply isUnit_iff_isUnit_det toBlocks₂₂ add_mulVec fromBlocks_apply₂₁ det_transpose neg det_apply fromBlocks rank smul inv_eq_right_inv mulVec_mulVec det_mul zero_apply of_apply posDef_gram_of_linearIndependent single det_fromBlocks₂₂ posDef_iff_dotProduct_mulVec isHermitian_fromBlocks_iff mulVec_diagonal mulVec_injective_of_isUnit mulVec_sub ext_iff diagonal_mul one_apply mulVec_transpose neg_apply smul_apply toBlocks₁₂ PosDef vecMul_transpose toBlocks₂₁ det neg_mulVec toBlocks₁₁ diagonal inv_reindex add_apply comp_apply of smul_mul sum_apply transpose_smul fromBlocks_toBlocks inv invertibleOfIsUnitDet zpow_add_one map mulVec_zero discr single_apply mul_apply unique transpose_sub trace invOf_fromBlocks₂₂_eq transpose_mul vecMul_vecMul mulVec_smul transpose_nonsing_inv diagonal_mul_diagonal reindex_apply mul_inv_rev mulVec add_vecMul"

p2m_open "Matrix"

end Matrix

namespace MeasureTheory

p2m_export "MeasureTheory" "HasFiniteIntegral Measure.quasiMeasurePreserving_snd Measure.restrict_apply_univ Measure.smul_absolutelyContinuous integrable_const volume_preserving_piUnique lintegral_image_eq_lintegral_abs_det_fderiv_mul Measure Measure.volume_eq_prod setIntegral_congr_fun continuousOn_of_dominated MeasurePreserving lintegral_comp hasFiniteIntegral_iff_enorm integral_sub lintegral_prod integral_nonneg lintegral_congr measure_preimage_add integral_tsum setIntegral_const measurePreserving_vadd withDensity_absolutelyContinuous IntegrableOn volume_pi lintegral_withDensity_eq_lintegral_mul norm_setIntegral_le_of_norm_le_const Measure.prod_restrict Measure.ext_of_lintegral Measure.pi Measure.pi_pi ae_restrict_mem integrableOn_const Measure.measurePreserving_neg Measure.map enorm_integral_le_lintegral_enorm setIntegral_prod IsAddFundamentalDomain covolume IsFiniteMeasure lintegral_mono HasFiniteIntegral.mono' setLIntegral_univ setLIntegral_congr_fun AEStronglyMeasurable.tsum lintegral_map integral_fintype_prod_eq_prod integral_smul_measure VAddInvariantMeasure measureReal_def lintegral_tsum MeasurePreserving.id setIntegral_mono_on norm_integral_le_integral_norm ae_restrict_of_forall_mem Integrable lintegral_mono_ae lintegral_smul_measure setLIntegral_prod Measure.restrict_univ integral_add integral_const_mul integral_map AEStronglyMeasurable ofReal_integral_eq_lintegral_ofReal volume_preserving_piEquivPiSubtypeProd lintegral_const_mul' integrable_const_iff Measure.restrict_pi_pi ae_of_all"

p2m_open "MeasureTheory"

end MeasureTheory

namespace Module

p2m_export "Module" "Basis.map_repr Basis.coe_span_apply Basis.mem_span_iff_repr_mem Basis.repr_reindex_apply Free.ChooseBasisIndex Basis.span finrank_eq_card_basis Basis.toMatrix_apply finrank Free mk Finite.of_injective Basis.equivFun_symm_apply Basis.det_apply Basis.map_apply Basis.coe_reindex finrank_pos finrank_eq_card_chooseBasisIndex Basis"

p2m_open "Module"

end Module

namespace Nat

p2m_export "Nat" "cast_nonneg cast_ne_zero log_pos floor_le lt_floor_add_one card_eq_fintype_card log_pow log sqrt_one le_floor div_pos one_lt_ofNat add_le_add succ sqrt_pos card_eq_zero coe_castRingHom cast_sum factorial_le choose cast_eq_zero cast_natAbs cast_sub card_ne_zero card_univ sqrt cast_injective sqrt_le_sqrt zero_le eq_zero_or_pos cast_pos cast_le ne_of_gt card_fin cast_ofNat castRingHom one_le_cast pred sub_le succ_le_succ one_le_iff_ne_zero card_congr pow_succ' factorial_le_pow zero mul_eq_zero cast_one factorial_pos dist_zero_right"

p2m_open "Nat"

end Nat

namespace NumberField

p2m_export "NumberField" "InfinitePlace.nrRealPlaces mixedEmbedding.covolume_idealLattice discr mixedEmbedding.norm_apply mk mixedEmbedding.fundamentalCone mixedEmbedding.idealLattice fractionalIdeal_rank mixedEmbedding.norm_eq_norm RingOfIntegers InfinitePlace.nrComplexPlaces mixedEmbedding dedekindZeta InfinitePlace mixedEmbedding.stdBasis absNorm_differentIdeal discr_ne_zero mixedEmbedding_injective basisOfFractionalIdeal RingOfIntegers.rank Ideal.tendsto_norm_le_div_atTop₀ mixedEmbedding.norm mixedEmbedding.finrank ComplexEmbedding.conjugate_coe_eq mem_span_basisOfFractionalIdeal"

p2m_open "NumberField"

end NumberField

namespace NumberField

p2m_export "NumberField" "InfinitePlace.nrRealPlaces mixedEmbedding.covolume_idealLattice discr mixedEmbedding.norm_apply mk mixedEmbedding.fundamentalCone mixedEmbedding.idealLattice fractionalIdeal_rank mixedEmbedding.norm_eq_norm RingOfIntegers InfinitePlace.nrComplexPlaces mixedEmbedding dedekindZeta InfinitePlace mixedEmbedding.stdBasis absNorm_differentIdeal discr_ne_zero mixedEmbedding_injective basisOfFractionalIdeal RingOfIntegers.rank Ideal.tendsto_norm_le_div_atTop₀ mixedEmbedding.norm mixedEmbedding.finrank ComplexEmbedding.conjugate_coe_eq mem_span_basisOfFractionalIdeal"

namespace InfinitePlace

p2m_export "NumberField.InfinitePlace" "nrRealPlaces mult_isReal embedding_of_isReal_apply IsReal IsComplex smul_apply mult_isComplex card_eq_nrRealPlaces_add_nrComplexPlaces not_isComplex_iff_isReal mult_pos mult mk embedding_of_isReal not_isReal_iff_isComplex ext nrComplexPlaces pos_iff isReal_or_isComplex apply prod_eq_prod_mul_prod card_add_two_mul_card_eq_rank embedding"

p2m_open "NumberField.InfinitePlace NumberField"

end NumberField.InfinitePlace

namespace NumberField

p2m_export "NumberField" "InfinitePlace.nrRealPlaces mixedEmbedding.covolume_idealLattice discr mixedEmbedding.norm_apply mk mixedEmbedding.fundamentalCone mixedEmbedding.idealLattice fractionalIdeal_rank mixedEmbedding.norm_eq_norm RingOfIntegers InfinitePlace.nrComplexPlaces mixedEmbedding dedekindZeta InfinitePlace mixedEmbedding.stdBasis absNorm_differentIdeal discr_ne_zero mixedEmbedding_injective basisOfFractionalIdeal RingOfIntegers.rank Ideal.tendsto_norm_le_div_atTop₀ mixedEmbedding.norm mixedEmbedding.finrank ComplexEmbedding.conjugate_coe_eq mem_span_basisOfFractionalIdeal"

namespace Units

p2m_export "NumberField.Units" "fundSystem pos_at_place rank regulator_pos torsionOrder equivFinRank exist_unique_eq_mul_prod mem_torsion torsion coe_coe regulator torsionOrder_pos"

p2m_open "NumberField.Units NumberField"

end NumberField.Units

namespace NumberField

p2m_export "NumberField" "InfinitePlace.nrRealPlaces mixedEmbedding.covolume_idealLattice discr mixedEmbedding.norm_apply mk mixedEmbedding.fundamentalCone mixedEmbedding.idealLattice fractionalIdeal_rank mixedEmbedding.norm_eq_norm RingOfIntegers InfinitePlace.nrComplexPlaces mixedEmbedding dedekindZeta InfinitePlace mixedEmbedding.stdBasis absNorm_differentIdeal discr_ne_zero mixedEmbedding_injective basisOfFractionalIdeal RingOfIntegers.rank Ideal.tendsto_norm_le_div_atTop₀ mixedEmbedding.norm mixedEmbedding.finrank ComplexEmbedding.conjugate_coe_eq mem_span_basisOfFractionalIdeal"

namespace Units

p2m_export "NumberField.Units" "fundSystem pos_at_place rank regulator_pos torsionOrder equivFinRank exist_unique_eq_mul_prod mem_torsion torsion coe_coe regulator torsionOrder_pos"

namespace dirichletUnitTheorem

p2m_export "NumberField.Units.dirichletUnitTheorem" "w₀ logSpace"

p2m_open "NumberField.Units.dirichletUnitTheorem NumberField.Units NumberField"

end NumberField.Units.dirichletUnitTheorem

namespace NumberField

p2m_export "NumberField" "InfinitePlace.nrRealPlaces mixedEmbedding.covolume_idealLattice discr mixedEmbedding.norm_apply mk mixedEmbedding.fundamentalCone mixedEmbedding.idealLattice fractionalIdeal_rank mixedEmbedding.norm_eq_norm RingOfIntegers InfinitePlace.nrComplexPlaces mixedEmbedding dedekindZeta InfinitePlace mixedEmbedding.stdBasis absNorm_differentIdeal discr_ne_zero mixedEmbedding_injective basisOfFractionalIdeal RingOfIntegers.rank Ideal.tendsto_norm_le_div_atTop₀ mixedEmbedding.norm mixedEmbedding.finrank ComplexEmbedding.conjugate_coe_eq mem_span_basisOfFractionalIdeal"

namespace mixedEmbedding

p2m_export "NumberField.mixedEmbedding" "indexEquiv mem_idealLattice covolume_idealLattice euclidean.toMixed index norm_real euclidean.stdOrthonormalBasis normAtAllPlaces indexEquiv_apply_isComplex_snd mixedEmbedding_apply_isComplex euclidean.stdOrthonormalBasis_map_eq volume_fundamentalDomain_stdBasis fundamentalCone idealLattice normAtPlace norm_eq_norm fractionalIdealLatticeBasis normAtPlace_nonneg stdBasis_apply_isReal mixedSpace mixedEmbedding_apply_isReal indexEquiv_apply_isReal euclidean.mixedSpace stdBasis unitSMul_smul indexEquiv_apply_isComplex_fst stdBasis_apply_isComplex_snd normAtPlace_apply fractionalIdealLatticeBasis_apply span_idealLatticeBasis normAtAllPlaces_apply normAtPlace_apply_of_isReal norm_smul stdBasis_apply_isComplex_fst realSpace normAtPlace_apply_of_isComplex"

p2m_open "NumberField.mixedEmbedding NumberField"

end NumberField.mixedEmbedding

namespace NumberField

p2m_export "NumberField" "InfinitePlace.nrRealPlaces mixedEmbedding.covolume_idealLattice discr mixedEmbedding.norm_apply mk mixedEmbedding.fundamentalCone mixedEmbedding.idealLattice fractionalIdeal_rank mixedEmbedding.norm_eq_norm RingOfIntegers InfinitePlace.nrComplexPlaces mixedEmbedding dedekindZeta InfinitePlace mixedEmbedding.stdBasis absNorm_differentIdeal discr_ne_zero mixedEmbedding_injective basisOfFractionalIdeal RingOfIntegers.rank Ideal.tendsto_norm_le_div_atTop₀ mixedEmbedding.norm mixedEmbedding.finrank ComplexEmbedding.conjugate_coe_eq mem_span_basisOfFractionalIdeal"

namespace mixedEmbedding

p2m_export "NumberField.mixedEmbedding" "indexEquiv mem_idealLattice covolume_idealLattice euclidean.toMixed index norm_real euclidean.stdOrthonormalBasis normAtAllPlaces indexEquiv_apply_isComplex_snd mixedEmbedding_apply_isComplex euclidean.stdOrthonormalBasis_map_eq volume_fundamentalDomain_stdBasis fundamentalCone idealLattice normAtPlace norm_eq_norm fractionalIdealLatticeBasis normAtPlace_nonneg stdBasis_apply_isReal mixedSpace mixedEmbedding_apply_isReal indexEquiv_apply_isReal euclidean.mixedSpace stdBasis unitSMul_smul indexEquiv_apply_isComplex_fst stdBasis_apply_isComplex_snd normAtPlace_apply fractionalIdealLatticeBasis_apply span_idealLatticeBasis normAtAllPlaces_apply normAtPlace_apply_of_isReal norm_smul stdBasis_apply_isComplex_fst realSpace normAtPlace_apply_of_isComplex"

namespace fundamentalCone

p2m_export "NumberField.mixedEmbedding.fundamentalCone" "prod_expMapBasis_pow expMapBasis_apply completeBasis_apply_of_ne expMap_target expMap_apply setLIntegral_expMapBasis_image expMapBasis_pos expMapBasis_apply' expMap equivFinRank completeBasis continuous_expMapBasis expMapBasis expMap_add"

p2m_open "NumberField.mixedEmbedding.fundamentalCone NumberField.mixedEmbedding NumberField"

end NumberField.mixedEmbedding.fundamentalCone

namespace Real

p2m_export "Real" "sqrt_pos log_le_sub_one_of_pos log_pos continuous_const_rpow norm volume_Ico norm_natCast log_nonneg exp_zero sqrt_le_sqrt rpow_mul pi_ne_zero pi_gt_three rpow_nonneg log_zero continuousOn_log log_exp measurable_exp sqrt_sq_eq_abs Gamma convexOn_log_Gamma log_inv two_le_pi Gamma_nat_eq_factorial exp_nat_mul exp_one_lt_d9 exp Gamma_ne_zero tendsto_log_atTop rpow_two exp_pos exp_le_exp sqrt_nonneg exp_nonneg measurable_log pi_nonneg rpow_le_rpow_of_exponent_le rpow_neg_one exp_sum rpow_neg log_rpow sqrt_one rpow_pos_of_pos rpow_natCast continuousAt_rpow_const continuous_exp log norm_of_nonneg norm_eq_abs exp_neg inv_rpow inner_apply mk pi_pos exp_log Gamma_eq_integral Gamma_add_one log_mul summable_abs_int_rpow rpow_one sq_sqrt log_le_log one_le_rpow mul_rpow rpow_le_rpow_of_exponent_ge hasDerivAt_log le_log_iff_exp_le add_one_le_exp exp_add sqrt_sq log_pow log_div sqrt"

p2m_open "Real"

end Real

namespace RealInnerProductSpace

p2m_open "RealInnerProductSpace"

end RealInnerProductSpace

namespace Set

p2m_export "Set" "eq_univ_of_forall exists_min_image restrict prod_pow indicator_apply univ_nonempty Icc diagonal Icc_succ_left_eq_Ioc mem_compl_iff ext univ_prod finite_singleton coe_eq_subtype mem_univ_pi pi Ioc unit card_singleton MapsTo mem_singleton_iff mem_univ pi_mono Ioi EqOn mem_Ici prod_insert mapsTo_univ Countable.isConnected_compl_of_one_lt_rank mem_singleton InjOn Ici mem_setOf_eq Ico_subset_Icc_self mem_insert_iff univ Ico mem_insert prod prod_empty range mem_Ioi mem_iInter"

p2m_open "Set"

end Set

namespace Topology

p2m_open "Topology"

end Topology

namespace WithLp

p2m_export "WithLp" "toLp ofLp"

p2m_open "WithLp"

end WithLp

section

set_option maxHeartbeats 999999

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation"

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation"

section

set_option maxHeartbeats 999999

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation"

section

set_option maxHeartbeats 999999

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel"

section

set_option maxHeartbeats 999999

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge"

section

set_option maxHeartbeats 999999

noncomputable section

namespace FLT

namespace Gapsw80T7ClosedFEWeakPair

p2m_open "NumberField P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField NumberField.InfinitePlace P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.InfinitePlace NumberField.mixedEmbedding P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.mixedEmbedding"

p2m_open "NumberField.mixedEmbedding.fundamentalCone P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.mixedEmbedding.fundamentalCone"

p2m_open "NumberField.Units P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.Units NumberField.Units.dirichletUnitTheorem P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.Units.dirichletUnitTheorem"

open FLT.Gapsw80T2RankNGaussianPoisson FLT.Gapsw80T3IdealLatticeThetaTransformation

open FLT.Gapsw80T4MultiVarIdealThetaTransformation FLT.Gapsw80T5HeckeThetaKernel

open FLT.Gapsw80T6TraceDualBridge

p2m_open "Matrix P2MW.S_NumberField_exists_completedDedekindZeta_package.Matrix Complex P2MW.S_NumberField_exists_completedDedekindZeta_package.Complex Module P2MW.S_NumberField_exists_completedDedekindZeta_package.Module Matrix.Module Real P2MW.S_NumberField_exists_completedDedekindZeta_package.Real MeasureTheory P2MW.S_NumberField_exists_completedDedekindZeta_package.MeasureTheory Asymptotics P2MW.S_NumberField_exists_completedDedekindZeta_package.Asymptotics Filter P2MW.S_NumberField_exists_completedDedekindZeta_package.Filter Asymptotics.Filter Set P2MW.S_NumberField_exists_completedDedekindZeta_package.Set"

p2m_open_scoped "Classical P2MW.S_NumberField_exists_completedDedekindZeta_package.Classical InnerProductSpace P2MW.S_NumberField_exists_completedDedekindZeta_package.InnerProductSpace nonZeroDivisors Topology P2MW.S_NumberField_exists_completedDedekindZeta_package.Topology"

variable (K : Type) [Field K] [NumberField K]

theorem unitPart_pos (u : logSpace K) (w : InfinitePlace K) :
    0 < gapsw80_t7_unitPart K u w := by
  refine pow_pos (Finset.prod_pos fun i _ => ?_) 2
  exact Real.rpow_pos_of_pos (pos_iff.mpr (by simp)) _

theorem gapsw80_t7_yParam_mkParam_factor {t : ℝ} (ht : 0 < t) (u : logSpace K)
    (w : InfinitePlace K) :
    gapsw80_t5_yParam K (gapsw80_t5_mkParam K (Real.log t / 2) u) w
      = t * gapsw80_t7_unitPart K u w := by
  unfold gapsw80_t5_yParam gapsw80_t7_unitPart
  rw [expMapBasis_apply']
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, mkParam_w₀,
    ← Real.exp_nat_mul, show (2:ℕ) * (Real.log t / 2) = Real.log t by ring, Real.exp_log ht]
  congr 2
  exact Finset.prod_congr rfl fun i _ => by rw [mkParam_ne K i.2]

theorem continuous_unitPart (w : InfinitePlace K) :
    Continuous fun u : logSpace K => gapsw80_t7_unitPart K u w := by
  unfold gapsw80_t7_unitPart
  refine (continuous_finset_prod _ fun i _ => ?_).pow 2
  exact (Real.continuous_const_rpow
    (pos_iff.mpr (by simp [fundSystem])).ne').comp (continuous_apply i)

theorem gapsw80_t7_unitPart_lower_bound :
    ∃ c > 0, ∀ u ∈ (Set.univ.pi fun _ : {w : InfinitePlace K // w ≠ w₀} => Set.Icc (0:ℝ) 1),
      ∀ w, c ≤ gapsw80_t7_unitPart K u w := by
  have hcpct : IsCompact (Set.univ.pi fun _ : {w : InfinitePlace K // w ≠ w₀} => Icc (0:ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hne : (Set.univ.pi fun _ : {w : InfinitePlace K // w ≠ w₀} => Icc (0:ℝ) 1).Nonempty :=
    ⟨0, fun i _ => by simp⟩

  have hw : ∀ w : InfinitePlace K, ∃ c > 0,
      ∀ u ∈ (Set.univ.pi fun _ : {w : InfinitePlace K // w ≠ w₀} => Icc (0:ℝ) 1),
        c ≤ gapsw80_t7_unitPart K u w := fun w => by
    obtain ⟨u₀, hu₀, hmin⟩ := hcpct.exists_isMinOn hne (continuous_unitPart K w).continuousOn
    exact ⟨gapsw80_t7_unitPart K u₀ w, unitPart_pos K u₀ w, fun u hu => hmin hu⟩
  choose c hcpos hc using hw
  refine ⟨Finset.univ.inf' ⟨w₀, Finset.mem_univ _⟩ c, ?_, fun u hu w => ?_⟩
  · exact (Finset.lt_inf'_iff _).mpr fun w _ => hcpos w
  · exact (Finset.inf'_le c (Finset.mem_univ w)).trans (hc w u hu)

theorem isCompact_sum_sq_eq_one :
    IsCompact {w : Fin (nK K) → ℝ | ∑ i, w i ^ 2 = 1} := by
  have hclosed : IsClosed {w : Fin (nK K) → ℝ | ∑ i, w i ^ 2 = 1} :=
    isClosed_eq (by fun_prop) continuous_const
  have hbdd : {w : Fin (nK K) → ℝ | ∑ i, w i ^ 2 = 1} ⊆ Metric.closedBall 0 1 := by
    intro w hw
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    have hle : w i ^ 2 ≤ 1 :=
      (Finset.single_le_sum (fun j _ => sq_nonneg (w j)) (Finset.mem_univ i)).trans_eq hw
    calc ‖w i‖ = |w i| := Real.norm_eq_abs _
      _ = √(w i ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ √1 := Real.sqrt_le_sqrt hle
      _ = 1 := Real.sqrt_one
  exact (Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨hclosed, Metric.isBounded_closedBall.subset hbdd⟩)

theorem gapsw80_t7_idealGram_lower_bound (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ lam > 0, ∀ v : Fin (nK K) → ℤ,
      lam * ∑ i, (v i : ℝ)^2 ≤ zcastR v ⬝ᵥ (gapsw80_t3_idealGram K I) *ᵥ zcastR v := by
  set F : (Fin (nK K) → ℝ) → ℝ := fun w => w ⬝ᵥ (gapsw80_t3_idealGram K I) *ᵥ w with hF
  have hFcont : Continuous F := by unfold F; fun_prop
  have hFscale : ∀ (c : ℝ) (w : Fin (nK K) → ℝ), F (c • w) = c^2 * F w := fun c w => by
    simp only [hF, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, sq, mul_assoc]
  have hSne : {w : Fin (nK K) → ℝ | ∑ i, w i ^ 2 = 1}.Nonempty := by
    refine ⟨Pi.single (⟨0, Module.finrank_pos⟩ : Fin (nK K)) 1, ?_⟩
    simp only [Set.mem_setOf_eq, Pi.single_apply, ite_pow, one_pow, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  obtain ⟨ww, hww, hmin⟩ := (isCompact_sum_sq_eq_one K).exists_isMinOn hSne hFcont.continuousOn
  have hne : ww ≠ 0 := fun habs => by rw [habs] at hww; simp at hww
  have hlam : 0 < F ww := by
    have h := (gapsw80_t3_idealGram_posDef K I).dotProduct_mulVec_pos hne
    simpa [hF] using h
  refine ⟨F ww, hlam, fun v => ?_⟩
  by_cases hv : zcastR v = 0
  · have hsum0 : ∑ i, (v i : ℝ)^2 = 0 := Finset.sum_eq_zero fun i _ => by
      have h0 : (v i : ℝ) = 0 := congr_fun hv i; rw [h0]; ring
    simp only [hsum0, mul_zero, hv, hF, Matrix.mulVec_zero, dotProduct_zero, le_refl]
  ·
    set s : ℝ := Real.sqrt (∑ i, (v i : ℝ)^2) with hs_def
    have hsumpos : 0 < ∑ i, (v i : ℝ)^2 := by
      refine Finset.sum_pos' (fun i _ => sq_nonneg _) ?_
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
      exact ⟨i, Finset.mem_univ i, by
        simp only [zcastR, Pi.zero_apply] at hi; positivity⟩
    have hspos : 0 < s := Real.sqrt_pos.mpr hsumpos
    have hs_sq : s^2 = ∑ i, (v i : ℝ)^2 := Real.sq_sqrt hsumpos.le
    have hmem : s⁻¹ • zcastR v ∈ {w : Fin (nK K) → ℝ | ∑ i, w i ^ 2 = 1} := by
      simp only [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum,
        ← hs_sq, inv_pow]
      exact inv_mul_cancel₀ (pow_ne_zero 2 hspos.ne')
    calc F ww * ∑ i, (v i : ℝ)^2
        = s^2 * F ww := by rw [hs_sq, mul_comm]
      _ ≤ s^2 * F (s⁻¹ • zcastR v) :=
          mul_le_mul_of_nonneg_left (hmin hmem) (sq_nonneg s)
      _ = F (s • (s⁻¹ • zcastR v)) := (hFscale s _).symm
      _ = zcastR v ⬝ᵥ (gapsw80_t3_idealGram K I) *ᵥ zcastR v := by
          rw [smul_smul, mul_inv_cancel₀ hspos.ne', one_smul]

theorem multiIdealTheta_zero_term (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (y : InfinitePlace K → ℝ) :
    cexp ((-(π * (zcastR (0 : Fin (nK K) → ℤ) ⬝ᵥ (gapsw80_t4_scaledGram K I y)
      *ᵥ zcastR 0)) : ℝ) : ℂ) = 1 := by
  simp [zcastR, dotProduct]

theorem scaledGram_lower_bound (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {c : ℝ}
    {y : InfinitePlace K → ℝ} (hy : ∀ w, c ≤ y w) (v : Fin (nK K) → ℤ) :
    c * (zcastR v ⬝ᵥ (gapsw80_t3_idealGram K I) *ᵥ zcastR v)
      ≤ zcastR v ⬝ᵥ (gapsw80_t4_scaledGram K I y) *ᵥ zcastR v := by
  have hGram1 : gapsw80_t3_idealGram K I = gapsw80_t4_scaledGram K I (fun _ => (1:ℝ)) := by
    rw [gapsw80_t4_scaledGram_const_eq, one_smul]
  rw [hGram1, gapsw80_t4_quadForm_scaledGram, gapsw80_t4_quadForm_scaledGram, Finset.mul_sum]
  exact Finset.sum_le_sum fun w _ => by
    rw [one_mul]; exact mul_le_mul_of_nonneg_right (hy w) (sq_nonneg _)

theorem one_le_sum_sq_of_ne_zero {v : Fin (nK K) → ℤ} (hv : v ≠ 0) :
    (1 : ℝ) ≤ ∑ i, (v i : ℝ)^2 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  have h1 : (1:ℝ) ≤ (v i : ℝ)^2 := by
    have : (1:ℤ) ≤ |v i| := Int.one_le_abs (by simpa using hi)
    have habs : (1:ℝ) ≤ |(v i : ℝ)| := by exact_mod_cast this
    calc (1:ℝ) = (1:ℝ)^2 := (one_pow 2).symm
      _ ≤ |(v i:ℝ)|^2 := pow_le_pow_left₀ zero_le_one habs 2
      _ = (v i:ℝ)^2 := sq_abs _
  have h2 : (v i : ℝ)^2 ≤ ∑ j, (v j : ℝ)^2 :=
    Finset.single_le_sum (f := fun j => (v j : ℝ)^2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  linarith

theorem gapsw80_t7_summable_dom_gaussian {lam : ℝ} (hlam : 0 < lam) :
    Summable fun v : Fin (nK K) → ℤ => rexp (-(π * lam * ∑ i, (v i : ℝ)^2)) := by
  have h := gapsw80_t2_summable_gaussian_Zn (n := nK K) (c := π * lam) (by positivity)
  exact h.congr fun v => by ring_nf

theorem gapsw80_t7_theta_sub_one_exp_bound (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ C p, 0 < p ∧ ∀ {c : ℝ}, 1 ≤ c →
      ∀ {y : InfinitePlace K → ℝ}, (∀ w, c ≤ y w) →
        ‖gapsw80_t4_multiIdealTheta K I y - 1‖ ≤ C * Real.exp (-(p * c)) := by
  obtain ⟨lam, hlam, hGram⟩ := gapsw80_t7_idealGram_lower_bound K I
  set p := π * lam with hp_def
  have hp : 0 < p := by positivity
  have hsum : Summable fun v : Fin (nK K) → ℤ => rexp (-(p * ∑ i, (v i:ℝ)^2)) :=
    gapsw80_t7_summable_dom_gaussian K hlam
  set C := rexp p * ∑' v : Fin (nK K) → ℤ, rexp (-(p * ∑ i, (v i:ℝ)^2)) with hC_def
  refine ⟨C, p, hp, fun {c} hc {y} hy => ?_⟩

  let f : (Fin (nK K) → ℤ) → ℂ := fun v =>
    cexp ((-(π * (zcastR v ⬝ᵥ (gapsw80_t4_scaledGram K I y) *ᵥ zcastR v)) : ℝ) : ℂ)
  have hzero : f 0 = 1 := multiIdealTheta_zero_term K I y

  have hterm : ∀ v, ‖f v‖ ≤ rexp (-(p * c * ∑ i, (v i:ℝ)^2)) := fun v => by
    show ‖cexp _‖ ≤ _
    rw [Complex.norm_exp, Complex.ofReal_re]
    refine Real.exp_le_exp.mpr (neg_le_neg ?_)
    calc p * c * ∑ i, (v i:ℝ)^2
        = π * (c * (lam * ∑ i, (v i:ℝ)^2)) := by ring
      _ ≤ π * (c * (zcastR v ⬝ᵥ (gapsw80_t3_idealGram K I) *ᵥ zcastR v)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hGram v) (by linarith)) Real.pi_nonneg
      _ ≤ π * (zcastR v ⬝ᵥ (gapsw80_t4_scaledGram K I y) *ᵥ zcastR v) :=
          mul_le_mul_of_nonneg_left (scaledGram_lower_bound K I hy v) Real.pi_nonneg

  have hdom : ∀ v : Fin (nK K) → ℤ,
      rexp (-(p * c * ∑ i, (v i:ℝ)^2)) ≤ rexp (-(p * ∑ i, (v i:ℝ)^2)) := fun v => by
    refine Real.exp_le_exp.mpr (neg_le_neg ?_)
    have hs : (0:ℝ) ≤ ∑ i, (v i : ℝ)^2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    nlinarith [mul_nonneg (mul_nonneg hp.le (sub_nonneg.mpr hc)) hs]
  have hsplit : ∀ {v : Fin (nK K) → ℤ}, v ≠ 0 →
      rexp (-(p * c * ∑ i, (v i:ℝ)^2)) ≤ rexp (-(p*(c-1))) * rexp (-(p * ∑ i, (v i:ℝ)^2)) := by
    intro v hv
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have h1 := one_le_sum_sq_of_ne_zero K hv
    nlinarith [mul_nonneg (mul_nonneg hp.le (sub_nonneg.mpr hc)) (sub_nonneg.mpr h1)]

  have hfullnorm : Summable fun v => ‖f v‖ :=
    hsum.of_nonneg_of_le (fun v => norm_nonneg _) (fun v => (hterm v).trans (hdom v))
  have hfullsum : Summable f := hfullnorm.of_norm
  have htail_summable : Summable fun v : Fin (nK K) → ℤ =>
      if v = 0 then (0:ℝ) else rexp (-(p * c * ∑ i, (v i:ℝ)^2)) := by
    refine hsum.of_nonneg_of_le (fun v => ?_) (fun v => ?_)
    · split_ifs <;> positivity
    · split_ifs with h
      · positivity
      · exact hdom v
  have hite_norm_summable : Summable fun v : Fin (nK K) → ℤ =>
      ‖if v = (0 : Fin (nK K) → ℤ) then (0:ℂ) else f v‖ := by
    refine hfullnorm.of_nonneg_of_le (fun v => norm_nonneg _) (fun v => ?_)
    split_ifs <;> simp

  have hTheta : gapsw80_t4_multiIdealTheta K I y - 1
      = ∑' v, if v = 0 then 0 else f v := by
    have heq : gapsw80_t4_multiIdealTheta K I y = ∑' v, f v := rfl
    rw [heq, hfullsum.tsum_eq_add_tsum_ite 0, hzero, add_sub_cancel_left]
  rw [hTheta]
  calc ‖∑' v, if v = 0 then 0 else f v‖
      ≤ ∑' v, ‖if v = (0 : Fin (nK K) → ℤ) then (0:ℂ) else f v‖ :=
        norm_tsum_le_tsum_norm hite_norm_summable
    _ ≤ ∑' v, if v = (0 : Fin (nK K) → ℤ) then (0:ℝ) else rexp (-(p*c*∑ i, (v i:ℝ)^2)) := by
        refine hite_norm_summable.tsum_le_tsum (fun v => ?_) htail_summable
        split_ifs with h
        · simp
        · exact hterm v
    _ ≤ ∑' v : Fin (nK K) → ℤ, rexp (-(p*(c-1))) * rexp (-(p * ∑ i, (v i:ℝ)^2)) := by
        refine htail_summable.tsum_le_tsum (fun v => ?_) (hsum.mul_left _)
        split_ifs with h
        · positivity
        · exact hsplit h
    _ = C * rexp (-(p * c)) := by
        rw [tsum_mul_left, hC_def,
          show -(p*(c-1)) = p + (-(p*c)) from by ring, Real.exp_add]
        ring

theorem continuous_theta_term (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (v : Fin (nK K) → ℤ) :
    Continuous fun y : InfinitePlace K → ℝ =>
      cexp ((-(π * (zcastR v ⬝ᵥ (gapsw80_t4_scaledGram K I y) *ᵥ zcastR v)) : ℝ) : ℂ) := by
  refine Complex.continuous_exp.comp (Complex.continuous_ofReal.comp (Continuous.neg ?_))
  refine continuous_const.mul ?_
  simp only [gapsw80_t4_quadForm_scaledGram]
  exact continuous_finset_sum _ fun w _ => (continuous_apply w).mul continuous_const

theorem gapsw80_t7_continuousOn_multiIdealTheta_ge (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {c : ℝ} (hc : 0 < c) :
    ContinuousOn (gapsw80_t4_multiIdealTheta K I) {y | ∀ w, c ≤ y w} := by
  obtain ⟨lam, hlam, hGram⟩ := gapsw80_t7_idealGram_lower_bound K I
  refine continuousOn_tsum (fun v => (continuous_theta_term K I v).continuousOn)
    (gapsw80_t7_summable_dom_gaussian K (mul_pos hc hlam)) (fun v y hy => ?_)
  rw [Complex.norm_exp, Complex.ofReal_re]
  refine Real.exp_le_exp.mpr (neg_le_neg ?_)
  calc π * (c * lam) * ∑ i, (v i:ℝ)^2
      = π * (c * (lam * ∑ i, (v i:ℝ)^2)) := by ring
    _ ≤ π * (c * (zcastR v ⬝ᵥ (gapsw80_t3_idealGram K I) *ᵥ zcastR v)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hGram v) hc.le) Real.pi_nonneg
    _ ≤ π * (zcastR v ⬝ᵥ (gapsw80_t4_scaledGram K I y) *ᵥ zcastR v) :=
        mul_le_mul_of_nonneg_left (scaledGram_lower_bound K I hy v) Real.pi_nonneg

theorem gapsw80_t7_continuousOn_multiIdealTheta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ContinuousOn (gapsw80_t4_multiIdealTheta K I) {y | ∀ w, 0 < y w} := by
  intro y hy
  set c := Finset.univ.inf' ⟨w₀, Finset.mem_univ _⟩ (fun w => y w / 2) with hc_def
  have hc : 0 < c := (Finset.lt_inf'_iff _).mpr fun w _ => half_pos (hy w)
  have hy' : y ∈ {z | ∀ w, c ≤ z w} := fun w =>
    (Finset.inf'_le _ (Finset.mem_univ w)).trans (half_le_self (hy w).le)
  have hopen : IsOpen {z : InfinitePlace K → ℝ | ∀ w, c < z w} := by
    have : {z : InfinitePlace K → ℝ | ∀ w, c < z w} = ⋂ w, {z | c < z w} := by
      ext z; simp [Set.mem_iInter]
    rw [this]; exact isOpen_iInter_of_finite fun w => isOpen_lt continuous_const (continuous_apply w)
  have hy'' : y ∈ {z | ∀ w, c < z w} := fun w =>
    (Finset.inf'_le _ (Finset.mem_univ w)).trans_lt (by linarith [half_lt_self (hy w)])

  refine ContinuousWithinAt.mono_of_mem_nhdsWithin ?_
    (mem_nhdsWithin_of_mem_nhds (hopen.mem_nhds hy''))
  exact ((gapsw80_t7_continuousOn_multiIdealTheta_ge K I hc) y hy').mono
    (fun z hz w => (hz w).le)

theorem continuous_mkParam (r : ℝ) :
    Continuous fun u : logSpace K => gapsw80_t5_mkParam K r u := by
  refine continuous_pi fun w => ?_
  unfold gapsw80_t5_mkParam
  split_ifs
  · exact continuous_const
  · exact continuous_apply _

theorem continuous_genericKernel_integrand (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (r : ℝ)
    (scale : realSpace K) (hscale : ∀ w, 0 < scale w) :
    Continuous fun u : logSpace K =>
      gapsw80_t4_multiIdealTheta K I
        (scale * gapsw80_t5_yParam K (gapsw80_t5_mkParam K r u)) := by
  have hyP : Continuous fun u : logSpace K =>
      scale * gapsw80_t5_yParam K (gapsw80_t5_mkParam K r u) := by
    refine continuous_pi fun w => ?_
    exact continuous_const.mul
      (((continuous_apply w).comp ((continuous_expMapBasis K).comp (continuous_mkParam K r))).pow 2)
  refine ContinuousOn.comp_continuous (gapsw80_t7_continuousOn_multiIdealTheta K I) hyP ?_
  exact fun u w => mul_pos (hscale w) (yParam_pos K _ w)

theorem volume_unitBox_eq_one : volume (gapsw80_t7_unitBox K) = 1 := by
  rw [volume_pi, Measure.pi_pi]
  simp [Real.volume_Ico]

theorem volume_unitBox_lt_top : volume (gapsw80_t7_unitBox K) < ⊤ := by
  rw [volume_unitBox_eq_one]; exact ENNReal.one_lt_top

theorem gapsw80_t7_continuousOn_genericKernel (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (scale : realSpace K) (hscale : ∀ w, 1 ≤ scale w) :
    ContinuousOn (fun t : ℝ => ∫ u in gapsw80_t7_unitBox K,
      gapsw80_t4_multiIdealTheta K I
        (scale * gapsw80_t5_yParam K (gapsw80_t5_mkParam K (Real.log t / 2) u)) ∂volume)
      (Set.Ioi 0) := by
  have hscale' : ∀ w, 0 < scale w := fun w => lt_of_lt_of_le one_pos (hscale w)
  obtain ⟨cK, hcK, hLB⟩ := gapsw80_t7_unitPart_lower_bound K
  obtain ⟨C, p, hp, hbound⟩ := gapsw80_t7_theta_sub_one_exp_bound K I
  haveI hfin : IsFiniteMeasure (volume.restrict (gapsw80_t7_unitBox K)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact volume_unitBox_lt_top K⟩

  intro t₀ ht₀
  have ht₀' : (0:ℝ) < t₀ := ht₀
  set s := Set.Icc (t₀/2) (t₀+1) with hs_def
  have hsnhds : s ∈ 𝓝 t₀ := Icc_mem_nhds (by linarith) (by linarith)
  have hssub : s ⊆ Ioi 0 := fun t ht => lt_of_lt_of_le (by linarith) ht.1
  set c₀ : ℝ := cK * (t₀/2)
  have hc₀ : 0 < c₀ := mul_pos hcK (by linarith)
  obtain ⟨lam, hlam, hGram⟩ := gapsw80_t7_idealGram_lower_bound K I
  set M : ℝ := ∑' v : Fin (nK K) → ℤ, rexp (-(π * (c₀ * lam) * ∑ i, (v i:ℝ)^2)) with hM_def
  have hMsum := gapsw80_t7_summable_dom_gaussian K (mul_pos hc₀ hlam)

  have hy_lb : ∀ t ∈ s, ∀ u ∈ gapsw80_t7_unitBox K, ∀ w,
      c₀ ≤ (scale * gapsw80_t5_yParam K (gapsw80_t5_mkParam K (Real.log t / 2) u)) w := by
    intro t ht u hu w
    have ht' : (0:ℝ) < t := hssub ht
    rw [Pi.mul_apply, gapsw80_t7_yParam_mkParam_factor K ht']
    have huIcc : u ∈ (Set.univ.pi fun _ : {w // w ≠ w₀} => Icc (0:ℝ) 1) :=
      fun i hi => Ico_subset_Icc_self (hu i hi)
    have huP : 0 < gapsw80_t7_unitPart K u w := unitPart_pos K u w
    calc c₀ = cK * (t₀/2) := rfl
      _ ≤ gapsw80_t7_unitPart K u w * t :=
          mul_le_mul (hLB u huIcc w) ht.1 (by linarith) huP.le
      _ = 1 * (t * gapsw80_t7_unitPart K u w) := by ring
      _ ≤ scale w * (t * gapsw80_t7_unitPart K u w) :=
          mul_le_mul_of_nonneg_right (hscale w) (by positivity)

  have hTheta_bound : ∀ t ∈ s, ∀ u ∈ gapsw80_t7_unitBox K,
      ‖gapsw80_t4_multiIdealTheta K I
        (scale * gapsw80_t5_yParam K (gapsw80_t5_mkParam K (Real.log t / 2) u))‖ ≤ M := by
    intro t ht u hu
    unfold gapsw80_t4_multiIdealTheta
    refine (norm_tsum_le_tsum_norm ?_).trans ?_
    · exact hMsum.of_nonneg_of_le (fun v => norm_nonneg _) (fun v => by
        rw [Complex.norm_exp, Complex.ofReal_re]
        exact Real.exp_le_exp.mpr (neg_le_neg (by
          calc π * (c₀ * lam) * ∑ i, (v i:ℝ)^2
              = π * (c₀ * (lam * ∑ i, (v i:ℝ)^2)) := by ring
            _ ≤ π * (c₀ * (zcastR v ⬝ᵥ (gapsw80_t3_idealGram K I) *ᵥ zcastR v)) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left (hGram v) hc₀.le) Real.pi_nonneg
            _ ≤ π * (zcastR v ⬝ᵥ (gapsw80_t4_scaledGram K I _) *ᵥ zcastR v) :=
                mul_le_mul_of_nonneg_left
                  (scaledGram_lower_bound K I (hy_lb t ht u hu) v) Real.pi_nonneg)))
    · refine (Summable.tsum_le_tsum (fun v => ?_) ?_ hMsum)
      · rw [Complex.norm_exp, Complex.ofReal_re]
        exact Real.exp_le_exp.mpr (neg_le_neg (by
          calc π * (c₀ * lam) * ∑ i, (v i:ℝ)^2
              = π * (c₀ * (lam * ∑ i, (v i:ℝ)^2)) := by ring
            _ ≤ π * (c₀ * (zcastR v ⬝ᵥ (gapsw80_t3_idealGram K I) *ᵥ zcastR v)) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left (hGram v) hc₀.le) Real.pi_nonneg
            _ ≤ π * (zcastR v ⬝ᵥ (gapsw80_t4_scaledGram K I _) *ᵥ zcastR v) :=
                mul_le_mul_of_nonneg_left
                  (scaledGram_lower_bound K I (hy_lb t ht u hu) v) Real.pi_nonneg))
      · exact hMsum.of_nonneg_of_le (fun v => norm_nonneg _) (fun v => by
          rw [Complex.norm_exp, Complex.ofReal_re]
          exact Real.exp_le_exp.mpr (neg_le_neg (by
            calc π * (c₀ * lam) * ∑ i, (v i:ℝ)^2
                = π * (c₀ * (lam * ∑ i, (v i:ℝ)^2)) := by ring
              _ ≤ π * (c₀ * (zcastR v ⬝ᵥ (gapsw80_t3_idealGram K I) *ᵥ zcastR v)) :=
                  mul_le_mul_of_nonneg_left
                    (mul_le_mul_of_nonneg_left (hGram v) hc₀.le) Real.pi_nonneg
              _ ≤ π * (zcastR v ⬝ᵥ (gapsw80_t4_scaledGram K I _) *ᵥ zcastR v) :=
                  mul_le_mul_of_nonneg_left
                    (scaledGram_lower_bound K I (hy_lb t ht u hu) v) Real.pi_nonneg)))

  have hcontOn_s : ContinuousOn
      (fun t => ∫ u in gapsw80_t7_unitBox K,
        gapsw80_t4_multiIdealTheta K I
          (scale * gapsw80_t5_yParam K (gapsw80_t5_mkParam K (Real.log t / 2) u)) ∂volume) s := by
    refine continuousOn_of_dominated (bound := fun _ => M)
      (μ := volume.restrict (gapsw80_t7_unitBox K)) ?_ ?_ ?_ ?_
    · intro t _
      exact (continuous_genericKernel_integrand K I _ scale hscale').aestronglyMeasurable.restrict
    · intro t ht
      exact ae_restrict_of_forall_mem (MeasurableSet.univ_pi fun _ => measurableSet_Ico)
        (fun u hu => hTheta_bound t ht u hu)
    · exact integrable_const M
    · refine ae_of_all _ fun u => ?_

      have hmk : ContinuousOn (fun t : ℝ => gapsw80_t5_mkParam K (Real.log t / 2) u) s := by
        refine continuousOn_pi.mpr fun w' => ?_
        unfold gapsw80_t5_mkParam
        split_ifs
        · exact (Real.continuousOn_log.mono (hssub.trans fun x hx => ne_of_gt hx)).div_const 2
        · exact continuousOn_const
      have hyP : ContinuousOn
          (fun t : ℝ => scale * gapsw80_t5_yParam K (gapsw80_t5_mkParam K (Real.log t / 2) u)) s := by
        refine ContinuousOn.mul continuousOn_const ?_
        refine continuousOn_pi.mpr fun w => ?_
        unfold gapsw80_t5_yParam
        exact (((continuous_apply w).comp (continuous_expMapBasis K)).continuousOn.comp hmk
          (Set.mapsTo_univ _ _)).pow 2
      exact (gapsw80_t7_continuousOn_multiIdealTheta K I).comp hyP
        (fun t ht w => mul_pos (hscale' w) (yParam_pos K _ w))
  exact (hcontOn_s t₀ ⟨by linarith, by linarith⟩).mono_of_mem_nhdsWithin
    (mem_nhdsWithin_of_mem_nhds hsnhds)

theorem gapsw80_t7_continuousOn_heckeKernel (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ContinuousOn (gapsw80_t5_heckeKernel K I) (Set.Ioi 0) := by
  have h := gapsw80_t7_continuousOn_genericKernel K I 1 (fun _ => le_refl 1)
  simp only [one_mul] at h
  exact h

theorem gapsw80_t7_continuousOn_multHeckeKernel (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ContinuousOn (gapsw80_t7_multHeckeKernel K J) (Set.Ioi 0) := by
  have h := gapsw80_t7_continuousOn_genericKernel K J (gapsw80_t7_multSq K)
    (fun w => one_le_pow₀ (Nat.one_le_cast.mpr mult_pos))
  exact h

theorem gapsw80_t7_genericKernel_sub_one_isBigO_exp (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (scale : realSpace K) (hscale : ∀ w, 1 ≤ scale w) :
    ∃ p > 0, (fun t => (∫ u in gapsw80_t7_unitBox K,
        gapsw80_t4_multiIdealTheta K I
          (scale * gapsw80_t5_yParam K (gapsw80_t5_mkParam K (Real.log t / 2) u)) ∂volume) - 1)
      =O[atTop] fun t => Real.exp (-p * t) := by
  obtain ⟨cK, hcK, hLB⟩ := gapsw80_t7_unitPart_lower_bound K
  obtain ⟨C, p, hp, hbound⟩ := gapsw80_t7_theta_sub_one_exp_bound K I
  have hscale' : ∀ w, 0 < scale w := fun w => lt_of_lt_of_le one_pos (hscale w)
  refine ⟨p * cK, by positivity, IsBigO.of_bound (max C 0) ?_⟩
  filter_upwards [eventually_ge_atTop cK⁻¹] with t ht
  have ht0 : 0 < t := lt_of_lt_of_le (inv_pos.mpr hcK) ht
  have hcKt : 1 ≤ cK * t := by rw [mul_comm]; exact (inv_le_iff_one_le_mul₀ hcK).mp ht
  set G : logSpace K → ℂ := fun u => gapsw80_t4_multiIdealTheta K I
      (scale * gapsw80_t5_yParam K (gapsw80_t5_mkParam K (Real.log t / 2) u)) with hG_def

  have hptw : ∀ u ∈ gapsw80_t7_unitBox K, ‖G u - 1‖ ≤ C * Real.exp (-(p * (cK * t))) := by
    intro u hu
    refine hbound hcKt (fun w => ?_)
    rw [Pi.mul_apply, gapsw80_t7_yParam_mkParam_factor K ht0]
    have huIcc : u ∈ (Set.univ.pi fun _ : {w // w ≠ w₀} => Icc (0:ℝ) 1) :=
      fun i hi => Ico_subset_Icc_self (hu i hi)
    have huP : 0 < gapsw80_t7_unitPart K u w := unitPart_pos K u w
    calc cK * t ≤ gapsw80_t7_unitPart K u w * t :=
          mul_le_mul_of_nonneg_right (hLB u huIcc w) ht0.le
      _ = 1 * (t * gapsw80_t7_unitPart K u w) := by ring
      _ ≤ scale w * (t * gapsw80_t7_unitPart K u w) :=
          mul_le_mul_of_nonneg_right (hscale w) (by positivity)

  have hGcont : Continuous G := continuous_genericKernel_integrand K I _ scale hscale'
  haveI hfin : IsFiniteMeasure (volume.restrict (gapsw80_t7_unitBox K)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact volume_unitBox_lt_top K⟩
  have hintconst : IntegrableOn (fun _ : logSpace K => (1:ℂ)) (gapsw80_t7_unitBox K) volume := by
    simp only [IntegrableOn, integrable_const_iff]; exact Or.inr hfin
  have hint : IntegrableOn (fun u => G u - 1) (gapsw80_t7_unitBox K) volume := by
    refine ⟨(hGcont.sub continuous_const).aestronglyMeasurable.restrict, ?_⟩
    refine HasFiniteIntegral.mono' ?_
      (ae_restrict_of_forall_mem (MeasurableSet.univ_pi fun _ => measurableSet_Ico)
        (fun u hu => hptw u hu))
    exact (integrable_const (C * Real.exp (-(p * (cK * t))))).hasFiniteIntegral

  have heq : (∫ u in gapsw80_t7_unitBox K, G u ∂volume) - 1
      = ∫ u in gapsw80_t7_unitBox K, (G u - 1) ∂volume := by
    have hintG : IntegrableOn G (gapsw80_t7_unitBox K) volume :=
      (hint.add hintconst).congr_fun
        (fun u _ => by simp only [Pi.add_apply]; ring)
        (MeasurableSet.univ_pi fun _ => measurableSet_Ico)
    rw [integral_sub hintG hintconst, setIntegral_const]
    simp [measureReal_def, volume_unitBox_eq_one]

  rw [Real.norm_of_nonneg (Real.exp_pos _).le,
    show -(p * cK) * t = -(p * (cK * t)) from by ring]
  calc ‖(∫ u in gapsw80_t7_unitBox K, G u ∂volume) - 1‖
      = ‖∫ u in gapsw80_t7_unitBox K, (G u - 1) ∂volume‖ := by rw [heq]
    _ ≤ (C * Real.exp (-(p * (cK * t)))) * (volume (gapsw80_t7_unitBox K)).toReal :=
        norm_setIntegral_le_of_norm_le_const (volume_unitBox_lt_top K) hptw
    _ = C * Real.exp (-(p * (cK * t))) := by
        rw [volume_unitBox_eq_one, ENNReal.toReal_one, mul_one]
    _ ≤ max C 0 * Real.exp (-(p * (cK * t))) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le

theorem gapsw80_t7_heckeKernel_sub_one_isBigO_exp (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ p > 0, (fun t => gapsw80_t5_heckeKernel K I t - 1)
      =O[atTop] fun t => Real.exp (-p * t) := by
  obtain ⟨p, hp, hO⟩ := gapsw80_t7_genericKernel_sub_one_isBigO_exp K I 1 (fun _ => le_refl 1)
  refine ⟨p, hp, hO.congr' (Eventually.of_forall fun t => ?_) EventuallyEq.rfl⟩
  simp only [one_mul, gapsw80_t5_heckeKernel]

theorem gapsw80_t7_hf_top (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (r : ℝ) :
    (fun t => gapsw80_t5_heckeKernel K I t - 1) =O[atTop] fun t => t ^ r := by
  obtain ⟨p, hp, hO⟩ := gapsw80_t7_heckeKernel_sub_one_isBigO_exp K I
  exact hO.trans (isLittleO_exp_neg_mul_rpow_atTop hp r).isBigO

theorem gapsw80_t7_multHeckeKernel_sub_one_isBigO_exp (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ p > 0, (fun t => gapsw80_t7_multHeckeKernel K J t - 1)
      =O[atTop] fun t => Real.exp (-p * t) :=
  gapsw80_t7_genericKernel_sub_one_isBigO_exp K J (gapsw80_t7_multSq K)
    (fun w => one_le_pow₀ (Nat.one_le_cast.mpr mult_pos))

theorem gapsw80_t7_hg_top (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (r : ℝ) :
    (fun t => gapsw80_t7_multHeckeKernel K J t - 1) =O[atTop] fun t => t ^ r := by
  obtain ⟨p, hp, hO⟩ := gapsw80_t7_multHeckeKernel_sub_one_isBigO_exp K J
  exact hO.trans (isLittleO_exp_neg_mul_rpow_atTop hp r).isBigO

end Gapsw80T7ClosedFEWeakPair
end FLT
end
end
end
end
end
end
end P2MW.S_NumberField_exists_completedDedekindZeta_package
