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
import Instance.NumberTheory.NumberField.CompletedDedekindZeta.Package.Part3


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

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge"

section

set_option maxHeartbeats 999999

namespace FLT

namespace Gapsw80T8MellinGammaPartialZeta

p2m_open "NumberField P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField NumberField.InfinitePlace P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.InfinitePlace NumberField.mixedEmbedding P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.mixedEmbedding"

p2m_open "NumberField.mixedEmbedding.fundamentalCone P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.mixedEmbedding.fundamentalCone"

p2m_open "NumberField.Units P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.Units NumberField.Units.dirichletUnitTheorem P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.Units.dirichletUnitTheorem"

open FLT.Gapsw80T2RankNGaussianPoisson FLT.Gapsw80T3IdealLatticeThetaTransformation

open FLT.Gapsw80T4MultiVarIdealThetaTransformation FLT.Gapsw80T5HeckeThetaKernel

open FLT.Gapsw80T6TraceDualBridge FLT.Gapsw80T7ClosedFEWeakPair

p2m_open "Matrix P2MW.S_NumberField_exists_completedDedekindZeta_package.Matrix Complex P2MW.S_NumberField_exists_completedDedekindZeta_package.Complex Module P2MW.S_NumberField_exists_completedDedekindZeta_package.Module Matrix.Module Real P2MW.S_NumberField_exists_completedDedekindZeta_package.Real MeasureTheory P2MW.S_NumberField_exists_completedDedekindZeta_package.MeasureTheory Asymptotics P2MW.S_NumberField_exists_completedDedekindZeta_package.Asymptotics Filter P2MW.S_NumberField_exists_completedDedekindZeta_package.Filter Asymptotics.Filter Set P2MW.S_NumberField_exists_completedDedekindZeta_package.Set"

p2m_open_scoped "Classical P2MW.S_NumberField_exists_completedDedekindZeta_package.Classical InnerProductSpace P2MW.S_NumberField_exists_completedDedekindZeta_package.InnerProductSpace nonZeroDivisors Topology P2MW.S_NumberField_exists_completedDedekindZeta_package.Topology"

variable (K : Type) [Field K] [NumberField K]

theorem gapsw80_t8_continuous_cexpQ (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (a : gapsw80_t8_nonzeroIdeal K I) :
    Continuous fun p : ℝ × logSpace K =>
      cexp ((-(π * ∑ w, gapsw80_t8_placeParam K p w * (w (a : K)) ^ 2) : ℝ) : ℂ) := by
  refine Complex.continuous_exp.comp (Complex.continuous_ofReal.comp (continuous_neg.comp ?_))
  refine continuous_const.mul (continuous_finset_sum _ fun w _ => ?_)
  exact (continuous_fst.mul ((continuous_unitPart K w).comp continuous_snd)).mul continuous_const

theorem gapsw80_t8_lintegral_master_reindex (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (σre : ℝ) :
    ∑' a : gapsw80_t8_nonzeroIdeal K I,
        ∫⁻ p in (Set.Ioi (0:ℝ)) ×ˢ (gapsw80_t7_unitBox K),
          ENNReal.ofReal
            (Real.exp (-(π * ∑ w, gapsw80_t8_placeParam K p w * (w (a : K)) ^ 2)) * p.1 ^ (σre - 1))
      = (torsionOrder K : ENNReal) *
        ∑' ω : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (gapsw80_t8_nonzeroIdeal K I)),
          ∫⁻ p in (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
            ENNReal.ofReal (Real.exp
                (-(π * ∑ w, gapsw80_t8_placeParam K p w * (w (gapsw80_t8_orbitRepr K I ω)) ^ 2))
              * p.1 ^ (σre - 1)) := by
  set GE : gapsw80_t8_nonzeroIdeal K I → ℝ × logSpace K → ENNReal := fun a p =>
    ENNReal.ofReal (Real.exp (-(π * ∑ w, gapsw80_t8_placeParam K p w * (w (a : K)) ^ 2))
      * p.1 ^ (σre - 1)) with hGE_def
  have hGE_orbitSigma : ∀ ω η p, GE (gapsw80_t8_orbitSigmaEquiv K I ⟨ω, η⟩) p
      = GE (η • ω.out) p := fun ω η p => by unfold GE; congr 4

  rw [← (gapsw80_t8_orbitSigmaEquiv K I).tsum_eq fun a =>
      ∫⁻ p in (Set.Ioi (0:ℝ)) ×ˢ (gapsw80_t7_unitBox K), GE a p,
    ENNReal.tsum_sigma']
  refine (tsum_congr fun ω => ?_).trans ENNReal.tsum_mul_left

  have hstep6a : ∀ p' : torsion K × (Fin (rank K) → ℤ), ∀ p : ℝ × logSpace K,
      GE (gapsw80_t8_orbitSigmaEquiv K I ⟨ω, gapsw80_t8_dutEquiv K p'⟩) p
        = GE ((∏ j, fundSystem K j ^ p'.2 j) • ω.out) p := fun p' p => by
    rw [hGE_orbitSigma,
      show gapsw80_t8_dutEquiv K p' • ω.out
          = (p'.1 : (𝓞 K)ˣ) • ((∏ j, fundSystem K j ^ p'.2 j) • ω.out) from by
        rw [← mul_smul]; rfl]
    unfold GE; congr 5
    exact gapsw80_t8_quadForm_torsion_invariant K I p p'.1 _
  rw [← (gapsw80_t8_dutEquiv K).tsum_eq,
    tsum_congr fun p' => lintegral_congr fun p => hstep6a p' p]

  rw [ENNReal.tsum_prod']
  simp only [Prod.snd]
  rw [ENNReal.tsum_const,
    show (ENat.card (torsion K) : ENNReal) = (torsionOrder K : ENNReal) from by
      rw [ENat.card_eq_coe_natCard]; rfl]
  congr 1

  set efr : (Fin (rank K) → ℤ) ≃
      Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀})) :=
    (Equiv.arrowCongr
        (equivFinRank : Fin (rank K) ≃ {w : InfinitePlace K // w ≠ w₀}) (Equiv.refl ℤ)).trans
      (gapsw80_t8_spanEquiv K).symm with hefr_def
  have hefr_prod : ∀ g,
      (∏ j, fundSystem K j ^ efr.symm g j)
        = ∏ i, fundSystem K (equivFinRank.symm i) ^ gapsw80_t8_spanEquiv K g i := fun g => by
    have hefrs : ∀ j, efr.symm g j = gapsw80_t8_spanEquiv K g (equivFinRank j) := fun j => by
      simp only [hefr_def, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.arrowCongr_symm,
        Equiv.refl_symm, Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply,
        Equiv.symm_apply_apply, id_eq]
    exact Fintype.prod_equiv (equivFinRank : Fin (rank K) ≃ {w : InfinitePlace K // w ≠ w₀}) _ _
      fun j => by rw [hefrs j, Equiv.symm_apply_apply]
  rw [← efr.symm.tsum_eq,
    tsum_congr fun g => by rw [hefr_prod g]]

  have hrpow_meas : Measurable fun p : ℝ × logSpace K => p.1 ^ (σre - 1) :=
    (measurable_of_continuousOn_compl_singleton (0:ℝ)
      (fun x hx => (Real.continuousAt_rpow_const x (σre - 1) (Or.inl hx)).continuousWithinAt)).comp
    measurable_fst
  have hGE_meas : ∀ a, Measurable (GE a) := fun a =>
    ENNReal.measurable_ofReal.comp ((Real.measurable_exp.comp
      (measurable_const.mul (Finset.measurable_sum _ fun w _ =>
        (measurable_fst.mul ((continuous_unitPart K w).measurable.comp measurable_snd)).mul
          measurable_const)).neg).mul hrpow_meas)
  have hGE_slice_meas : ∀ a,
      Measurable fun t : ℝ => ∫⁻ u in gapsw80_t7_unitBox K, GE a (t, u) ∂volume := fun a =>
    (hGE_meas a).lintegral_prod_right' (ν := volume.restrict (gapsw80_t7_unitBox K))
  have hGE_repr : (fun p => ENNReal.ofReal (Real.exp
          (-(π * ∑ w, gapsw80_t8_placeParam K p w * (w (gapsw80_t8_orbitRepr K I ω)) ^ 2))
        * p.1 ^ (σre - 1))) = GE ω.out := rfl
  simp_rw [hGE_repr, Measure.volume_eq_prod (ℝ) (logSpace K),
    ← Measure.prod_restrict, lintegral_prod _ (hGE_meas _).aemeasurable, setLIntegral_univ]
  rw [← lintegral_tsum fun g => (hGE_slice_meas _).aemeasurable.restrict]

  refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [(gapsw80_t7_unitBox_isAddFundamentalDomain K).lintegral_eq_tsum''
    (fun u => GE ω.out (t, u))]
  exact tsum_congr fun g => setLIntegral_congr_fun
    (MeasurableSet.univ_pi fun _ => measurableSet_Ico) fun u _ => by
      unfold GE; congr 5
      rw [show (g +ᵥ u : logSpace K) = u + (g : logSpace K) from by
            rw [AddSubmonoid.vadd_def]; exact add_comm _ _]
      exact (gapsw80_t8_quadForm_shift_span K I ht u g ω.out).symm

theorem gapsw80_t8_enorm_integrand_eq (σ : ℂ) (x : K) {p : ℝ × logSpace K} (hp : 0 < p.1) :
    ‖cexp ((-(π * ∑ w, gapsw80_t8_placeParam K p w * (w x) ^ 2) : ℝ) : ℂ)
        * ((p.1 : ℝ) : ℂ) ^ (σ - 1)‖ₑ
      = ENNReal.ofReal
          (Real.exp (-(π * ∑ w, gapsw80_t8_placeParam K p w * (w x) ^ 2))
            * p.1 ^ (σ.re - 1)) := by
  have hn : ‖cexp ((-(π * ∑ w, gapsw80_t8_placeParam K p w * (w x) ^ 2) : ℝ) : ℂ)
        * ((p.1 : ℝ) : ℂ) ^ (σ - 1)‖
      = Real.exp (-(π * ∑ w, gapsw80_t8_placeParam K p w * (w x) ^ 2))
        * p.1 ^ (σ.re - 1) := by
    rw [norm_mul, Complex.norm_exp, Complex.ofReal_re,
      Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hp),
      Complex.sub_re, Complex.one_re]
  rw [← hn, ← ofReal_norm_eq_enorm]

theorem gapsw80_t8_master_finite (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {σ : ℂ} (hσ : ((gapsw80_t7_heckeWeakFEPair K I).k : ℝ) < σ.re) :
    (∑' a : gapsw80_t8_nonzeroIdeal K I,
        ∫⁻ p in (Set.Ioi (0:ℝ)) ×ˢ (gapsw80_t7_unitBox K),
          ENNReal.ofReal
            (Real.exp (-(π * ∑ w, gapsw80_t8_placeParam K p w * (w (a : K)) ^ 2))
              * p.1 ^ (σ.re - 1))) ≠ ⊤ := by

  have hMC : IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (σ - 1) • ((gapsw80_t7_heckeWeakFEPair K I).f t
        - (gapsw80_t7_heckeWeakFEPair K I).f₀)) (Set.Ioi 0) volume :=
    ((gapsw80_t7_heckeWeakFEPair K I).hasMellin hσ).1
  suffices heq : (∑' a : gapsw80_t8_nonzeroIdeal K I,
        ∫⁻ p in (Set.Ioi (0:ℝ)) ×ˢ (gapsw80_t7_unitBox K),
          ENNReal.ofReal
            (Real.exp (-(π * ∑ w, gapsw80_t8_placeParam K p w * (w (a : K)) ^ 2))
              * p.1 ^ (σ.re - 1)))
      = ∫⁻ t in Set.Ioi (0:ℝ),
          ‖(t : ℂ) ^ (σ - 1) • ((gapsw80_t7_heckeWeakFEPair K I).f t
            - (gapsw80_t7_heckeWeakFEPair K I).f₀)‖ₑ by
    rw [heq]; exact hMC.2.ne

  have hrpow_meas : Measurable fun p : ℝ × logSpace K => p.1 ^ (σ.re - 1) :=
    (measurable_of_continuousOn_compl_singleton (0:ℝ)
      (fun x hx => (Real.continuousAt_rpow_const x (σ.re - 1) (Or.inl hx)).continuousWithinAt)).comp
    measurable_fst
  have hGE_meas : ∀ a : gapsw80_t8_nonzeroIdeal K I,
      Measurable fun p : ℝ × logSpace K =>
        ENNReal.ofReal (Real.exp (-(π * ∑ w, gapsw80_t8_placeParam K p w * (w (a : K)) ^ 2))
          * p.1 ^ (σ.re - 1)) := fun a =>
    ENNReal.measurable_ofReal.comp ((Real.measurable_exp.comp
      (measurable_const.mul (Finset.measurable_sum _ fun w _ =>
        (measurable_fst.mul ((continuous_unitPart K w).measurable.comp measurable_snd)).mul
          measurable_const)).neg).mul hrpow_meas)

  rw [← lintegral_tsum fun a => (hGE_meas a).aemeasurable.restrict,
    Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod _ (Measurable.ennreal_tsum hGE_meas).aemeasurable]

  refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht' : (0:ℝ) < t := ht
  have hrpow_nn : (0:ℝ) ≤ t ^ (σ.re - 1) := Real.rpow_nonneg ht'.le _
  have hy : ∀ u : logSpace K, ∀ w, 0 < gapsw80_t8_placeParam K (t, u) w :=
    fun u w => gapsw80_t8_placeParam_pos K ht' (p := (t, u)) w

  have hΘ_real : ∀ u : logSpace K,
      gapsw80_t4_multiIdealTheta K I (gapsw80_t8_placeParam K (t, u)) - 1
        = ((∑' a : gapsw80_t8_nonzeroIdeal K I,
            Real.exp (-(π * ∑ w, gapsw80_t8_placeParam K (t, u) w * (w (a : K)) ^ 2)) : ℝ)
          : ℂ) := fun u => by
    rw [gapsw80_t8_multiIdealTheta_sub_one K I (hy u), Complex.ofReal_tsum]
    exact tsum_congr fun a => (Complex.ofReal_exp _).symm
  have hΘ_norm : ∀ u : logSpace K,
      ‖gapsw80_t4_multiIdealTheta K I (gapsw80_t8_placeParam K (t, u)) - 1‖
        = ∑' a : gapsw80_t8_nonzeroIdeal K I,
            Real.exp (-(π * ∑ w, gapsw80_t8_placeParam K (t, u) w * (w (a : K)) ^ 2)) := fun u => by
    rw [hΘ_real u, Complex.norm_real,
      Real.norm_of_nonneg (tsum_nonneg fun _ => (Real.exp_pos _).le)]
  have hintΘ := gapsw80_t8_integrableOn_theta_sub_one K I ht'
  calc (∫⁻ u in gapsw80_t7_unitBox K,
          ∑' a : gapsw80_t8_nonzeroIdeal K I,
            ENNReal.ofReal (Real.exp (-(π * ∑ w, gapsw80_t8_placeParam K (t, u) w
                * (w (a : K)) ^ 2)) * t ^ (σ.re - 1)) ∂volume)

      = ENNReal.ofReal (t ^ (σ.re - 1)) * ∫⁻ u in gapsw80_t7_unitBox K,
            ‖gapsw80_t4_multiIdealTheta K I (gapsw80_t8_placeParam K (t, u)) - 1‖ₑ ∂volume := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine setLIntegral_congr_fun
          (MeasurableSet.univ_pi fun _ => measurableSet_Ico) fun u _ => ?_
        rw [tsum_congr fun a => by rw [mul_comm, ENNReal.ofReal_mul hrpow_nn],
          ENNReal.tsum_mul_left,
          ← ENNReal.ofReal_tsum_of_nonneg (fun _ => (Real.exp_pos _).le)
            (gapsw80_t8_summable_rexpQ K I (hy u)),
          ← ofReal_norm_eq_enorm, hΘ_norm u]

    _ = ENNReal.ofReal (t ^ (σ.re - 1) * ∫ u in gapsw80_t7_unitBox K,
            ‖gapsw80_t4_multiIdealTheta K I (gapsw80_t8_placeParam K (t, u)) - 1‖ ∂volume) := by
        rw [setLIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ico)
            fun u _ => (ofReal_norm_eq_enorm _).symm,
          ← ofReal_integral_eq_lintegral_ofReal hintΘ.norm (ae_of_all _ fun u => norm_nonneg _),
          ENNReal.ofReal_mul hrpow_nn]

    _ = _ := by
        rw [← ofReal_norm_eq_enorm, smul_eq_mul, norm_mul,
          Complex.norm_cpow_eq_rpow_re_of_pos ht', Complex.sub_re, Complex.one_re,
          show (gapsw80_t7_heckeWeakFEPair K I).f = gapsw80_t5_heckeKernel K I from rfl,
          show ((gapsw80_t7_heckeWeakFEPair K I).f₀ : ℂ) = 1 from rfl,
          gapsw80_t8_heckeKernel_sub_one K I ht',
          setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ico)
            (fun u _ => hΘ_real u),
          integral_complex_ofReal, Complex.norm_real,
          Real.norm_of_nonneg (integral_nonneg fun u => tsum_nonneg fun _ => (Real.exp_pos _).le),
          setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ico)
            (fun u _ => hΘ_norm u)]

theorem gapsw80_t8_integrableOn_orbitRepr (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {σ : ℂ} (hσ : ((gapsw80_t7_heckeWeakFEPair K I).k : ℝ) < σ.re)
    (ω : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (gapsw80_t8_nonzeroIdeal K I))) :
    IntegrableOn (fun p =>
        cexp ((-(π * ∑ w, gapsw80_t8_placeParam K p w
            * (w (gapsw80_t8_orbitRepr K I ω)) ^ 2) : ℝ) : ℂ)
          * ((p.1 : ℝ) : ℂ) ^ (σ - 1))
      ((Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K))) volume := by
  have hcont : ContinuousOn (fun p : ℝ × logSpace K =>
      cexp ((-(π * ∑ w, gapsw80_t8_placeParam K p w
          * (w (gapsw80_t8_orbitRepr K I ω)) ^ 2) : ℝ) : ℂ) * ((p.1 : ℝ) : ℂ) ^ (σ - 1))
      ((Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K))) :=
    (gapsw80_t8_continuous_cexpQ K I ω.out).continuousOn.mul fun p hp =>
      (((Complex.continuous_ofReal.comp continuous_fst).continuousAt (x := p)).cpow
          continuousAt_const (Or.inl (by
            simp only [Function.comp_apply, Complex.ofReal_re]; exact hp.1))
        ).continuousWithinAt
  refine ⟨hcont.aestronglyMeasurable (measurableSet_Ioi.prod MeasurableSet.univ), ?_⟩
  rw [hasFiniteIntegral_iff_enorm,
    setLIntegral_congr_fun (measurableSet_Ioi.prod MeasurableSet.univ)
      fun p hp => gapsw80_t8_enorm_integrand_eq K σ (gapsw80_t8_orbitRepr K I ω) (p := p) hp.1]
  refine lt_of_le_of_lt ?_ (lt_top_iff_ne_top.mpr (gapsw80_t8_master_finite K I hσ))
  rw [gapsw80_t8_lintegral_master_reindex K I σ.re]
  exact le_trans
    (ENNReal.le_tsum
      (f := fun ω' : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (gapsw80_t8_nonzeroIdeal K I)) =>
        ∫⁻ p in (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
          ENNReal.ofReal (Real.exp
              (-(π * ∑ w, gapsw80_t8_placeParam K p w *
                (w (gapsw80_t8_orbitRepr K I ω')) ^ 2))
            * p.1 ^ (σ.re - 1))) ω)
    (le_mul_of_one_le_left' (by exact_mod_cast torsionOrder_pos K))

theorem gapsw80_t8_quadForm_unit_smul_c (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (c : realSpace K) (p : ℝ × logSpace K) (η : (𝓞 K)ˣ) (a : gapsw80_t8_nonzeroIdeal K I) :
    ∑ w : InfinitePlace K,
        c w * gapsw80_t8_placeParam K p w * (w ((η • a : gapsw80_t8_nonzeroIdeal K I) : K)) ^ 2
      = ∑ w : InfinitePlace K,
          c w * gapsw80_t8_placeParam K p w * gapsw80_t5_unitSqScale K η w * (w (a : K)) ^ 2 := by
  refine Finset.sum_congr rfl fun w _ => ?_
  have hcoe : ((η • a : gapsw80_t8_nonzeroIdeal K I) : K) = (η : 𝓞 K) • (a : K) := rfl
  rw [hcoe, Algebra.smul_def, map_mul, mul_pow, gapsw80_t5_unitSqScale,
    show ((algebraMap (𝓞 K) K) (η : 𝓞 K) : K) = ((η : 𝓞 K) : K) from rfl]
  ring

theorem gapsw80_t8_quadForm_torsion_invariant_c (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (c : realSpace K) (p : ℝ × logSpace K) (ζ : torsion K) (a : gapsw80_t8_nonzeroIdeal K I) :
    ∑ w : InfinitePlace K,
        c w * gapsw80_t8_placeParam K p w
          * (w (((ζ : (𝓞 K)ˣ) • a : gapsw80_t8_nonzeroIdeal K I) : K)) ^ 2
      = ∑ w : InfinitePlace K, c w * gapsw80_t8_placeParam K p w * (w (a : K)) ^ 2 := by
  rw [gapsw80_t8_quadForm_unit_smul_c]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [gapsw80_t5_unitSqScale, (mem_torsion K).mp ζ.2 w, one_pow, mul_one]

theorem gapsw80_t8_quadForm_shift_single_c (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (c : realSpace K) {t : ℝ} (ht : 0 < t) (u : logSpace K)
    (i : {w : InfinitePlace K // w ≠ w₀}) (a : gapsw80_t8_nonzeroIdeal K I) :
    ∑ w : InfinitePlace K,
        c w * gapsw80_t8_placeParam K (t, u + Pi.single i 1) w * (w (a : K)) ^ 2
      = ∑ w : InfinitePlace K,
          c w * gapsw80_t8_placeParam K (t, u) w
            * (w (((fundSystem K (equivFinRank.symm i)) • a : gapsw80_t8_nonzeroIdeal K I) : K)) ^ 2 := by
  rw [gapsw80_t8_quadForm_unit_smul_c]
  exact Finset.sum_congr rfl fun w _ => by rw [gapsw80_t8_placeParam_add_single K ht]; ring

theorem gapsw80_t8_quadForm_shift_span_c (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (c : realSpace K) {t : ℝ} (ht : 0 < t) (u : logSpace K)
    (g : Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀})))
    (a : gapsw80_t8_nonzeroIdeal K I) :
    ∑ w : InfinitePlace K,
        c w * gapsw80_t8_placeParam K (t, u + (g : logSpace K)) w * (w (a : K)) ^ 2
      = ∑ w : InfinitePlace K,
          c w * gapsw80_t8_placeParam K (t, u) w
            * (w (((∏ i, fundSystem K (equivFinRank.symm i) ^ (gapsw80_t8_spanEquiv K g i))
                • a : gapsw80_t8_nonzeroIdeal K I) : K)) ^ 2 := by
  set m := gapsw80_t8_spanEquiv K g with hm_def
  have hg : (g : logSpace K) = ∑ i, (m i : ℝ) • Pi.single i (1:ℝ) := by
    have : g = (gapsw80_t8_spanEquiv K).symm m := ((gapsw80_t8_spanEquiv K).symm_apply_apply g).symm
    rw [this]
    funext j
    simp only [gapsw80_t8_spanEquiv_symm_apply_coe, Finset.sum_apply, Pi.smul_apply,
      Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [hg]
  have hstep : ∀ (v : logSpace K) (i : {w : InfinitePlace K // w ≠ w₀}) (k : ℤ),
      ∀ (b : gapsw80_t8_nonzeroIdeal K I),
      ∑ w, c w * gapsw80_t8_placeParam K (t, v + (k : ℝ) • Pi.single i 1) w * (w (b : K)) ^ 2
        = ∑ w, c w * gapsw80_t8_placeParam K (t, v) w
            * (w (((fundSystem K (equivFinRank.symm i) ^ k) • b : gapsw80_t8_nonzeroIdeal K I)
                : K)) ^ 2 := by
    intro v i k
    induction k using Int.induction_on with
    | zero => intro b; simp
    | succ n ih =>
      intro b
      rw [show (((n:ℤ)+1:ℤ):ℝ) • Pi.single i (1:ℝ)
              = ((n:ℤ):ℝ) • Pi.single i 1 + Pi.single i 1 from by
            push_cast; rw [add_smul, one_smul],
        ← add_assoc, gapsw80_t8_quadForm_shift_single_c K I c ht,
        ih (fundSystem K (equivFinRank.symm i) • b), ← mul_smul, ← _root_.zpow_add_one,
        show ((n:ℤ)+1 : ℤ) = (((n:ℕ)+1:ℕ):ℤ) from by push_cast; ring]
    | pred n ih =>
      intro b
      have key := (gapsw80_t8_quadForm_shift_single_c K I c ht
        (v + ((-(n:ℤ)-1:ℤ):ℝ) • Pi.single i 1) i
        ((fundSystem K (equivFinRank.symm i))⁻¹ • b)).symm
      rw [← mul_smul, mul_inv_cancel, one_smul, add_assoc,
        show ((-(n:ℤ)-1:ℤ):ℝ) • Pi.single i (1:ℝ) + Pi.single i 1
            = ((-(n:ℤ):ℤ):ℝ) • Pi.single i 1 from by
          rw [Int.cast_sub, Int.cast_one, sub_smul, one_smul, sub_add_cancel]] at key
      rw [key, ih ((fundSystem K (equivFinRank.symm i))⁻¹ • b), ← mul_smul,
        show fundSystem K (equivFinRank.symm i) ^ (-(n:ℤ)) * (fundSystem K (equivFinRank.symm i))⁻¹
            = fundSystem K (equivFinRank.symm i) ^ (-(n:ℤ)-1) from by group]
  suffices ∀ (s : Finset {w : InfinitePlace K // w ≠ w₀}) (a' : gapsw80_t8_nonzeroIdeal K I),
      ∑ w, c w * gapsw80_t8_placeParam K (t, u + ∑ i ∈ s, (m i : ℝ) • Pi.single i 1) w
          * (w (a' : K)) ^ 2
        = ∑ w, c w * gapsw80_t8_placeParam K (t, u) w
            * (w (((∏ i ∈ s, fundSystem K (equivFinRank.symm i) ^ (m i)) • a'
                : gapsw80_t8_nonzeroIdeal K I) : K)) ^ 2 from this Finset.univ a
  intro s
  induction s using Finset.induction with
  | empty => intro a'; simp
  | insert j s hj ih =>
    intro a'
    rw [Finset.sum_insert hj, add_comm ((m j : ℝ) • Pi.single j 1), ← add_assoc,
      hstep (u + ∑ i ∈ s, (m i : ℝ) • Pi.single i 1) j (m j) a',
      ih ((fundSystem K (equivFinRank.symm j) ^ (m j)) • a'),
      Finset.prod_insert hj, mul_smul, smul_comm]

theorem gapsw80_t8_continuous_cexpQ_c (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (c : realSpace K) (a : gapsw80_t8_nonzeroIdeal K I) :
    Continuous fun p : ℝ × logSpace K =>
      cexp ((-(π * ∑ w, c w * gapsw80_t8_placeParam K p w * (w (a : K)) ^ 2) : ℝ) : ℂ) := by
  refine Complex.continuous_exp.comp (Complex.continuous_ofReal.comp (continuous_neg.comp ?_))
  refine continuous_const.mul (continuous_finset_sum _ fun w _ => ?_)
  exact (continuous_const.mul
    (continuous_fst.mul ((continuous_unitPart K w).comp continuous_snd))).mul continuous_const

theorem gapsw80_t8_enorm_integrand_eq_c (c : realSpace K) (σ : ℂ) (x : K)
    {p : ℝ × logSpace K} (hp : 0 < p.1) :
    ‖cexp ((-(π * ∑ w, c w * gapsw80_t8_placeParam K p w * (w x) ^ 2) : ℝ) : ℂ)
        * ((p.1 : ℝ) : ℂ) ^ (σ - 1)‖ₑ
      = ENNReal.ofReal
          (Real.exp (-(π * ∑ w, c w * gapsw80_t8_placeParam K p w * (w x) ^ 2))
            * p.1 ^ (σ.re - 1)) := by
  rw [← ofReal_norm_eq_enorm, norm_mul, Complex.norm_exp, Complex.ofReal_re,
    Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hp),
    Complex.sub_re, Complex.one_re]

theorem gapsw80_t8_rankinSelberg_unfold_c (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (c : realSpace K) (σ : ℂ)
    (hMaster : (∑' a : gapsw80_t8_nonzeroIdeal K I,
        ∫⁻ p in (Set.Ioi (0:ℝ)) ×ˢ (gapsw80_t7_unitBox K),
          ENNReal.ofReal
            (Real.exp (-(π * ∑ w, c w * gapsw80_t8_placeParam K p w * (w (a : K)) ^ 2))
              * p.1 ^ (σ.re - 1))) ≠ ⊤)
    (hIntω : ∀ ω : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (gapsw80_t8_nonzeroIdeal K I)),
      IntegrableOn (fun p =>
          cexp ((-(π * ∑ w, c w * gapsw80_t8_placeParam K p w
              * (w (gapsw80_t8_orbitRepr K I ω)) ^ 2) : ℝ) : ℂ)
            * ((p.1 : ℝ) : ℂ) ^ (σ - 1))
        ((Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K))) volume) :
    (∫ t in Set.Ioi (0:ℝ), (t : ℂ) ^ (σ - 1)
        * ∫ u in gapsw80_t7_unitBox K,
            (∑' a : gapsw80_t8_nonzeroIdeal K I,
              cexp ((-(π * ∑ w, c w * gapsw80_t8_placeParam K (t, u) w * (w (a : K)) ^ 2) : ℝ) : ℂ))
            ∂volume)
      = (torsionOrder K : ℂ) *
        ∑' ω : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (gapsw80_t8_nonzeroIdeal K I)),
          ∫ p in (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
            cexp ((-(π * ∑ w : InfinitePlace K, c w * gapsw80_t8_placeParam K p w
                * (w (gapsw80_t8_orbitRepr K I ω)) ^ 2) : ℝ) : ℂ)
              * ((p.1 : ℝ) : ℂ) ^ (σ - 1) := by

  set F : gapsw80_t8_nonzeroIdeal K I → ℝ × logSpace K → ℂ := fun a p =>
    cexp ((-(π * ∑ w, c w * gapsw80_t8_placeParam K p w * (w (a : K)) ^ 2) : ℝ) : ℂ)
      * ((p.1 : ℝ) : ℂ) ^ (σ - 1) with hF_def
  have hF_sm : ∀ a, AEStronglyMeasurable (F a)
      (volume.restrict ((Set.Ioi (0:ℝ)) ×ˢ (gapsw80_t7_unitBox K))) := fun a =>
    ((gapsw80_t8_continuous_cexpQ_c K I c a).continuousOn.mul fun p hp =>
      (((Complex.continuous_ofReal.comp continuous_fst).continuousAt (x := p)).cpow
          continuousAt_const (Or.inl (by
            simp only [Function.comp_apply, Complex.ofReal_re]; exact hp.1))
        ).continuousWithinAt).aestronglyMeasurable
      (measurableSet_Ioi.prod (MeasurableSet.univ_pi fun _ => measurableSet_Ico))
  have hF_enorm : ∀ a, ∀ p ∈ (Set.Ioi (0:ℝ)) ×ˢ (gapsw80_t7_unitBox K),
      ‖F a p‖ₑ = ENNReal.ofReal
        (Real.exp (-(π * ∑ w, c w * gapsw80_t8_placeParam K p w * (w (a : K)) ^ 2))
          * p.1 ^ (σ.re - 1)) := fun a p hp =>
    gapsw80_t8_enorm_integrand_eq_c K c σ (a : K) (p := p) hp.1
  have hMaster' : (∑' a, ∫⁻ p in (Set.Ioi (0:ℝ)) ×ˢ (gapsw80_t7_unitBox K), ‖F a p‖ₑ) ≠ ⊤ := by
    refine (tsum_congr fun a => setLIntegral_congr_fun
      (measurableSet_Ioi.prod (MeasurableSet.univ_pi fun _ => measurableSet_Ico))
      (hF_enorm a)).symm ▸ hMaster

  have hFsum_int : IntegrableOn (fun p => ∑' a, F a p)
      ((Set.Ioi (0:ℝ)) ×ˢ (gapsw80_t7_unitBox K)) volume := by
    refine ⟨AEStronglyMeasurable.tsum hF_sm, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    refine lt_of_le_of_lt ?_ (lt_top_iff_ne_top.mpr hMaster')
    rw [← lintegral_tsum fun a => (hF_sm a).enorm]
    exact lintegral_mono fun p => enorm_tsum_le_tsum_enorm
  rw [show (∫ t in Set.Ioi (0:ℝ), (t : ℂ) ^ (σ - 1)
          * ∫ u in gapsw80_t7_unitBox K,
              (∑' a : gapsw80_t8_nonzeroIdeal K I,
                cexp ((-(π * ∑ w, c w * gapsw80_t8_placeParam K (t, u) w * (w (a : K)) ^ 2) : ℝ) : ℂ))
              ∂volume)
      = ∫ p in (Set.Ioi (0:ℝ)) ×ˢ (gapsw80_t7_unitBox K), ∑' a, F a p from by
    rw [Measure.volume_eq_prod, setIntegral_prod _ hFsum_int]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [← integral_const_mul]
    exact setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Ico)
      fun u _ => by rw [tsum_mul_right, mul_comm]]

  rw [integral_tsum (fun a => hF_sm a) hMaster']

  have hSsum : Summable fun a => ∫ p in (Set.Ioi (0:ℝ)) ×ˢ (gapsw80_t7_unitBox K), F a p := by
    refine .of_norm (.of_nonneg_of_le (fun _ => norm_nonneg _) (fun a => ?_)
      (ENNReal.summable_toReal hMaster'))
    rw [← ENNReal.toReal_ofReal (norm_nonneg _), ofReal_norm_eq_enorm]
    exact ENNReal.toReal_mono
      (ne_top_of_le_ne_top hMaster'
        (ENNReal.le_tsum
          (f := fun a => ∫⁻ p in (Set.Ioi (0:ℝ)) ×ˢ (gapsw80_t7_unitBox K), ‖F a p‖ₑ) a))
      (enorm_integral_le_lintegral_enorm _)
  have hF_Q : ∀ (a b : gapsw80_t8_nonzeroIdeal K I) (p : ℝ × logSpace K),
      (∑ w, c w * gapsw80_t8_placeParam K p w * (w (a : K)) ^ 2)
        = ∑ w, c w * gapsw80_t8_placeParam K p w * (w (b : K)) ^ 2 →
      F a p = F b p := fun a b p hQ => by unfold F; rw [hQ]
  have hSsumSig : Summable fun p :
        Σ _ : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (gapsw80_t8_nonzeroIdeal K I)), (𝓞 K)ˣ =>
      ∫ q in (Set.Ioi (0:ℝ)) ×ˢ (gapsw80_t7_unitBox K), F (gapsw80_t8_orbitSigmaEquiv K I p) q :=
    (gapsw80_t8_orbitSigmaEquiv K I).summable_iff.mpr hSsum
  rw [((gapsw80_t8_orbitSigmaEquiv K I).tsum_eq _).symm.trans hSsumSig.tsum_sigma,
    ← tsum_mul_left]
  refine tsum_congr fun ω => ?_
  have hstep6a : ∀ (p' : torsion K × (Fin (rank K) → ℤ)) (p : ℝ × logSpace K),
      F (gapsw80_t8_orbitSigmaEquiv K I ⟨ω, gapsw80_t8_dutEquiv K p'⟩) p
        = F ((∏ j, fundSystem K j ^ p'.2 j) • ω.out) p := fun p' p =>
    hF_Q _ _ p (by
      rw [show ((gapsw80_t8_orbitSigmaEquiv K I ⟨ω, gapsw80_t8_dutEquiv K p'⟩ :
            gapsw80_t8_nonzeroIdeal K I) : K)
          = ((gapsw80_t8_dutEquiv K p' • ω.out : gapsw80_t8_nonzeroIdeal K I) : K) from
        gapsw80_t8_orbitSigmaEquiv_apply K I ω _,
        show gapsw80_t8_dutEquiv K p' • ω.out
            = (p'.1 : (𝓞 K)ˣ) • ((∏ j, fundSystem K j ^ p'.2 j) • ω.out) from by
          rw [← mul_smul]; rfl]
      exact gapsw80_t8_quadForm_torsion_invariant_c K I c p p'.1 _)
  rw [← (gapsw80_t8_dutEquiv K).tsum_eq,
    tsum_congr fun p' => setIntegral_congr_fun
      (measurableSet_Ioi.prod (MeasurableSet.univ_pi fun _ => measurableSet_Ico))
      fun p _ => hstep6a p' p]
  have hSsumPr : Summable fun p' : torsion K × (Fin (rank K) → ℤ) =>
      ∫ p in (Set.Ioi (0:ℝ)) ×ˢ (gapsw80_t7_unitBox K),
        F ((∏ j, fundSystem K j ^ p'.2 j) • ω.out) p :=
    ((hSsumSig.sigma_factor ω).comp_injective (i := gapsw80_t8_dutEquiv K)
      (gapsw80_t8_dutEquiv K).injective).congr
      fun p' => setIntegral_congr_fun
        (measurableSet_Ioi.prod (MeasurableSet.univ_pi fun _ => measurableSet_Ico))
        fun p _ => hstep6a p' p
  rw [hSsumPr.tsum_prod]
  simp only [Prod.snd]
  rw [tsum_const, nsmul_eq_mul,
    show ((torsionOrder K : ℕ) : ℂ) = (Nat.card (torsion K) : ℂ) from rfl]
  congr 1
  set efr : (Fin (rank K) → ℤ) ≃
      Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀})) :=
    (Equiv.arrowCongr
        (equivFinRank : Fin (rank K) ≃ {w : InfinitePlace K // w ≠ w₀}) (Equiv.refl ℤ)).trans
      (gapsw80_t8_spanEquiv K).symm with hefr_def
  rw [← efr.symm.tsum_eq,
    tsum_congr fun g => by rw [show (∏ j, fundSystem K j ^ efr.symm g j)
        = (∏ i, fundSystem K (equivFinRank.symm i) ^ gapsw80_t8_spanEquiv K g i) from
      Fintype.prod_equiv (equivFinRank : Fin (rank K) ≃ {w : InfinitePlace K // w ≠ w₀}) _ _
        fun j => by
          simp only [hefr_def, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.arrowCongr_symm,
            Equiv.refl_symm, Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply,
            Equiv.symm_apply_apply, id_eq]]]

  have hInt_ω : IntegrableOn (F ω.out)
      ((Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K))) volume := hIntω ω
  have hInt_box : ∀ b : gapsw80_t8_nonzeroIdeal K I,
      IntegrableOn (F b) ((Set.Ioi (0:ℝ)) ×ˢ (gapsw80_t7_unitBox K)) volume := fun b =>
    ⟨hF_sm b, hasFiniteIntegral_iff_enorm.mpr
      (lt_of_le_of_lt
        (ENNReal.le_tsum
          (f := fun a => ∫⁻ p in (Set.Ioi (0:ℝ)) ×ˢ (gapsw80_t7_unitBox K), ‖F a p‖ₑ) b)
        (lt_top_iff_ne_top.mpr hMaster'))⟩
  set ν : Measure (ℝ × logSpace K) :=
    ((volume : Measure ℝ).restrict (Set.Ioi 0)).prod volume with hν_def
  have hν_eq : (volume : Measure (ℝ × logSpace K)).restrict
      ((Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K))) = ν := by
    rw [hν_def, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  have hν_box : (volume : Measure (ℝ × logSpace K)).restrict
        ((Set.Ioi (0:ℝ)) ×ˢ (gapsw80_t7_unitBox K))
      = ν.restrict (Prod.snd ⁻¹' gapsw80_t7_unitBox K) := by
    rw [hν_def, show (Prod.snd ⁻¹' gapsw80_t7_unitBox K : Set (ℝ × logSpace K))
          = Set.univ ×ˢ gapsw80_t7_unitBox K from Set.univ_prod.symm,
      ← Measure.prod_restrict, Measure.restrict_univ, Measure.volume_eq_prod,
      ← Measure.prod_restrict]
  have hInt_ω' : Integrable (F ω.out) ν := by rw [← hν_eq]; exact hInt_ω
  have hFD_prod : IsAddFundamentalDomain
      (Submodule.span ℤ (Set.range (Pi.basisFun ℝ {w : InfinitePlace K // w ≠ w₀})))
      (Prod.snd ⁻¹' gapsw80_t7_unitBox K) ν :=
    (gapsw80_t7_unitBox_isAddFundamentalDomain K).preimage_of_equiv
      (f := Prod.snd) Measure.quasiMeasurePreserving_snd Function.bijective_id (fun _ _ => rfl)
  rw [show (fun p : ℝ × logSpace K =>
          cexp ((-(π * ∑ w, c w * gapsw80_t8_placeParam K p w
                * (w (gapsw80_t8_orbitRepr K I ω)) ^ 2) : ℝ) : ℂ)
            * ((p.1 : ℝ) : ℂ) ^ (σ - 1)) = F ω.out from rfl,
    show (∫ p in (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)), F ω.out p)
        = ∫ p, F ω.out p ∂ν from by rw [← hν_eq],
    hFD_prod.integral_eq_tsum'' (F ω.out) hInt_ω']
  refine tsum_congr fun g => ?_
  rw [show (∫ p in Prod.snd ⁻¹' gapsw80_t7_unitBox K, F ω.out (g +ᵥ p) ∂ν)
        = ∫ p in (Set.Ioi (0:ℝ)) ×ˢ (gapsw80_t7_unitBox K), F ω.out (g +ᵥ p) from by
    show (∫ p, _ ∂(ν.restrict _)) = ∫ p, _ ∂(volume.restrict _); rw [hν_box]]
  refine setIntegral_congr_fun
    (measurableSet_Ioi.prod (MeasurableSet.univ_pi fun _ => measurableSet_Ico))
    fun p hp => ?_
  show F _ p = F ω.out (p.1, g +ᵥ p.2)
  unfold F
  congr 5
  rw [show (g +ᵥ p.2 : logSpace K) = p.2 + (g : logSpace K) from by
        rw [AddSubmonoid.vadd_def]; exact add_comm _ _]
  exact (gapsw80_t8_quadForm_shift_span_c K I c hp.1 p.2 g ω.out).symm

theorem gapsw80_t8_heckeLambda_unfold_eq (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : 1 < s.re) :
    (gapsw80_t7_heckeWeakFEPair K I).Λ ((nK K : ℂ) * s / 2)
      = (torsionOrder K : ℂ) *
        ∑' x : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (gapsw80_t8_nonzeroIdeal K I)),
          ∫ p in (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
            cexp ((-(π * ∑ w : InfinitePlace K,
                gapsw80_t8_placeParam K p w *
                (w (gapsw80_t8_orbitRepr K I x)) ^ 2) : ℝ) : ℂ)
              * ((p.1 : ℝ) : ℂ) ^ ((nK K : ℂ) * s / 2 - 1) := by
  set σ : ℂ := (nK K : ℂ) * s / 2 with hσ_def

  have hnK : (0:ℝ) < (nK K : ℝ) := by exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
  have hσ_re' : σ.re = (nK K : ℝ) * s.re / 2 := by
    rw [hσ_def]
    simp only [Complex.div_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      zero_mul, sub_zero, Complex.mul_im, mul_zero, zero_add, Complex.re_ofNat,
      Complex.im_ofNat, mul_zero, add_zero, Complex.normSq_ofNat]
    ring
  have hσ_re : ((gapsw80_t7_heckeWeakFEPair K I).k : ℝ) < σ.re := by
    show (nK K : ℝ) / 2 < σ.re
    rw [hσ_re']; nlinarith
  have hMellin := ((gapsw80_t7_heckeWeakFEPair K I).hasMellin hσ_re).2
  rw [← hMellin]

  have hstep23 : ∀ t ∈ Set.Ioi (0:ℝ),
      (t : ℂ) ^ (σ - 1) • ((gapsw80_t7_heckeWeakFEPair K I).f t
          - (gapsw80_t7_heckeWeakFEPair K I).f₀)
        = (t : ℂ) ^ (σ - 1)
          * ∫ u in gapsw80_t7_unitBox K,
              (∑' a : gapsw80_t8_nonzeroIdeal K I,
                cexp ((-(π * ∑ w, gapsw80_t8_placeParam K (t, u) w * (w (a : K)) ^ 2) : ℝ) : ℂ))
              ∂volume := fun t ht => by
    have ht' : (0:ℝ) < t := ht
    rw [show (gapsw80_t7_heckeWeakFEPair K I).f = gapsw80_t5_heckeKernel K I from rfl,
      show ((gapsw80_t7_heckeWeakFEPair K I).f₀ : ℂ) = 1 from rfl, smul_eq_mul,
      gapsw80_t8_heckeKernel_sub_one K I ht']
    congr 1
    refine setIntegral_congr_fun
      (MeasurableSet.univ_pi fun _ => measurableSet_Ico) fun u _ => ?_
    exact gapsw80_t8_multiIdealTheta_sub_one K I (fun w => gapsw80_t8_placeParam_pos K ht' w)
  rw [show mellin (fun t => (gapsw80_t7_heckeWeakFEPair K I).f t
        - (gapsw80_t7_heckeWeakFEPair K I).f₀) σ
      = ∫ t in Set.Ioi (0:ℝ), (t : ℂ) ^ (σ - 1)
          * ∫ u in gapsw80_t7_unitBox K,
              (∑' a : gapsw80_t8_nonzeroIdeal K I,
                cexp ((-(π * ∑ w, gapsw80_t8_placeParam K (t, u) w * (w (a : K)) ^ 2) : ℝ) : ℂ))
              ∂volume from
    setIntegral_congr_fun measurableSet_Ioi hstep23]

  have hMaster1 : (∑' a : gapsw80_t8_nonzeroIdeal K I,
      ∫⁻ p in (Set.Ioi (0:ℝ)) ×ˢ (gapsw80_t7_unitBox K),
        ENNReal.ofReal
          (Real.exp (-(π * ∑ w, (1:realSpace K) w * gapsw80_t8_placeParam K p w * (w (a : K)) ^ 2))
            * p.1 ^ (σ.re - 1))) ≠ ⊤ := by
    simp only [Pi.one_apply, one_mul]; exact gapsw80_t8_master_finite K I hσ_re
  have hIntω1 : ∀ ω : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (gapsw80_t8_nonzeroIdeal K I)),
      IntegrableOn (fun p =>
          cexp ((-(π * ∑ w, (1:realSpace K) w * gapsw80_t8_placeParam K p w
              * (w (gapsw80_t8_orbitRepr K I ω)) ^ 2) : ℝ) : ℂ)
            * ((p.1 : ℝ) : ℂ) ^ (σ - 1))
        ((Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K))) volume := fun ω => by
    simp only [Pi.one_apply, one_mul]; exact gapsw80_t8_integrableOn_orbitRepr K I hσ_re ω
  have hRS := gapsw80_t8_rankinSelberg_unfold_c K I 1 σ hMaster1 hIntω1
  simp only [Pi.one_apply, one_mul] at hRS
  exact hRS

theorem gapsw80_t8_perOrbit_integral_eq (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : 1 < s.re)
    (ω : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (gapsw80_t8_nonzeroIdeal K I))) :
    ∫ p in (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
        cexp ((-(π * ∑ w : InfinitePlace K,
            gapsw80_t8_placeParam K p w * (w (gapsw80_t8_orbitRepr K I ω)) ^ 2) : ℝ) : ℂ)
          * ((p.1 : ℝ) : ℂ) ^ ((nK K : ℂ) * s / 2 - 1)
      = (((2:ℝ) ^ ((nrRealPlaces K : ℤ) - 1) * nK K * regulator K : ℝ)⁻¹ : ℂ)
        * (Gammaℝ s ^ nrRealPlaces K * (Gammaℂ s * (2:ℂ)^(s-1)) ^ nrComplexPlaces K
          * ((|(Algebra.norm ℚ (gapsw80_t8_orbitRepr K I ω) : ℚ)| : ℝ) : ℂ) ^ (-s)) := by
  set a : K := gapsw80_t8_orbitRepr K I ω with ha_def
  have ha_ne : a ≠ 0 := ω.out.2.2
  have ha_pos : ∀ w : InfinitePlace K, (0:ℝ) < w a := fun w => pos_iff.mpr ha_ne
  have hnK : 1 ≤ nK K := Module.finrank_pos
  have hBset : {τ : realSpace K | ∀ w, 0 < τ w} = Set.univ.pi fun _ => Set.Ioi (0:ℝ) :=
    Set.ext fun τ => by simp [Set.mem_univ_pi]
  have hBmeas : MeasurableSet {τ : realSpace K | ∀ w, 0 < τ w} :=
    hBset ▸ MeasurableSet.univ_pi fun _ => measurableSet_Ioi

  set G : realSpace K → ℂ := fun τ =>
    cexp ((-(π * ∑ w, τ w * (w a) ^ 2) : ℝ) : ℂ)
      * ((∏ w : InfinitePlace K, τ w ^ w.mult : ℝ) : ℂ) ^ ((s - 2) / 2) with hG_def

  have hfactor : ∀ p ∈ (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
      cexp ((-(π * ∑ w, gapsw80_t8_placeParam K p w * (w a) ^ 2) : ℝ) : ℂ)
        * ((p.1 : ℝ) : ℂ) ^ ((nK K : ℂ) * s / 2 - 1)
      = ((p.1 ^ (nK K - 1) : ℝ) : ℂ) * G (gapsw80_t8_placeParam K p) := fun p hp => by
    have ht : (0:ℝ) < p.1 := hp.1
    simp only [hG_def, gapsw80_t8_prod_placeParam_pow_mult K ht p.2, Complex.ofReal_pow]
    rw [gapsw80_t8_ofReal_pow_cpow ht.le (nK K) ((s-2)/2),
      ← Complex.cpow_natCast (p.1:ℂ) (nK K - 1), mul_comm ((↑p.1:ℂ)^((nK K - 1 : ℕ):ℂ)),
      mul_assoc, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ht.ne')]
    congr 2
    push_cast [Nat.cast_sub hnK]; ring

  have hG_sm : AEStronglyMeasurable G (volume.restrict {τ : realSpace K | ∀ w, 0 < τ w}) := by
    refine ContinuousOn.aestronglyMeasurable ?_ hBmeas
    refine (Complex.continuous_exp.comp (Complex.continuous_ofReal.comp
        (continuous_const.mul (continuous_finset_sum _ fun w _ =>
          (continuous_apply w).mul continuous_const)).neg)).continuousOn.mul ?_
    intro τ hτ
    exact (((Complex.continuous_ofReal.comp (continuous_finset_prod _ fun w _ =>
        (continuous_apply w).pow _)).continuousAt).cpow continuousAt_const
      (Or.inl (by
        simp only [Function.comp_apply, Complex.ofReal_re]
        exact Finset.prod_pos fun w _ => pow_pos (hτ w) _))).continuousWithinAt

  rw [setIntegral_congr_fun (measurableSet_Ioi.prod MeasurableSet.univ) hfactor,
    gapsw80_t8_setIntegral_placeParam K hG_sm]
  congr 1

  have hreorg : ∀ τ ∈ {τ : realSpace K | ∀ w, 0 < τ w},
      ((∏ w : {w : InfinitePlace K // IsComplex w}, τ w.1 : ℝ) : ℂ) * G τ
        = ∏ w : InfinitePlace K,
            (((τ w : ℝ) : ℂ) ^ ((w.mult : ℂ) * s / 2 - 1)
              * cexp ((-(π * (w a)^2 * τ w) : ℝ) : ℂ)) := fun τ hτ => by
    have hτpos : ∀ w, (0:ℝ) < τ w := hτ
    have hτne : ∀ w, ((τ w : ℝ) : ℂ) ≠ 0 := fun w => Complex.ofReal_ne_zero.mpr (hτpos w).ne'
    simp only [hG_def]

    rw [show cexp ((-(π * ∑ w, τ w * (w a)^2):ℝ):ℂ)
          = ∏ w : InfinitePlace K, cexp ((-(π * (w a)^2 * τ w) : ℝ):ℂ) from by
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Complex.ofReal_sum, Complex.exp_sum]
        exact Finset.prod_congr rfl fun w _ => by ring_nf,

      gapsw80_t8_prod_ofReal_cpow Finset.univ (fun w _ => pow_nonneg (hτpos w).le _) ((s-2)/2),
      show (∏ w : InfinitePlace K, ((τ w ^ w.mult : ℝ):ℂ) ^ ((s-2)/2))
          = ∏ w : InfinitePlace K, ((τ w:ℝ):ℂ) ^ ((w.mult:ℂ)*(s-2)/2) from
        Finset.prod_congr rfl fun w _ => by
          rw [Complex.ofReal_pow,
            gapsw80_t8_ofReal_pow_cpow (hτpos w).le w.mult ((s-2)/2)]; ring_nf]

    rw [Complex.ofReal_prod, ← Finset.prod_mul_distrib,
      prod_eq_prod_mul_prod (K := K)
        (f := fun w => cexp ((-(π*(w a)^2*τ w):ℝ):ℂ) * ((τ w:ℝ):ℂ)^((w.mult:ℂ)*(s-2)/2)),
      prod_eq_prod_mul_prod (K := K)
        (f := fun w => ((τ w:ℝ):ℂ)^((w.mult:ℂ)*s/2-1) * cexp ((-(π*(w a)^2*τ w):ℝ):ℂ)),

      mul_left_comm
        (∏ w : {w : InfinitePlace K // IsComplex w}, ((τ w.1:ℝ):ℂ)),
      ← Finset.prod_mul_distrib]
    refine congr_arg₂ (· * ·)
      (Finset.prod_congr rfl fun w _ => ?_) (Finset.prod_congr rfl fun w _ => ?_)
    ·
      rw [mult_isReal w, Nat.cast_one, one_mul, one_mul,
        show s/2-1 = (s-2)/2 from by ring, mul_comm]
    ·
      rw [mult_isComplex w, Nat.cast_ofNat, show (2:ℂ)*(s-2)/2 = s-2 from by ring,
        show (2:ℂ)*s/2-1 = s-1 from by ring, mul_comm ((τ w.1:ℝ):ℂ), mul_assoc,
        show ((τ w.1:ℝ):ℂ)^(s-2) * ((τ w.1:ℝ):ℂ) = ((τ w.1:ℝ):ℂ)^(s-1) from by
          rw [show (s-1:ℂ) = (s-2)+1 from by ring,
            Complex.cpow_add _ _ (hτne w.1), Complex.cpow_one],
        mul_comm]

  have hmeas_eq : (volume : Measure (realSpace K)).restrict {τ | ∀ w, 0 < τ w}
      = Measure.pi (fun _ : InfinitePlace K => (volume : Measure ℝ).restrict (Set.Ioi 0)) := by
    rw [hBset, volume_pi, Measure.restrict_pi_pi]
  set fw : InfinitePlace K → ℝ → ℂ := fun w r =>
    (r:ℂ)^((w.mult:ℂ)*s/2-1) * cexp ((-(π*(w a)^2*r):ℝ):ℂ) with hfw_def
  have hfub : (∫ τ, ∏ w : InfinitePlace K, fw w (τ w)
        ∂Measure.pi (fun _ : InfinitePlace K => (volume : Measure ℝ).restrict (Set.Ioi 0)))
      = ∏ w : InfinitePlace K, ∫ r in Set.Ioi (0:ℝ), fw w r :=
    integral_fintype_prod_eq_prod fw
  rw [setIntegral_congr_fun hBmeas hreorg,
    show (∫ τ in {τ : realSpace K | ∀ w, 0 < τ w},
          ∏ w : InfinitePlace K, (((τ w:ℝ):ℂ)^((w.mult:ℂ)*s/2-1)
            * cexp ((-(π*(w a)^2*τ w):ℝ):ℂ)))
        = ∫ τ, ∏ w : InfinitePlace K, fw w (τ w)
          ∂Measure.pi (fun _ : InfinitePlace K => (volume : Measure ℝ).restrict (Set.Ioi 0))
      from by rw [← hmeas_eq],
    hfub]
  simp only [hfw_def]

  have hβre : ∀ w : InfinitePlace K, (0:ℝ) < ((w.mult:ℂ)*s/2).re := fun w => by
    have hre : ((w.mult:ℂ)*s/2).re = (w.mult : ℝ)*s.re/2 := by
      rw [Complex.div_ofNat_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
        zero_mul, sub_zero]
    rw [hre]
    exact div_pos (mul_pos (Nat.cast_pos.mpr w.mult_pos) (lt_trans one_pos hs)) two_pos
  rw [show (∏ w : InfinitePlace K, ∫ r in Set.Ioi (0:ℝ),
            ((r:ℝ):ℂ)^((w.mult:ℂ)*s/2-1) * cexp ((-(π*(w a)^2*r):ℝ):ℂ))
        = ∏ w : InfinitePlace K,
            (((π * (w a)^2:ℝ):ℂ)^(-((w.mult:ℂ)*s/2)) * Complex.Gamma ((w.mult:ℂ)*s/2)) from
      Finset.prod_congr rfl fun w _ => by
        simp only [Complex.ofReal_neg]
        exact gapsw80_t8_mellin_expNeg_eq_Gamma
          (mul_pos Real.pi_pos (pow_pos (ha_pos w) 2)) (hβre w)]

  have hx_nz : ∀ w, normAtPlace w (mixedEmbedding K a) ≠ 0 := fun w => by
    rw [normAtPlace_apply]; exact (ha_pos w).ne'
  rw [show (∏ w : InfinitePlace K,
            (((π * (w a)^2:ℝ):ℂ)^(-((w.mult:ℂ)*s/2)) * Complex.Gamma ((w.mult:ℂ)*s/2)))
        = ∏ w : InfinitePlace K,
            (((π * normAtPlace w (mixedEmbedding K a)^2:ℝ):ℂ)^(-((w.mult:ℂ)*s/2))
              * Complex.Gamma ((w.mult:ℂ)*s/2)) from
      Finset.prod_congr rfl fun w _ => by rw [normAtPlace_apply],
    gapsw80_t8_prod_gammaFactor_eq K hs hx_nz,
    gapsw80_t8_prod_normAtPlace_cpow K hx_nz s,
    mixedEmbedding.norm_eq_norm, Rat.cast_abs]

theorem gapsw80_t8_heckeLambda_eq_completedPartialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : 1 < s.re) :
    (gapsw80_t7_heckeWeakFEPair K I).Λ ((nK K : ℂ) * s / 2)
      = ((torsionOrder K : ℂ)
          / ((2:ℂ) ^ (nrRealPlaces K + nrComplexPlaces K - 1) * (nK K : ℂ) * (regulator K : ℂ)))
        * ((ZLattice.covolume (mixedEmbedding.idealLattice K I) : ℝ) : ℂ) ^ (-s)
        * ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2)
        * Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K
        * gapsw80_t8_partialDedekindZeta K (ClassGroup.mk K I)⁻¹ s := by

  rw [gapsw80_t8_heckeLambda_unfold_eq K I hs,
    tsum_congr (gapsw80_t8_perOrbit_integral_eq K I hs), tsum_mul_left, tsum_mul_left,
    gapsw80_t8_tsum_orbit_normInv_eq K I hs, mul_pow (Gammaℂ s), div_eq_mul_inv, mul_inv, mul_inv]

  set Ccov : ℂ := ((ZLattice.covolume (mixedEmbedding.idealLattice K I):ℝ):ℂ)^(-s) with hCcov
  set Cdisc : ℂ := ((|(discr K:ℝ)|:ℝ):ℂ)^(s/2) with hCdisc
  set CabsN : ℂ := ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K):ℝ):ℂ)^(-s) with hCabsN
  set C2rs : ℂ := ((2:ℝ):ℂ)^((nrComplexPlaces K:ℂ)*s) with hC2rs
  have hcd : Ccov * Cdisc = CabsN * C2rs := gapsw80_t8_covol_discr_cpow K I s

  have h2ne : (2:ℂ) ≠ 0 := two_ne_zero
  have hr₁ : 1 ≤ nrRealPlaces K + nrComplexPlaces K := by
    have h1 := card_add_two_mul_card_eq_rank K
    have h2 : 0 < Module.finrank ℚ K := Module.finrank_pos
    omega
  have hconst : (((2:ℝ)^((nrRealPlaces K:ℤ)-1) * (nK K:ℝ) * regulator K : ℝ)⁻¹ : ℂ)
        * ((2:ℂ)^(s-1))^nrComplexPlaces K
      = ((2:ℂ)^(nrRealPlaces K + nrComplexPlaces K - 1))⁻¹ * ((nK K:ℂ))⁻¹
        * ((regulator K:ℝ):ℂ)⁻¹ * C2rs := by
    have h2pow : ((2:ℂ)^((nrRealPlaces K:ℤ)-1 : ℤ))⁻¹ * ((2:ℂ)^(s-1))^nrComplexPlaces K
        = ((2:ℂ)^(nrRealPlaces K + nrComplexPlaces K - 1))⁻¹ * C2rs := by
      rw [hC2rs, Complex.ofReal_ofNat,
        ← Complex.cpow_intCast (2:ℂ) ((nrRealPlaces K:ℤ)-1),
        ← Complex.cpow_natCast (2:ℂ) (nrRealPlaces K + nrComplexPlaces K - 1),
        ← Complex.cpow_neg, ← Complex.cpow_neg,
        ← Complex.cpow_nat_mul (2:ℂ) (nrComplexPlaces K) (s-1),
        ← Complex.cpow_add _ _ h2ne, ← Complex.cpow_add _ _ h2ne]
      congr 1
      push_cast [Nat.cast_sub hr₁]; ring
    rw [← Complex.ofReal_inv, mul_inv, mul_inv, Complex.ofReal_mul, Complex.ofReal_mul,
      Complex.ofReal_inv, Complex.ofReal_inv, Complex.ofReal_inv, Complex.ofReal_natCast,
      Complex.ofReal_zpow, Complex.ofReal_ofNat]
    linear_combination ((nK K:ℂ))⁻¹ * ((regulator K:ℝ):ℂ)⁻¹ * h2pow
  linear_combination (Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K
        * gapsw80_t8_partialDedekindZeta K (ClassGroup.mk K I)⁻¹ s * CabsN
        * (torsionOrder K : ℂ)) * hconst
    - ((torsionOrder K : ℂ) * ((2:ℂ)^(nrRealPlaces K + nrComplexPlaces K - 1))⁻¹
        * ((nK K:ℂ))⁻¹ * ((regulator K:ℝ):ℂ)⁻¹
        * Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K
        * gapsw80_t8_partialDedekindZeta K (ClassGroup.mk K I)⁻¹ s) * hcd

theorem gapsw80_t8_one_le_multSq (w : InfinitePlace K) : (1:ℝ) ≤ gapsw80_t7_multSq K w :=
  one_le_pow₀ (Nat.one_le_cast.mpr mult_pos)

theorem gapsw80_t8_multHeckeKernel_sub_one (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {t : ℝ} (ht : 0 < t) :
    gapsw80_t7_multHeckeKernel K J t - 1
      = ∫ u in gapsw80_t7_unitBox K,
          (gapsw80_t4_multiIdealTheta K J
            (fun w => gapsw80_t7_multSq K w * gapsw80_t8_placeParam K (t, u) w) - 1) ∂volume := by
  have hvol : volume (gapsw80_t7_unitBox K) = 1 := volume_unitBox_eq_one K
  have hint2 : IntegrableOn (fun _ : logSpace K => (1:ℂ)) (gapsw80_t7_unitBox K) volume :=
    integrableOn_const (by rw [hvol]; exact ENNReal.one_ne_top)

  have hcont : Continuous
      (fun u => gapsw80_t4_multiIdealTheta K J
        (fun w => gapsw80_t7_multSq K w * gapsw80_t8_placeParam K (t, u) w)) := by
    have h := continuous_genericKernel_integrand K J (Real.log t / 2)
      (gapsw80_t7_multSq K) (fun w => multSq_pos K w)
    exact h.congr fun u => by
      congr 1; funext w
      rw [Pi.mul_apply, gapsw80_t7_yParam_mkParam_factor K ht]; rfl
  have hint1 : IntegrableOn
      (fun u => gapsw80_t4_multiIdealTheta K J
        (fun w => gapsw80_t7_multSq K w * gapsw80_t8_placeParam K (t, u) w))
      (gapsw80_t7_unitBox K) volume := by
    have hcompact : IsCompact
        (Set.univ.pi fun _ : {w : InfinitePlace K // w ≠ w₀} => Set.Icc (0:ℝ) 1) :=
      isCompact_univ_pi fun _ => isCompact_Icc
    exact (hcont.locallyIntegrable.integrableOn_isCompact hcompact).mono_set
      (Set.pi_mono fun _ _ => Set.Ico_subset_Icc_self)
  rw [integral_sub hint1 hint2, setIntegral_const]
  have hvol' : volume.real (gapsw80_t7_unitBox K) = 1 := by
    rw [measureReal_def, hvol, ENNReal.toReal_one]
  rw [hvol', one_smul]
  congr 1
  unfold gapsw80_t7_multHeckeKernel gapsw80_t7_integrand
  refine setIntegral_congr_fun
    (MeasurableSet.univ_pi fun _ => measurableSet_Ico) fun u _ => ?_
  congr 1; funext w
  rw [Pi.mul_apply, gapsw80_t7_yParam_mkParam_factor K ht]; rfl

theorem gapsw80_t8_rexpQ_c_le {c : realSpace K} (hc : ∀ w, 1 ≤ c w) (x : K)
    {p : ℝ × logSpace K} (hp : 0 < p.1) :
    Real.exp (-(π * ∑ w, c w * gapsw80_t8_placeParam K p w * (w x) ^ 2))
      ≤ Real.exp (-(π * ∑ w, gapsw80_t8_placeParam K p w * (w x) ^ 2)) := by
  refine Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left ?_ Real.pi_pos.le))
  refine Finset.sum_le_sum fun w _ => ?_
  have hpp := (gapsw80_t8_placeParam_pos K hp w).le
  have hwx := sq_nonneg (w x)
  nlinarith [hc w, mul_nonneg hpp hwx]

theorem gapsw80_t8_master_finite_mult (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {σ : ℂ} (hσ : ((gapsw80_t7_heckeWeakFEPair K J).k : ℝ) < σ.re) :
    (∑' a : gapsw80_t8_nonzeroIdeal K J,
        ∫⁻ p in (Set.Ioi (0:ℝ)) ×ˢ (gapsw80_t7_unitBox K),
          ENNReal.ofReal
            (Real.exp (-(π * ∑ w, gapsw80_t7_multSq K w * gapsw80_t8_placeParam K p w
                * (w (a : K)) ^ 2))
              * p.1 ^ (σ.re - 1))) ≠ ⊤ := by
  refine ne_top_of_le_ne_top (gapsw80_t8_master_finite K J hσ) ?_
  refine ENNReal.tsum_le_tsum fun a => ?_
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_mem
    (measurableSet_Ioi.prod (MeasurableSet.univ_pi fun _ => measurableSet_Ico))] with p hp
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
    (gapsw80_t8_rexpQ_c_le K (gapsw80_t8_one_le_multSq K) (a : K) hp.1)
    (Real.rpow_nonneg (le_of_lt hp.1) _))

theorem gapsw80_t8_integrableOn_orbitRepr_mult (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {σ : ℂ} (hσ : ((gapsw80_t7_heckeWeakFEPair K J).k : ℝ) < σ.re)
    (ω : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (gapsw80_t8_nonzeroIdeal K J))) :
    IntegrableOn (fun p =>
        cexp ((-(π * ∑ w, gapsw80_t7_multSq K w * gapsw80_t8_placeParam K p w
            * (w (gapsw80_t8_orbitRepr K J ω)) ^ 2) : ℝ) : ℂ)
          * ((p.1 : ℝ) : ℂ) ^ (σ - 1))
      ((Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K))) volume := by
  set a : K := gapsw80_t8_orbitRepr K J ω
  have hcont : ContinuousOn (fun p : ℝ × logSpace K =>
      cexp ((-(π * ∑ w, gapsw80_t7_multSq K w * gapsw80_t8_placeParam K p w
          * (w a) ^ 2) : ℝ) : ℂ) * ((p.1 : ℝ) : ℂ) ^ (σ - 1))
      ((Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K))) :=
    (gapsw80_t8_continuous_cexpQ_c K J (gapsw80_t7_multSq K) ω.out).continuousOn.mul fun p hp =>
      (((Complex.continuous_ofReal.comp continuous_fst).continuousAt (x := p)).cpow
          continuousAt_const (Or.inl (by
            simp only [Function.comp_apply, Complex.ofReal_re]; exact hp.1))
        ).continuousWithinAt
  refine ⟨hcont.aestronglyMeasurable (measurableSet_Ioi.prod MeasurableSet.univ), ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hbound := (gapsw80_t8_integrableOn_orbitRepr K J hσ ω).2
  rw [hasFiniteIntegral_iff_enorm] at hbound
  refine lt_of_le_of_lt ?_ hbound
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod MeasurableSet.univ)] with p hp
  rw [gapsw80_t8_enorm_integrand_eq_c K (gapsw80_t7_multSq K) σ a hp.1,
    gapsw80_t8_enorm_integrand_eq K σ a hp.1]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
    (gapsw80_t8_rexpQ_c_le K (gapsw80_t8_one_le_multSq K) a hp.1)
    (Real.rpow_nonneg (le_of_lt hp.1) _))

theorem gapsw80_t8_symmLambda_unfold_eq (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : 1 < s.re) :
    (gapsw80_t7_heckeWeakFEPair K I).symm.Λ ((nK K : ℂ) * s / 2)
      = (torsionOrder K : ℂ) *
        ∑' x : Quotient (MulAction.orbitRel ((𝓞 K)ˣ)
            (gapsw80_t8_nonzeroIdeal K (gapsw80_t6_traceDualIdeal K I))),
          ∫ p in (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
            cexp ((-(π * ∑ w : InfinitePlace K,
                gapsw80_t7_multSq K w * gapsw80_t8_placeParam K p w *
                (w (gapsw80_t8_orbitRepr K (gapsw80_t6_traceDualIdeal K I) x)) ^ 2) : ℝ) : ℂ)
              * ((p.1 : ℝ) : ℂ) ^ ((nK K : ℂ) * s / 2 - 1) := by
  set J : (FractionalIdeal (𝓞 K)⁰ K)ˣ := gapsw80_t6_traceDualIdeal K I with hJ_def
  set σ : ℂ := (nK K : ℂ) * s / 2 with hσ_def
  have hnK : (0:ℝ) < (nK K : ℝ) := by exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
  have hσ_re' : σ.re = (nK K : ℝ) * s.re / 2 := by
    rw [hσ_def]
    simp only [Complex.div_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      zero_mul, sub_zero, Complex.mul_im, mul_zero, zero_add, Complex.re_ofNat,
      Complex.im_ofNat, mul_zero, add_zero, Complex.normSq_ofNat]
    ring
  have hσ_re : ((gapsw80_t7_heckeWeakFEPair K I).symm.k : ℝ) < σ.re := by
    show (nK K : ℝ) / 2 < σ.re
    rw [hσ_re']; nlinarith
  have hσ_reJ : ((gapsw80_t7_heckeWeakFEPair K J).k : ℝ) < σ.re := hσ_re

  have hMellin := ((gapsw80_t7_heckeWeakFEPair K I).symm.hasMellin hσ_re).2
  rw [← hMellin]

  have hy : ∀ {t : ℝ} (_ : 0 < t) (u : logSpace K), ∀ w,
      0 < gapsw80_t7_multSq K w * gapsw80_t8_placeParam K (t, u) w := fun ht u w =>
    mul_pos (multSq_pos K w) (gapsw80_t8_placeParam_pos K ht w)
  have hstep23 : ∀ t ∈ Set.Ioi (0:ℝ),
      (t : ℂ) ^ (σ - 1) • ((gapsw80_t7_heckeWeakFEPair K I).symm.f t
          - (gapsw80_t7_heckeWeakFEPair K I).symm.f₀)
        = (t : ℂ) ^ (σ - 1)
          * ∫ u in gapsw80_t7_unitBox K,
              (∑' a : gapsw80_t8_nonzeroIdeal K J,
                cexp ((-(π * ∑ w, gapsw80_t7_multSq K w * gapsw80_t8_placeParam K (t, u) w
                    * (w (a : K)) ^ 2) : ℝ) : ℂ))
              ∂volume := fun t ht => by
    have ht' : (0:ℝ) < t := ht
    rw [show (gapsw80_t7_heckeWeakFEPair K I).symm.f
          = gapsw80_t7_multHeckeKernel K J from rfl,
      show ((gapsw80_t7_heckeWeakFEPair K I).symm.f₀ : ℂ) = 1 from rfl, smul_eq_mul,
      gapsw80_t8_multHeckeKernel_sub_one K J ht']
    congr 1
    refine setIntegral_congr_fun
      (MeasurableSet.univ_pi fun _ => measurableSet_Ico) fun u _ => ?_
    have := gapsw80_t8_multiIdealTheta_sub_one K J (y := fun w =>
        gapsw80_t7_multSq K w * gapsw80_t8_placeParam K (t, u) w) (hy ht' u)
    simpa only [mul_assoc] using this
  rw [show mellin (fun t => (gapsw80_t7_heckeWeakFEPair K I).symm.f t
        - (gapsw80_t7_heckeWeakFEPair K I).symm.f₀) σ
      = ∫ t in Set.Ioi (0:ℝ), (t : ℂ) ^ (σ - 1)
          * ∫ u in gapsw80_t7_unitBox K,
              (∑' a : gapsw80_t8_nonzeroIdeal K J,
                cexp ((-(π * ∑ w, gapsw80_t7_multSq K w * gapsw80_t8_placeParam K (t, u) w
                    * (w (a : K)) ^ 2) : ℝ) : ℂ))
              ∂volume from
    setIntegral_congr_fun measurableSet_Ioi hstep23]

  exact gapsw80_t8_rankinSelberg_unfold_c K J (gapsw80_t7_multSq K) σ
    (gapsw80_t8_master_finite_mult K J hσ_reJ)
    (gapsw80_t8_integrableOn_orbitRepr_mult K J hσ_reJ)

theorem gapsw80_t8_perOrbit_integral_eq_mult (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : 1 < s.re)
    (ω : Quotient (MulAction.orbitRel ((𝓞 K)ˣ) (gapsw80_t8_nonzeroIdeal K J))) :
    ∫ p in (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
        cexp ((-(π * ∑ w : InfinitePlace K,
            gapsw80_t7_multSq K w * gapsw80_t8_placeParam K p w
              * (w (gapsw80_t8_orbitRepr K J ω)) ^ 2) : ℝ) : ℂ)
          * ((p.1 : ℝ) : ℂ) ^ ((nK K : ℂ) * s / 2 - 1)
      = ((4:ℝ):ℂ) ^ (-(nrComplexPlaces K : ℂ) * s)
        * ((((2:ℝ) ^ ((nrRealPlaces K : ℤ) - 1) * nK K * regulator K : ℝ)⁻¹ : ℂ)
          * (Gammaℝ s ^ nrRealPlaces K * (Gammaℂ s * (2:ℂ)^(s-1)) ^ nrComplexPlaces K
            * ((|(Algebra.norm ℚ (gapsw80_t8_orbitRepr K J ω) : ℚ)| : ℝ) : ℂ) ^ (-s))) := by
  set a : K := gapsw80_t8_orbitRepr K J ω with ha_def
  have ha_ne : a ≠ 0 := ω.out.2.2
  have ha_pos : ∀ w : InfinitePlace K, (0:ℝ) < w a := fun w => pos_iff.mpr ha_ne
  have hnK : 1 ≤ nK K := Module.finrank_pos
  have hBset : {τ : realSpace K | ∀ w, 0 < τ w} = Set.univ.pi fun _ => Set.Ioi (0:ℝ) :=
    Set.ext fun τ => by simp [Set.mem_univ_pi]
  have hBmeas : MeasurableSet {τ : realSpace K | ∀ w, 0 < τ w} :=
    hBset ▸ MeasurableSet.univ_pi fun _ => measurableSet_Ioi

  set G : realSpace K → ℂ := fun τ =>
    cexp ((-(π * ∑ w, gapsw80_t7_multSq K w * τ w * (w a) ^ 2) : ℝ) : ℂ)
      * ((∏ w : InfinitePlace K, τ w ^ w.mult : ℝ) : ℂ) ^ ((s - 2) / 2) with hG_def

  have hfactor : ∀ p ∈ (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
      cexp ((-(π * ∑ w, gapsw80_t7_multSq K w * gapsw80_t8_placeParam K p w * (w a) ^ 2) : ℝ) : ℂ)
        * ((p.1 : ℝ) : ℂ) ^ ((nK K : ℂ) * s / 2 - 1)
      = ((p.1 ^ (nK K - 1) : ℝ) : ℂ) * G (gapsw80_t8_placeParam K p) := fun p hp => by
    have ht : (0:ℝ) < p.1 := hp.1
    simp only [hG_def, gapsw80_t8_prod_placeParam_pow_mult K ht p.2, Complex.ofReal_pow]
    rw [gapsw80_t8_ofReal_pow_cpow ht.le (nK K) ((s-2)/2),
      ← Complex.cpow_natCast (p.1:ℂ) (nK K - 1), mul_comm ((↑p.1:ℂ)^((nK K - 1 : ℕ):ℂ)),
      mul_assoc, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ht.ne')]
    congr 2
    push_cast [Nat.cast_sub hnK]; ring
  have hG_sm : AEStronglyMeasurable G (volume.restrict {τ : realSpace K | ∀ w, 0 < τ w}) := by
    refine ContinuousOn.aestronglyMeasurable ?_ hBmeas
    refine (Complex.continuous_exp.comp (Complex.continuous_ofReal.comp
        (continuous_const.mul (continuous_finset_sum _ fun w _ =>
          (continuous_const.mul (continuous_apply w)).mul continuous_const)).neg)).continuousOn.mul ?_
    intro τ hτ
    exact (((Complex.continuous_ofReal.comp (continuous_finset_prod _ fun w _ =>
        (continuous_apply w).pow _)).continuousAt).cpow continuousAt_const
      (Or.inl (by
        simp only [Function.comp_apply, Complex.ofReal_re]
        exact Finset.prod_pos fun w _ => pow_pos (hτ w) _))).continuousWithinAt

  rw [setIntegral_congr_fun (measurableSet_Ioi.prod MeasurableSet.univ) hfactor,
    gapsw80_t8_setIntegral_placeParam K hG_sm]
  rw [show ((4:ℝ):ℂ) ^ (-(nrComplexPlaces K:ℂ)*s)
        * ((((2:ℝ)^((nrRealPlaces K:ℤ)-1) * nK K * regulator K:ℝ)⁻¹:ℂ)
          * (Gammaℝ s ^ nrRealPlaces K * (Gammaℂ s * (2:ℂ)^(s-1))^nrComplexPlaces K
            * ((|(Algebra.norm ℚ a : ℚ)|:ℝ):ℂ)^(-s)))
      = (((2:ℝ)^((nrRealPlaces K:ℤ)-1) * nK K * regulator K:ℝ)⁻¹:ℂ)
        * (((4:ℝ):ℂ)^(-(nrComplexPlaces K:ℂ)*s)
          * (Gammaℝ s ^ nrRealPlaces K * (Gammaℂ s * (2:ℂ)^(s-1))^nrComplexPlaces K
            * ((|(Algebra.norm ℚ a : ℚ)|:ℝ):ℂ)^(-s))) from by ring]
  congr 1

  have hreorg : ∀ τ ∈ {τ : realSpace K | ∀ w, 0 < τ w},
      ((∏ w : {w : InfinitePlace K // IsComplex w}, τ w.1 : ℝ) : ℂ) * G τ
        = ∏ w : InfinitePlace K,
            (((τ w : ℝ) : ℂ) ^ ((w.mult : ℂ) * s / 2 - 1)
              * cexp ((-(π * gapsw80_t7_multSq K w * (w a)^2 * τ w) : ℝ) : ℂ)) := fun τ hτ => by
    have hτpos : ∀ w, (0:ℝ) < τ w := hτ
    have hτne : ∀ w, ((τ w : ℝ) : ℂ) ≠ 0 := fun w => Complex.ofReal_ne_zero.mpr (hτpos w).ne'
    simp only [hG_def]
    rw [show cexp ((-(π * ∑ w, gapsw80_t7_multSq K w * τ w * (w a)^2):ℝ):ℂ)
          = ∏ w : InfinitePlace K,
              cexp ((-(π * gapsw80_t7_multSq K w * (w a)^2 * τ w) : ℝ):ℂ) from by
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Complex.ofReal_sum, Complex.exp_sum]
        exact Finset.prod_congr rfl fun w _ => by ring_nf,
      gapsw80_t8_prod_ofReal_cpow Finset.univ (fun w _ => pow_nonneg (hτpos w).le _) ((s-2)/2),
      show (∏ w : InfinitePlace K, ((τ w ^ w.mult : ℝ):ℂ) ^ ((s-2)/2))
          = ∏ w : InfinitePlace K, ((τ w:ℝ):ℂ) ^ ((w.mult:ℂ)*(s-2)/2) from
        Finset.prod_congr rfl fun w _ => by
          rw [Complex.ofReal_pow,
            gapsw80_t8_ofReal_pow_cpow (hτpos w).le w.mult ((s-2)/2)]; ring_nf]
    rw [Complex.ofReal_prod, ← Finset.prod_mul_distrib,
      prod_eq_prod_mul_prod (K := K)
        (f := fun w => cexp ((-(π*gapsw80_t7_multSq K w*(w a)^2*τ w):ℝ):ℂ)
          * ((τ w:ℝ):ℂ)^((w.mult:ℂ)*(s-2)/2)),
      prod_eq_prod_mul_prod (K := K)
        (f := fun w => ((τ w:ℝ):ℂ)^((w.mult:ℂ)*s/2-1)
          * cexp ((-(π*gapsw80_t7_multSq K w*(w a)^2*τ w):ℝ):ℂ)),
      mul_left_comm
        (∏ w : {w : InfinitePlace K // IsComplex w}, ((τ w.1:ℝ):ℂ)),
      ← Finset.prod_mul_distrib]
    refine congr_arg₂ (· * ·)
      (Finset.prod_congr rfl fun w _ => ?_) (Finset.prod_congr rfl fun w _ => ?_)
    · rw [mult_isReal w, Nat.cast_one, one_mul, one_mul,
        show s/2-1 = (s-2)/2 from by ring, mul_comm]
    · rw [mult_isComplex w, Nat.cast_ofNat, show (2:ℂ)*(s-2)/2 = s-2 from by ring,
        show (2:ℂ)*s/2-1 = s-1 from by ring, mul_comm ((τ w.1:ℝ):ℂ), mul_assoc,
        show ((τ w.1:ℝ):ℂ)^(s-2) * ((τ w.1:ℝ):ℂ) = ((τ w.1:ℝ):ℂ)^(s-1) from by
          rw [show (s-1:ℂ) = (s-2)+1 from by ring,
            Complex.cpow_add _ _ (hτne w.1), Complex.cpow_one],
        mul_comm]

  have hmeas_eq : (volume : Measure (realSpace K)).restrict {τ | ∀ w, 0 < τ w}
      = Measure.pi (fun _ : InfinitePlace K => (volume : Measure ℝ).restrict (Set.Ioi 0)) := by
    rw [hBset, volume_pi, Measure.restrict_pi_pi]
  set fw : InfinitePlace K → ℝ → ℂ := fun w r =>
    (r:ℂ)^((w.mult:ℂ)*s/2-1) * cexp ((-(π*gapsw80_t7_multSq K w*(w a)^2*r):ℝ):ℂ) with hfw_def
  have hfub : (∫ τ, ∏ w : InfinitePlace K, fw w (τ w)
        ∂Measure.pi (fun _ : InfinitePlace K => (volume : Measure ℝ).restrict (Set.Ioi 0)))
      = ∏ w : InfinitePlace K, ∫ r in Set.Ioi (0:ℝ), fw w r :=
    integral_fintype_prod_eq_prod fw
  rw [setIntegral_congr_fun hBmeas hreorg,
    show (∫ τ in {τ : realSpace K | ∀ w, 0 < τ w},
          ∏ w : InfinitePlace K, (((τ w:ℝ):ℂ)^((w.mult:ℂ)*s/2-1)
            * cexp ((-(π*gapsw80_t7_multSq K w*(w a)^2*τ w):ℝ):ℂ)))
        = ∫ τ, ∏ w : InfinitePlace K, fw w (τ w)
          ∂Measure.pi (fun _ : InfinitePlace K => (volume : Measure ℝ).restrict (Set.Ioi 0))
      from by rw [← hmeas_eq],
    hfub]
  simp only [hfw_def]
  have hβre : ∀ w : InfinitePlace K, (0:ℝ) < ((w.mult:ℂ)*s/2).re := fun w => by
    have hre : ((w.mult:ℂ)*s/2).re = (w.mult : ℝ)*s.re/2 := by
      rw [Complex.div_ofNat_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
        zero_mul, sub_zero]
    rw [hre]
    exact div_pos (mul_pos (Nat.cast_pos.mpr w.mult_pos) (lt_trans one_pos hs)) two_pos
  rw [show (∏ w : InfinitePlace K, ∫ r in Set.Ioi (0:ℝ),
            ((r:ℝ):ℂ)^((w.mult:ℂ)*s/2-1)
              * cexp ((-(π*gapsw80_t7_multSq K w*(w a)^2*r):ℝ):ℂ))
        = ∏ w : InfinitePlace K,
            (((π * gapsw80_t7_multSq K w * (w a)^2:ℝ):ℂ)^(-((w.mult:ℂ)*s/2))
              * Complex.Gamma ((w.mult:ℂ)*s/2)) from
      Finset.prod_congr rfl fun w _ => by
        simp only [Complex.ofReal_neg]
        exact gapsw80_t8_mellin_expNeg_eq_Gamma
          (mul_pos (mul_pos Real.pi_pos (multSq_pos K w)) (pow_pos (ha_pos w) 2)) (hβre w)]

  have hx_nz : ∀ w, normAtPlace w (mixedEmbedding K a) ≠ 0 := fun w => by
    rw [normAtPlace_apply]; exact (ha_pos w).ne'
  have hsplit : ∀ w : InfinitePlace K,
      ((π * gapsw80_t7_multSq K w * (w a)^2:ℝ):ℂ)^(-((w.mult:ℂ)*s/2))
        = ((gapsw80_t7_multSq K w:ℝ):ℂ)^(-((w.mult:ℂ)*s/2))
          * ((π * (w a)^2:ℝ):ℂ)^(-((w.mult:ℂ)*s/2)) := fun w => by
    rw [show π * gapsw80_t7_multSq K w * (w a)^2
          = gapsw80_t7_multSq K w * (π * (w a)^2) from by ring,
      Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (multSq_pos K w).le
        (mul_nonneg Real.pi_pos.le (sq_nonneg _))]
  rw [show (∏ w : InfinitePlace K,
            (((π * gapsw80_t7_multSq K w * (w a)^2:ℝ):ℂ)^(-((w.mult:ℂ)*s/2))
              * Complex.Gamma ((w.mult:ℂ)*s/2)))
        = (∏ w : InfinitePlace K, ((gapsw80_t7_multSq K w:ℝ):ℂ)^(-((w.mult:ℂ)*s/2)))
          * ∏ w : InfinitePlace K,
              (((π * normAtPlace w (mixedEmbedding K a)^2:ℝ):ℂ)^(-((w.mult:ℂ)*s/2))
                * Complex.Gamma ((w.mult:ℂ)*s/2)) from by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun w _ => by rw [hsplit w, normAtPlace_apply]; ring,
    gapsw80_t8_prod_gammaFactor_eq K hs hx_nz,
    gapsw80_t8_prod_normAtPlace_cpow K hx_nz s,
    mixedEmbedding.norm_eq_norm, Rat.cast_abs]

  congr 1
  rw [prod_eq_prod_mul_prod (K := K)
      (f := fun w => ((gapsw80_t7_multSq K w:ℝ):ℂ)^(-((w.mult:ℂ)*s/2)))]
  have hreal : (∏ w : {w : InfinitePlace K // IsReal w},
      ((gapsw80_t7_multSq K w.1:ℝ):ℂ)^(-((w.1.mult:ℂ)*s/2))) = 1 :=
    Finset.prod_eq_one fun w _ => by
      rw [show gapsw80_t7_multSq K w.1 = 1 from by
        simp [gapsw80_t7_multSq, mult_isReal w], Complex.ofReal_one, Complex.one_cpow]
  have hcplx : (∏ w : {w : InfinitePlace K // IsComplex w},
        ((gapsw80_t7_multSq K w.1:ℝ):ℂ)^(-((w.1.mult:ℂ)*s/2)))
      = ((4:ℝ):ℂ)^(-(nrComplexPlaces K:ℂ)*s) := by
    rw [show (∏ w : {w : InfinitePlace K // IsComplex w},
            ((gapsw80_t7_multSq K w.1:ℝ):ℂ)^(-((w.1.mult:ℂ)*s/2)))
          = ∏ _w : {w : InfinitePlace K // IsComplex w}, ((4:ℝ):ℂ)^(-s) from
        Finset.prod_congr rfl fun w _ => by
          rw [show gapsw80_t7_multSq K w.1 = 4 from by
            simp [gapsw80_t7_multSq, mult_isComplex w]; norm_num,
            mult_isComplex w]
          congr 1; push_cast; ring,
      Finset.prod_const, ← Complex.cpow_nat_mul, Finset.card_univ,
      show Fintype.card {w : InfinitePlace K // IsComplex w} = nrComplexPlaces K from rfl]
    congr 1; push_cast; ring
  rw [hreal, one_mul, hcplx]

theorem gapsw80_t8_symmLambda_eq_completedPartialZeta (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    {s : ℂ} (hs : 1 < s.re) :
    (gapsw80_t7_heckeWeakFEPair K I).symm.Λ ((nK K : ℂ) * s / 2)
      = ((torsionOrder K : ℂ)
          / ((2:ℂ) ^ (nrRealPlaces K + nrComplexPlaces K - 1) * (nK K : ℂ) * (regulator K : ℂ)))
        * ((4:ℝ) : ℂ) ^ (-(nrComplexPlaces K : ℂ) * s)
        * ((ZLattice.covolume (mixedEmbedding.idealLattice K
            (gapsw80_t6_traceDualIdeal K I)) : ℝ) : ℂ) ^ (-s)
        * ((|(discr K : ℝ)| : ℝ) : ℂ) ^ (s / 2)
        * Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K
        * gapsw80_t8_partialDedekindZeta K (ClassGroup.mk K (gapsw80_t6_traceDualIdeal K I))⁻¹ s := by
  set J := gapsw80_t6_traceDualIdeal K I with hJ_def

  rw [gapsw80_t8_symmLambda_unfold_eq K I hs,
    tsum_congr (gapsw80_t8_perOrbit_integral_eq_mult K J hs), tsum_mul_left, tsum_mul_left,
    tsum_mul_left, gapsw80_t8_tsum_orbit_normInv_eq K J hs, mul_pow (Gammaℂ s),
    div_eq_mul_inv, mul_inv, mul_inv]

  set Ccov : ℂ := ((ZLattice.covolume (mixedEmbedding.idealLattice K J):ℝ):ℂ)^(-s) with hCcov
  set Cdisc : ℂ := ((|(discr K:ℝ)|:ℝ):ℂ)^(s/2) with hCdisc
  set CabsN : ℂ := ((FractionalIdeal.absNorm (J : FractionalIdeal (𝓞 K)⁰ K):ℝ):ℂ)^(-s) with hCabsN
  set C2rs : ℂ := ((2:ℝ):ℂ)^((nrComplexPlaces K:ℂ)*s) with hC2rs
  set C4rs : ℂ := ((4:ℝ):ℂ)^(-(nrComplexPlaces K:ℂ)*s) with hC4rs
  have hcd : Ccov * Cdisc = CabsN * C2rs := gapsw80_t8_covol_discr_cpow K J s
  have h2ne : (2:ℂ) ≠ 0 := two_ne_zero
  have hr₁ : 1 ≤ nrRealPlaces K + nrComplexPlaces K := by
    have h1 := card_add_two_mul_card_eq_rank K
    have h2 : 0 < Module.finrank ℚ K := Module.finrank_pos
    omega
  have hconst : (((2:ℝ)^((nrRealPlaces K:ℤ)-1) * (nK K:ℝ) * regulator K : ℝ)⁻¹ : ℂ)
        * ((2:ℂ)^(s-1))^nrComplexPlaces K
      = ((2:ℂ)^(nrRealPlaces K + nrComplexPlaces K - 1))⁻¹ * ((nK K:ℂ))⁻¹
        * ((regulator K:ℝ):ℂ)⁻¹ * C2rs := by
    have h2pow : ((2:ℂ)^((nrRealPlaces K:ℤ)-1 : ℤ))⁻¹ * ((2:ℂ)^(s-1))^nrComplexPlaces K
        = ((2:ℂ)^(nrRealPlaces K + nrComplexPlaces K - 1))⁻¹ * C2rs := by
      rw [hC2rs, Complex.ofReal_ofNat,
        ← Complex.cpow_intCast (2:ℂ) ((nrRealPlaces K:ℤ)-1),
        ← Complex.cpow_natCast (2:ℂ) (nrRealPlaces K + nrComplexPlaces K - 1),
        ← Complex.cpow_neg, ← Complex.cpow_neg,
        ← Complex.cpow_nat_mul (2:ℂ) (nrComplexPlaces K) (s-1),
        ← Complex.cpow_add _ _ h2ne, ← Complex.cpow_add _ _ h2ne]
      congr 1
      push_cast [Nat.cast_sub hr₁]; ring
    rw [← Complex.ofReal_inv, mul_inv, mul_inv, Complex.ofReal_mul, Complex.ofReal_mul,
      Complex.ofReal_inv, Complex.ofReal_inv, Complex.ofReal_inv, Complex.ofReal_natCast,
      Complex.ofReal_zpow, Complex.ofReal_ofNat]
    linear_combination ((nK K:ℂ))⁻¹ * ((regulator K:ℝ):ℂ)⁻¹ * h2pow
  linear_combination C4rs * (Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K
        * gapsw80_t8_partialDedekindZeta K (ClassGroup.mk K J)⁻¹ s * CabsN
        * (torsionOrder K : ℂ)) * hconst
    - C4rs * ((torsionOrder K : ℂ) * ((2:ℂ)^(nrRealPlaces K + nrComplexPlaces K - 1))⁻¹
        * ((nK K:ℂ))⁻¹ * ((regulator K:ℝ):ℂ)⁻¹
        * Gammaℝ s ^ nrRealPlaces K * Gammaℂ s ^ nrComplexPlaces K
        * gapsw80_t8_partialDedekindZeta K (ClassGroup.mk K J)⁻¹ s) * hcd

theorem gapsw80_t8_sat_covol_prod (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ZLattice.covolume (mixedEmbedding.idealLattice K I)
        * ZLattice.covolume (mixedEmbedding.idealLattice K (gapsw80_t6_traceDualIdeal K I))
      = (4 : ℝ)⁻¹ ^ nrComplexPlaces K := by
  have h4 : ((4:ℝ) ^ nrComplexPlaces K) ≠ 0 := (pow_pos (by norm_num) _).ne'
  have hdet : |(gapsw80_t6_bridgeMatrix K I).det|
      = ZLattice.covolume (mixedEmbedding.idealLattice K I)
          * (4 : ℝ) ^ nrComplexPlaces K
          * ZLattice.covolume (mixedEmbedding.idealLattice K (gapsw80_t6_traceDualIdeal K I)) := by
    rw [gapsw80_t6_bridgeMatrix, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
      abs_mul, abs_mul, abs_det_coordMatrix, abs_det_coordMatrix, gapsw80_t6_abs_det_Phi]
  have h1 : ZLattice.covolume (mixedEmbedding.idealLattice K I)
        * (4 : ℝ) ^ nrComplexPlaces K
        * ZLattice.covolume (mixedEmbedding.idealLattice K (gapsw80_t6_traceDualIdeal K I))
      = 1 := hdet ▸ gapsw80_t6_abs_det_bridgeMatrix K I
  rw [inv_pow]; field_simp
  linear_combination h1

end Gapsw80T8MellinGammaPartialZeta
end FLT
end
end
end
end
end
end
end P2MW.S_NumberField_exists_completedDedekindZeta_package
