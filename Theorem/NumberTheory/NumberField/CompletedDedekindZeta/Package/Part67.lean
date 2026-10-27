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
import Def.NumberTheory.NumberField.CompletedDedekindZeta.Package.Part61


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

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta"

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta"

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

section

set_option maxHeartbeats 999999

namespace FLT

namespace Gapsw80T43CompletedZetaRealSuperlinearProof

open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition

open FLT.Gapsw80T9ClassSumA1Closure

open FLT.Gapsw80T10DedekindZetaBridgeA1Discharge

open FLT.Gapsw80T11ExplicitFormulaA34Decomp

open FLT.Gapsw80T16XiRightHalfBoundProof

open FLT.Gapsw80T21D2SubDecompWire

open FLT.Gapsw80T25B4pppStripSinglePointAbsorption

open FLT.Gapsw80T30D2d0cLocalEulerFactorProof

open FLT.Gapsw80T41D1b0aHadamardFactorSubDecomp

open FLT.Gapsw80T42D1b0a0XiNonzeroInfZerosProof

p2m_open "NumberField P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField NumberField.InfinitePlace P2MW.S_NumberField_exists_completedDedekindZeta_package.NumberField.InfinitePlace Complex P2MW.S_NumberField_exists_completedDedekindZeta_package.Complex Filter P2MW.S_NumberField_exists_completedDedekindZeta_package.Filter Set P2MW.S_NumberField_exists_completedDedekindZeta_package.Set"

p2m_open_scoped "Topology P2MW.S_NumberField_exists_completedDedekindZeta_package.Topology Real P2MW.S_NumberField_exists_completedDedekindZeta_package.Real Nat P2MW.S_NumberField_exists_completedDedekindZeta_package.Nat Filter.Nat Set.Nat"

theorem gapsw80_t43_one_le_norm_discrPow (K : Type) [Field K] [NumberField K]
    {σ : ℝ} (hσ : 0 ≤ σ) :
    (1:ℝ) ≤ ‖(((|discr K| : ℤ) : ℂ)) ^ ((σ:ℂ) / 2)‖ := by
  rw [gapsw80_t10_discrCoercion,
    Complex.norm_cpow_eq_rpow_re_of_pos
      (lt_of_lt_of_le one_pos (gapsw80_t16_one_le_abs_discr K))]
  have hre : ((σ:ℂ) / 2).re = σ / 2 := by
    simp [Complex.ofReal_div, Complex.div_re, Complex.ofReal_re, Complex.ofReal_im]
  rw [hre]
  exact Real.one_le_rpow (gapsw80_t16_one_le_abs_discr K) (by linarith)

theorem gapsw80_t43_norm_Gamma_nat_succ (n : ℕ) :
    ‖Complex.Gamma ((n + 1 : ℕ) : ℂ)‖ = (n ! : ℝ) := by
  rw [show (((n + 1 : ℕ) : ℂ)) = (((n + 1 : ℕ) : ℝ) : ℂ) by push_cast; ring,
    Complex.Gamma_ofReal, Complex.norm_real, Real.norm_eq_abs,
    show (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 by push_cast; ring,
    Real.Gamma_nat_eq_factorial]
  exact abs_of_pos (by exact_mod_cast n.factorial_pos)

theorem gapsw80_t43_one_le_norm_dedekindZeta_ofReal (K : Type) [Field K]
    [NumberField K] {σ : ℝ} (hσ : 1 < σ) :
    (1:ℝ) ≤ ‖dedekindZeta K (σ:ℂ)‖ := by
  have hre : 1 < (σ:ℂ).re := by rwa [Complex.ofReal_re]
  have hsum : LSeriesSummable
      (fun n ↦ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ)) (σ:ℂ) :=
    gapsw80_t10_LSeriesSummable_dedekindZeta K hre

  have hterm_re_nonneg : ∀ n,
      0 ≤ (LSeries.term
        (fun k ↦ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℂ))
        (σ:ℂ) n).re := fun n => by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero hn]
      have hcpow : (n:ℂ)^(σ:ℂ) = (((n:ℝ)^σ : ℝ):ℂ) := by
        rw [show ((n:ℕ):ℂ) = (((n:ℕ):ℝ):ℂ) from (Complex.ofReal_natCast n).symm,
          ← Complex.ofReal_cpow (Nat.cast_nonneg n)]
      rw [hcpow, show ((Nat.card _ : ℕ):ℂ) = (((Nat.card _ : ℕ):ℝ):ℂ) from
          (Complex.ofReal_natCast _).symm, ← Complex.ofReal_div, Complex.ofReal_re]
      positivity

  have hterm1_re :
      (LSeries.term
        (fun k ↦ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℂ))
        (σ:ℂ) 1).re = 1 := by
    rw [LSeries.term_of_ne_zero one_ne_zero]
    simp only [Nat.cast_one, Complex.one_cpow, div_one]
    have : Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 1} = 1 := by
      simp [Ideal.absNorm_eq_one_iff]
    rw [this]; simp

  have hHS_re : HasSum
      (fun n => (LSeries.term
        (fun k ↦ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = k} : ℂ))
        (σ:ℂ) n).re)
      (dedekindZeta K (σ:ℂ)).re :=
    Complex.hasSum_re hsum.hasSum
  calc (1:ℝ)
      = (LSeries.term _ (σ:ℂ) 1).re := hterm1_re.symm
    _ ≤ (dedekindZeta K (σ:ℂ)).re :=
        le_hasSum hHS_re 1 (fun n _ => hterm_re_nonneg n)
    _ ≤ ‖dedekindZeta K (σ:ℂ)‖ := Complex.re_le_norm _

theorem gapsw80_t43_log_pi_le : Real.log Real.pi ≤ 2 * Real.log (2 * Real.pi) := by
  have h1 : Real.log Real.pi ≤ Real.log (2 * Real.pi) :=
    Real.log_le_log Real.pi_pos (by linarith [Real.pi_pos])
  have h2 : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by linarith [Real.pi_gt_three])
  linarith

theorem gapsw80_t43_stirling_core {m : ℕ} (hm : 1 ≤ m) :
    (m:ℝ) * Real.log m - m ≤ Real.log (m ! : ℝ) := by
  have hlog_m : 0 ≤ Real.log (m:ℝ) := Real.log_nonneg (by exact_mod_cast hm)
  have h2π : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by linarith [Real.pi_gt_three])
  have key := Stirling.le_log_factorial_stirling (Nat.one_le_iff_ne_zero.mp hm)
  push_cast at key ⊢
  linarith

theorem gapsw80_t43_log_norm_Gammaℝ_ge {m : ℕ} (hm : 1 ≤ m) :
    (m:ℝ) * Real.log m - gapsw80_t43_L₀ * ((m:ℝ) + 1)
      ≤ Real.log ‖Complex.Gammaℝ ((2 * ((m:ℝ) + 1) : ℝ):ℂ)‖ := by
  set σ : ℝ := 2 * ((m:ℝ) + 1) with hσ
  have hσ2 : σ / 2 = (m:ℝ) + 1 := by rw [hσ]; ring
  have hm1pos : (0:ℝ) < (m:ℝ) + 1 := by positivity
  have harg : ((σ:ℂ)/2) = ((m + 1 : ℕ) : ℂ) := by
    rw [hσ]; push_cast; ring

  have heq : ‖Complex.Gammaℝ (σ:ℂ)‖
      = Real.pi ^ (-((m:ℝ)+1)) * (m ! : ℝ) := by
    rw [Complex.Gammaℝ_def, norm_mul,
      show (-(σ:ℂ)/2) = -((σ:ℂ)/2) from by ring, harg,
      gapsw80_t43_norm_Gamma_nat_succ m,
      show (-((m+1:ℕ):ℂ)) = ((-((m:ℝ)+1) : ℝ):ℂ) from by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos, Complex.ofReal_re]
  rw [heq, Real.log_mul (by positivity) (by exact_mod_cast m.factorial_pos.ne'),
    Real.log_rpow Real.pi_pos]
  have hstir : (m:ℝ) * Real.log m - m ≤ Real.log (m ! : ℝ) :=
    gapsw80_t43_stirling_core hm
  have hπ : Real.log Real.pi ≤ 2 * Real.log (2 * Real.pi) := gapsw80_t43_log_pi_le
  unfold gapsw80_t43_L₀
  nlinarith [hm1pos]

theorem gapsw80_t43_log_norm_Gammaℂ_ge {m : ℕ} (hm : 1 ≤ m) :
    (m:ℝ) * Real.log m - gapsw80_t43_L₀ * ((m:ℝ) + 1)
      ≤ Real.log ‖Complex.Gammaℂ ((2 * ((m:ℝ) + 1) : ℝ):ℂ)‖ := by
  set σ : ℝ := 2 * ((m:ℝ) + 1) with hσ
  have hσnat : σ = ((2*m+1 : ℕ):ℝ) + 1 := by push_cast; rw [hσ]; ring
  have h2πpos : (0:ℝ) < 2 * Real.pi := by linarith [Real.pi_pos]
  have harg : ((σ:ℝ):ℂ) = (((2*m+1) + 1 : ℕ) : ℂ) := by
    rw [hσ]; push_cast; ring

  have heq : ‖Complex.Gammaℂ (σ:ℂ)‖
      = 2 * (2*Real.pi) ^ (-σ) * ((2*m+1)! : ℝ) := by
    rw [Complex.Gammaℂ_def, norm_mul, norm_mul, harg,
      gapsw80_t43_norm_Gamma_nat_succ (2*m+1),
      show (-(((2*m+1)+1:ℕ):ℂ)) = (((-σ):ℝ):ℂ) from by rw [hσ]; push_cast; ring,
      show ((2:ℂ)*(Real.pi:ℂ)) = (((2*Real.pi:ℝ)):ℂ) from by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos h2πpos, Complex.ofReal_re]
    norm_num
  rw [heq, Real.log_mul (by positivity) (by exact_mod_cast (2*m+1).factorial_pos.ne'),
    Real.log_mul (by norm_num) (by positivity), Real.log_rpow h2πpos]

  have hfac_le : (m ! : ℝ) ≤ ((2*m+1)! : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega)
  have hlogfac : Real.log (m ! : ℝ) ≤ Real.log ((2*m+1)! : ℝ) :=
    Real.log_le_log (by exact_mod_cast m.factorial_pos) hfac_le
  have hstir : (m:ℝ) * Real.log m - m ≤ Real.log (m ! : ℝ) :=
    gapsw80_t43_stirling_core hm
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
  unfold gapsw80_t43_L₀
  nlinarith

theorem gapsw80_t43_one_le_nrPlaces_sum (K : Type) [Field K] [NumberField K] :
    1 ≤ nrRealPlaces K + nrComplexPlaces K := by
  have hk : 1 ≤ nrRealPlaces K + 2 * nrComplexPlaces K := by
    rw [card_add_two_mul_card_eq_rank]; exact Module.finrank_pos
  omega

theorem gapsw80_t43_exists_m_superlinear (D : ℝ) :
    ∃ m : ℕ, 2 ≤ m ∧ D * ((m:ℝ) + 1) < (m:ℝ) * Real.log m := by
  set D' := max D 0 with hD'
  have hD'0 : 0 ≤ D' := le_max_right _ _
  have hlog : ∀ᶠ m : ℕ in atTop, 2 * D' < Real.log (m:ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop (2*D')
  obtain ⟨m, hmD, hm2⟩ := (hlog.and (eventually_ge_atTop 2)).exists
  refine ⟨m, hm2, ?_⟩
  have hm0 : (0:ℝ) < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
  calc D * ((m:ℝ) + 1)
      ≤ D' * ((m:ℝ) + 1) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ D' * (2 * (m:ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ hD'0
        have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
        linarith
    _ = (2 * D') * (m:ℝ) := by ring
    _ < Real.log (m:ℝ) * (m:ℝ) := mul_lt_mul_of_pos_right hmD hm0
    _ = (m:ℝ) * Real.log m := by ring

set_option maxHeartbeats 999999 in

theorem gapsw80_t43_SL_closed : gapsw80_t42_CompletedZetaRealSuperlinear := by
  have _em := Classical.em
  intro K _ _ C
  obtain ⟨m, hm2, hmD⟩ := gapsw80_t43_exists_m_superlinear (2 * |C| + gapsw80_t43_L₀)
  have hm1 : 1 ≤ m := by omega
  set σ : ℝ := 2 * ((m:ℝ) + 1) with hσdef
  have hσ4 : (4:ℝ) ≤ σ := by
    have : (2:ℝ) ≤ (m:ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hm1
    rw [hσdef]; linarith
  have hσ1 : (1:ℝ) < σ := by linarith
  have hσ0 : (0:ℝ) < σ := by linarith
  have hnorm_s : ‖(σ:ℂ)‖ = σ := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_of_pos hσ0

  refine ⟨(σ:ℂ), ?_, ?_, ?_, ?_⟩
  · rw [hnorm_s]; linarith
  · exact_mod_cast hσ0.ne'
  · intro h; rw [Complex.ofReal_eq_one] at h; linarith

  have hre : (1:ℝ) < (σ:ℂ).re := by rwa [Complex.ofReal_re]

  set L : ℝ := (m:ℝ) * Real.log m - gapsw80_t43_L₀ * ((m:ℝ) + 1) with hLdef
  have hL_pos : 0 ≤ L := by
    have h2C : 0 ≤ 2 * |C| * ((m:ℝ)+1) := by positivity
    rw [hLdef]; linarith [hmD]
  have hCL : C * σ < L := by
    rw [hσdef, hLdef]
    have habs : C * (2 * ((m:ℝ)+1)) ≤ |C| * (2 * ((m:ℝ)+1)) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    linarith [hmD]

  rw [hnorm_s, gapsw80_t10_completedDedekindZeta_eq_T1 K hre,
    gapsw80_t1_completedDedekindZeta]
  refine lt_of_lt_of_le hCL ?_

  have hDge1 : (1:ℝ) ≤ ‖(((|discr K| : ℤ) : ℂ)) ^ ((σ:ℂ) / 2)‖ :=
    gapsw80_t43_one_le_norm_discrPow K hσ0.le
  have hZge1 : (1:ℝ) ≤ ‖dedekindZeta K (σ:ℂ)‖ :=
    gapsw80_t43_one_le_norm_dedekindZeta_ofReal K hσ1
  have hGRne : Complex.Gammaℝ (σ:ℂ) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by rw [Complex.ofReal_re]; exact hσ0)
  have hGCne : Complex.Gammaℂ (σ:ℂ) ≠ 0 :=
    gapsw80_t16_Gammaℂ_ne_zero (by rw [Complex.ofReal_re]; exact hσ0)
  have hGRpos : (0:ℝ) < ‖Complex.Gammaℝ (σ:ℂ)‖ := norm_pos_iff.mpr hGRne
  have hGCpos : (0:ℝ) < ‖Complex.Gammaℂ (σ:ℂ)‖ := norm_pos_iff.mpr hGCne
  have hGRL : L ≤ Real.log ‖Complex.Gammaℝ (σ:ℂ)‖ := by
    rw [hLdef]; exact gapsw80_t43_log_norm_Gammaℝ_ge hm1
  have hGCL : L ≤ Real.log ‖Complex.Gammaℂ (σ:ℂ)‖ := by
    rw [hLdef]; exact gapsw80_t43_log_norm_Gammaℂ_ge hm1
  have hs1 : ‖(σ:ℂ) - 1‖ = σ - 1 := by
    rw [show ((σ:ℂ) - 1) = (((σ - 1 : ℝ)):ℂ) from by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_pos (by linarith)

  simp only [norm_mul, norm_pow, hnorm_s, hs1]

  have hall_pos :
      (0:ℝ) < σ * (σ - 1) *
        (‖(((|discr K| : ℤ) : ℂ)) ^ ((σ:ℂ) / 2)‖
          * ‖Complex.Gammaℝ (σ:ℂ)‖ ^ nrRealPlaces K
          * ‖Complex.Gammaℂ (σ:ℂ)‖ ^ nrComplexPlaces K
          * ‖dedekindZeta K (σ:ℂ)‖) := by
    have : (0:ℝ) < σ - 1 := by linarith
    positivity

  rw [show σ * (σ - 1) *
        (‖(((|discr K| : ℤ) : ℂ)) ^ ((σ:ℂ) / 2)‖
          * ‖Complex.Gammaℝ (σ:ℂ)‖ ^ nrRealPlaces K
          * ‖Complex.Gammaℂ (σ:ℂ)‖ ^ nrComplexPlaces K
          * ‖dedekindZeta K (σ:ℂ)‖)
      = (σ * (σ - 1)) * ‖(((|discr K| : ℤ) : ℂ)) ^ ((σ:ℂ) / 2)‖
          * ‖Complex.Gammaℝ (σ:ℂ)‖ ^ nrRealPlaces K
          * ‖Complex.Gammaℂ (σ:ℂ)‖ ^ nrComplexPlaces K
          * ‖dedekindZeta K (σ:ℂ)‖ by ring,
    Real.log_mul (by positivity) (by linarith [hZge1]),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by linarith [hDge1]),
    Real.log_pow, Real.log_pow]

  have hlog_ss1 : 0 ≤ Real.log (σ * (σ - 1)) :=
    Real.log_nonneg (by nlinarith)
  have hlogD : 0 ≤ Real.log ‖(((|discr K| : ℤ) : ℂ)) ^ ((σ:ℂ) / 2)‖ :=
    Real.log_nonneg hDge1
  have hlogZ : 0 ≤ Real.log ‖dedekindZeta K (σ:ℂ)‖ := Real.log_nonneg hZge1

  have hr1 : (nrRealPlaces K : ℝ) * L
      ≤ (nrRealPlaces K : ℝ) * Real.log ‖Complex.Gammaℝ (σ:ℂ)‖ :=
    mul_le_mul_of_nonneg_left hGRL (Nat.cast_nonneg _)
  have hr2 : (nrComplexPlaces K : ℝ) * L
      ≤ (nrComplexPlaces K : ℝ) * Real.log ‖Complex.Gammaℂ (σ:ℂ)‖ :=
    mul_le_mul_of_nonneg_left hGCL (Nat.cast_nonneg _)
  have hrsum : (1:ℝ) ≤ (nrRealPlaces K : ℝ) + (nrComplexPlaces K : ℝ) := by
    exact_mod_cast gapsw80_t43_one_le_nrPlaces_sum K
  nlinarith [mul_nonneg (Nat.cast_nonneg (nrRealPlaces K)) hL_pos,
    mul_nonneg (Nat.cast_nonneg (nrComplexPlaces K)) hL_pos]

end FLT.Gapsw80T43CompletedZetaRealSuperlinearProof

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

end

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T4MultiVarIdealThetaTransformation P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T5HeckeThetaKernel P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T6TraceDualBridge P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T8MellinGammaPartialZeta P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T10DedekindZetaBridgeA1Discharge"

open FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition FLT.Gapsw80T9ClassSumA1Closure FLT.Gapsw80T10DedekindZetaBridgeA1Discharge FLT.Gapsw80T16XiRightHalfBoundProof FLT.Gapsw80T36D1appXiEndpointResidueProof FLT.Gapsw80T43CompletedZetaRealSuperlinearProof FLT.Gapsw80T11ExplicitFormulaA34Decomp FLT.Gapsw80T32D1aBoundaryCaseDecomp FLT.Gapsw80T42D1b0a0XiNonzeroInfZerosProof in

theorem solution (K : Type) [Field K] [NumberField K] :
    ∃ Λ : ℂ → ℂ,
      DifferentiableOn ℂ Λ ({(0 : ℂ), 1}ᶜ) ∧
      (∀ s : ℂ, s ≠ 0 → s ≠ 1 → Λ (1 - s) = Λ s) ∧
      (∀ s : ℂ, 1 < s.re → Λ s =
        (((|NumberField.discr K| : ℤ) : ℂ)) ^ (s / 2)
          * Complex.Gammaℝ s ^ NumberField.InfinitePlace.nrRealPlaces K
          * Complex.Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces K
          * NumberField.dedekindZeta K s) ∧
      (∃ ξ : ℂ → ℂ, Differentiable ℂ ξ ∧
        (∀ s : ℂ, s ≠ 0 → s ≠ 1 → ξ s = s * (s - 1) * Λ s) ∧
        ∃ C : ℝ, ∀ s : ℂ, 2 ≤ ‖s‖ → Real.log ‖ξ s‖ ≤ C * ‖s‖ * Real.log ‖s‖) ∧
      (∀ ξ : ℂ → ℂ, Differentiable ℂ ξ →
        (∀ s : ℂ, s ≠ 0 → s ≠ 1 → ξ s = s * (s - 1) * Λ s) → ξ 0 ≠ 0 ∧ ξ 1 ≠ 0) ∧
      (∀ C : ℝ, ∃ s : ℂ, 2 ≤ ‖s‖ ∧ s ≠ 0 ∧ s ≠ 1 ∧
        C * ‖s‖ < Real.log ‖s * (s - 1) * Λ s‖) := by
  refine ⟨gapsw80_t9_completedDedekindZeta K, ?_, ?_, ?_, gapsw80_t16_B1_closed K,
    gapsw80_t36_D1app_closed K, gapsw80_t43_SL_closed K⟩
  · exact gapsw80_t9_differentiableOn_completedDedekindZeta K
  · exact fun s hs0 hs1 => gapsw80_t9_completedDedekindZeta_FE K hs0 hs1
  · intro s hs
    rw [gapsw80_t10_completedDedekindZeta_eq_T1 K hs]
    rfl

end
end
end
end
end
end P2MW.S_NumberField_exists_completedDedekindZeta_package
