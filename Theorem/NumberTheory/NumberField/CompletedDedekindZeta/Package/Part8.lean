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
import Def.NumberTheory.NumberField.CompletedDedekindZeta.Package.Part8


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

section

set_option maxHeartbeats 999999

p2m_open "Complex P2MW.S_NumberField_exists_completedDedekindZeta_package.Complex Real P2MW.S_NumberField_exists_completedDedekindZeta_package.Real Set P2MW.S_NumberField_exists_completedDedekindZeta_package.Set Filter P2MW.S_NumberField_exists_completedDedekindZeta_package.Filter Topology P2MW.S_NumberField_exists_completedDedekindZeta_package.Topology Matrix P2MW.S_NumberField_exists_completedDedekindZeta_package.Matrix"

p2m_open_scoped "Matrix P2MW.S_NumberField_exists_completedDedekindZeta_package.Matrix"

namespace FLT

namespace Gapsw80T2RankNGaussianPoisson

noncomputable section

variable {n : ℕ}

section Summability

theorem gapsw80_t2_posDef_quadForm_lower {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : Fin n → ℝ, c * (x ⬝ᵥ x) ≤ rQuad A x := by
  classical
  rcases isEmpty_or_nonempty (Fin n) with hE | hNE
  · exact ⟨1, one_pos, fun x => by simp [rQuad, dotProduct]⟩
  obtain ⟨i₀, hmin⟩ := Finite.exists_min hA.1.eigenvalues
  refine ⟨hA.1.eigenvalues i₀, hA.eigenvalues_pos i₀, fun x => ?_⟩
  have hquad :=
    FLT.GaussianFourierPosDef.quadForm_eq_sum_eigen hA (WithLp.toLp 2 x)
  have hxx : x ⬝ᵥ x
      = ∑ i, (WithLp.ofLp (hA.1.eigenvectorBasis.repr (WithLp.toLp 2 x)) i) ^ 2 := by
    have h1 : x ⬝ᵥ x = inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 x) :=
      FLT.GaussianFourierPosDef.dotProduct_ofLp_eq_inner
        (WithLp.toLp 2 x) (WithLp.toLp 2 x)
    have h2 := (hA.1.eigenvectorBasis.repr.inner_map_map
      (WithLp.toLp 2 x) (WithLp.toLp 2 x)).symm
    have h3 := (FLT.GaussianFourierPosDef.dotProduct_ofLp_eq_inner
      (hA.1.eigenvectorBasis.repr (WithLp.toLp 2 x))
      (hA.1.eigenvectorBasis.repr (WithLp.toLp 2 x))).symm
    rw [h1, h2, h3]; simp only [dotProduct]
    exact Finset.sum_congr rfl fun i _ => (pow_two _).symm
  calc hA.1.eigenvalues i₀ * (x ⬝ᵥ x)
      = ∑ i, hA.1.eigenvalues i₀ *
          (WithLp.ofLp (hA.1.eigenvectorBasis.repr (WithLp.toLp 2 x)) i) ^ 2 := by
        rw [hxx, Finset.mul_sum]
    _ ≤ ∑ i, hA.1.eigenvalues i *
          (WithLp.ofLp (hA.1.eigenvectorBasis.repr (WithLp.toLp 2 x)) i) ^ 2 :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hmin i) (sq_nonneg _)
    _ = rQuad A x := hquad.symm

theorem gapsw80_t2_summable_1D {a : ℝ} (ha : 0 < a) (b : ℂ) :
    Summable fun k : ℤ =>
      ‖cexp (-(π : ℂ) * (a : ℂ) * (k : ℂ) ^ 2 + 2 * π * b * (k : ℂ))‖ := by
  have hre : (-(π : ℂ) * (a : ℂ)).re < 0 := by
    simp only [neg_mul, neg_re, Complex.re_ofReal_mul, Complex.ofReal_re]
    exact neg_neg_of_pos (mul_pos pi_pos ha)
  have hO := (cexp_neg_quadratic_isLittleO_abs_rpow_cocompact hre (2 * π * b)
    (-2)).isBigO.comp_tendsto Int.tendsto_coe_cofinite
  simp only [Function.comp_def, Complex.ofReal_intCast] at hO
  exact (summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two) hO).norm

theorem gapsw80_t2_summable_prod_fin :
    ∀ {n : ℕ} {f : Fin n → ℤ → ℝ}, (∀ i k, 0 ≤ f i k) → (∀ i, Summable (f i)) →
      Summable fun v : Fin n → ℤ => ∏ i, f i (v i) := by
  intro n
  induction n with
  | zero =>
    intro f _ _
    have hU : Subsingleton (Fin 0 → ℤ) := inferInstance
    refine ⟨1, ?_⟩
    have hconst : (fun v : Fin 0 → ℤ => ∏ i, f i (v i)) = fun _ => 1 := by
      funext v; exact Finset.prod_empty
    rw [hconst]
    simpa using hasSum_ite_eq (default : Fin 0 → ℤ) (1 : ℝ)
  | succ m IH =>
    intro f hpos hsum
    set e : (Fin (m + 1) → ℤ) ≃ (Fin m → ℤ) × ℤ :=
      { toFun := fun v => ⟨v ∘ Fin.castSucc, v (Fin.last m)⟩
        invFun := fun p => Fin.snoc p.1 p.2
        left_inv := fun v => by
          funext i; dsimp only
          rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
          · simp [Fin.snoc_castSucc]
          · simp [Fin.snoc_last]
        right_inv := fun p => by
          ext
          · simp [Fin.snoc_castSucc]
          · simp [Fin.snoc_last] }
    have hIH : Summable fun v : Fin m → ℤ => ∏ i, f (Fin.castSucc i) (v i) :=
      IH (fun i k => hpos _ k) fun i => hsum _
    have hprod :
        Summable fun p : (Fin m → ℤ) × ℤ =>
          (∏ i, f (Fin.castSucc i) (p.1 i)) * f (Fin.last m) p.2 :=
      hIH.mul_of_nonneg (hsum _) (fun v => Finset.prod_nonneg fun i _ => hpos _ _)
        (fun k => hpos _ k)
    have hprod' :
        Summable fun p : (Fin m → ℤ) × ℤ =>
          ∏ i, f i ((Fin.snoc p.1 p.2 : Fin (m + 1) → ℤ) i) := by
      refine hprod.congr fun p => ?_
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
    exact e.symm.summable_iff.mp hprod'

theorem gapsw80_t2_summable_1D_real {a : ℝ} (ha : 0 < a) (r : ℝ) :
    Summable fun k : ℤ => rexp (-(a * (k : ℝ) ^ 2) + r * (k : ℝ)) := by
  have hπ : (π : ℝ) ≠ 0 := pi_ne_zero
  have h := gapsw80_t2_summable_1D (a := a / π) (div_pos ha pi_pos)
    (((r / (2 * π)) : ℝ) : ℂ)
  refine h.congr fun k => ?_
  have heq : (-(π : ℂ) * ((a / π : ℝ) : ℂ) * (k : ℂ) ^ 2
        + 2 * π * (((r / (2 * π)) : ℝ) : ℂ) * (k : ℂ))
      = (((-(a * (k : ℝ) ^ 2) + r * (k : ℝ)) : ℝ) : ℂ) := by
    push_cast
    field_simp
  rw [heq, Complex.norm_exp, Complex.ofReal_re]

theorem gapsw80_t2_summable_gaussian_Zn {c : ℝ} (hc : 0 < c) :
    Summable fun v : Fin n → ℤ => rexp (-(c * ∑ i, (v i : ℝ) ^ 2)) := by
  have hrew : (fun v : Fin n → ℤ => rexp (-(c * ∑ i, (v i : ℝ) ^ 2)))
      = fun v => ∏ i, rexp (-(c * (v i : ℝ) ^ 2)) := by
    funext v; rw [← Real.exp_sum, Finset.mul_sum, Finset.sum_neg_distrib]
  rw [hrew]
  exact gapsw80_t2_summable_prod_fin (n := n)
    (f := fun _ k => rexp (-(c * (k : ℝ) ^ 2)))
    (fun _ _ => (Real.exp_pos _).le)
    (fun _ => (gapsw80_t2_summable_1D_real hc 0).congr fun k => by
      rw [zero_mul, add_zero])

theorem gapsw80_t2_re_cQuad_liftC (A : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → ℂ) :
    (cQuad (liftC A) z).re
      = rQuad A (fun i => (z i).re) - rQuad A (fun i => (z i).im) := by
  have hmv : ∀ i, ((liftC A) *ᵥ z) i = ∑ j, (A i j : ℂ) * z j := fun i => by
    simp only [Matrix.mulVec, dotProduct, liftC, Matrix.map_apply]
  have hmvR : ∀ (x : Fin n → ℝ) i, (A *ᵥ x) i = ∑ j, A i j * x j := fun x i => by
    simp only [Matrix.mulVec, dotProduct]
  unfold cQuad rQuad
  simp only [dotProduct, hmv, hmvR]
  rw [Complex.re_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.mul_re, Complex.re_sum, Complex.im_sum]
  simp only [Complex.re_ofReal_mul, Complex.im_ofReal_mul]

theorem gapsw80_t2_summable_thetaTerm {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) {t : ℝ} (ht : 0 < t) (b : Fin n → ℂ) :
    Summable fun v : Fin n → ℤ => ‖thetaTerm A t b v‖ := by
  obtain ⟨c, hc, hQ⟩ := gapsw80_t2_posDef_quadForm_lower hA
  have hxx : ∀ v : Fin n → ℤ, zcastR v ⬝ᵥ zcastR v = ∑ i, (v i : ℝ) ^ 2 := fun v => by
    simp only [dotProduct, zcastR]; exact Finset.sum_congr rfl fun i _ => (sq _).symm
  set g : Fin n → ℤ → ℝ := fun i k =>
    rexp (-(π * t * c * (k : ℝ) ^ 2) + 2 * π * (b i).re * (k : ℝ))
  have hmajor : Summable fun v : Fin n → ℤ => ∏ i, g i (v i) :=
    gapsw80_t2_summable_prod_fin (n := n) (f := g)
      (fun _ _ => (Real.exp_pos _).le)
      (fun i => (gapsw80_t2_summable_1D_real (a := π * t * c) (by positivity)
          (2 * π * (b i).re)).congr
        fun k => by unfold g; ring_nf)
  refine hmajor.of_nonneg_of_le (fun v => norm_nonneg _) fun v => ?_
  unfold thetaTerm
  rw [Complex.norm_exp]
  have hre : (-(π : ℂ) * (t : ℂ) * (rQuad A (zcastR v) : ℂ)
        + 2 * π * ∑ i, b i * (v i : ℂ)).re
      = -(π * t * rQuad A (zcastR v)) + 2 * π * ∑ i, (b i).re * (v i : ℝ) := by
    have h1 : -(π : ℂ) * (t : ℂ) * (rQuad A (zcastR v) : ℂ)
        = (((-(π * t * rQuad A (zcastR v))) : ℝ) : ℂ) := by push_cast; ring
    have h2 : (2 : ℂ) * (π : ℂ) = (((2 * π) : ℝ) : ℂ) := by push_cast; ring
    rw [h1, h2, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul,
      Complex.re_sum]
    congr 2
    exact Finset.sum_congr rfl fun i _ => by
      simp [Complex.mul_re, Complex.intCast_re, Complex.intCast_im]
  rw [hre, show (∏ i, g i (v i)) = rexp (∑ i,
      (-(π * t * c * (v i : ℝ) ^ 2) + 2 * π * (b i).re * (v i : ℝ))) from
    (Real.exp_sum _ _).symm]
  apply Real.exp_le_exp.mpr
  have hQv := hQ (zcastR v); rw [hxx v] at hQv
  have hsplit : (∑ i, (-(π * t * c * (v i : ℝ) ^ 2) + 2 * π * (b i).re * (v i : ℝ)))
      = -(π * t) * (c * ∑ i, (v i : ℝ) ^ 2)
        + (2 * π) * ∑ i, (b i).re * (v i : ℝ) := by
    rw [Finset.sum_add_distrib]; congr 1
    · rw [← mul_assoc, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    · rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsplit]
  nlinarith [mul_pos pi_pos ht]

theorem gapsw80_t2_summable_dualTerm {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosDef) {t : ℝ} (ht : 0 < t) (b : Fin n → ℂ) :
    Summable fun w : Fin n → ℤ => ‖dualTerm A t b w‖ := by
  obtain ⟨c, hc, hQ⟩ := gapsw80_t2_posDef_quadForm_lower hA.inv
  set d : Fin n → ℝ := fun i => (b i).im
  set C₁ : ℝ := rexp (π / t * rQuad A⁻¹ (fun i => (b i).re))
  have hC₁ : 0 ≤ C₁ := (Real.exp_pos _).le

  have hconst : ∀ w : Fin n → ℤ,
      ‖dualTerm A t b w‖
        = C₁ * rexp (-(π / t) * rQuad A⁻¹ (fun i => (w i : ℝ) - d i)) := by
    intro w
    unfold dualTerm
    rw [Complex.norm_exp, ← Real.exp_add]
    congr 1
    have hcoef : -(π : ℂ) / (t : ℂ) = (((-(π / t)) : ℝ) : ℂ) := by push_cast; ring
    rw [hcoef, Complex.re_ofReal_mul, gapsw80_t2_re_cQuad_liftC]
    have hre : (fun i => ((w i : ℂ) + Complex.I * b i).re)
        = fun i => (w i : ℝ) - d i := by
      funext i; simp only [Complex.add_re, Complex.intCast_re, Complex.mul_re,
        Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, d]; ring
    have him : (fun i => ((w i : ℂ) + Complex.I * b i).im)
        = fun i => (b i).re := by
      funext i; simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im]
    rw [hre, him]; ring

  set g : Fin n → ℤ → ℝ := fun i k => rexp (-(π * c / t) * ((k : ℝ) - d i) ^ 2)
  have hg_sum : ∀ i, Summable (g i) := fun i => by
    refine ((gapsw80_t2_summable_1D_real (a := π * c / t) (by positivity)
        (2 * (π * c / t) * d i)).mul_left (rexp (-(π * c / t) * (d i) ^ 2))).congr
      fun k => ?_
    unfold g; rw [← Real.exp_add]; ring_nf
  have hmajor : Summable fun w : Fin n → ℤ => ∏ i, g i (w i) :=
    gapsw80_t2_summable_prod_fin (n := n) (f := g)
      (fun _ _ => (Real.exp_pos _).le) hg_sum
  refine (hmajor.mul_left C₁).of_nonneg_of_le (fun w => norm_nonneg _) fun w => ?_
  rw [hconst w]
  refine mul_le_mul_of_nonneg_left ?_ hC₁
  rw [show (∏ i, g i (w i))
      = rexp (∑ i, -(π * c / t) * ((w i : ℝ) - d i) ^ 2) from (Real.exp_sum _ _).symm]
  apply Real.exp_le_exp.mpr
  have hQw := hQ (fun i => (w i : ℝ) - d i)
  have hdot : (fun i => (w i : ℝ) - d i) ⬝ᵥ (fun i => (w i : ℝ) - d i)
      = ∑ i, ((w i : ℝ) - d i) ^ 2 := by
    simp only [dotProduct]; exact Finset.sum_congr rfl fun i _ => (sq _).symm
  rw [hdot] at hQw
  rw [← Finset.mul_sum, show -(π * c / t) = -(π / t) * c by ring, mul_assoc]
  have hnp : -(π / t) ≤ 0 := neg_nonpos_of_nonneg (div_pos pi_pos ht).le
  exact mul_le_mul_of_nonpos_left hQw hnp

end Summability

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation"

section BilinearSchur

variable {R : Type*} [CommRing R] {m k : ℕ}

theorem gapsw80_t2_bilin_schur_eq₂₂
    (P : Matrix (Fin m) (Fin m) R) (q : Matrix (Fin m) (Fin k) R)
    (D : Matrix (Fin k) (Fin k) R) [Invertible D] (hD : Dᵀ = D)
    (x : Fin m → R) (y : Fin k → R) :
    (Sum.elim x y) ᵥ* (fromBlocks P q qᵀ D) ⬝ᵥ (Sum.elim x y)
      = ((⅟D * qᵀ) *ᵥ x + y) ᵥ* D ⬝ᵥ ((⅟D * qᵀ) *ᵥ x + y)
        + x ᵥ* (P - q * ⅟D * qᵀ) ⬝ᵥ x := by

  have hDinv : (⅟D)ᵀ = ⅟D := by
    have : Dᵀ * (⅟D)ᵀ = 1 := by rw [← Matrix.transpose_mul, invOf_mul_self,
      Matrix.transpose_one]
    rw [hD] at this
    exact (invOf_eq_right_inv this).symm
  have hz : ((⅟D * qᵀ) *ᵥ x) ᵥ* D = x ᵥ* q := by
    rw [← vecMul_transpose, Matrix.transpose_mul, hDinv, Matrix.transpose_transpose,
      vecMul_vecMul, Matrix.mul_assoc, invOf_mul_self, Matrix.mul_one]
  have hDz : D *ᵥ ((⅟D * qᵀ) *ᵥ x) = qᵀ *ᵥ x := by
    rw [mulVec_mulVec, ← Matrix.mul_assoc, mul_invOf_self, Matrix.one_mul]
  have hxy : x ᵥ* q ⬝ᵥ y = y ᵥ* qᵀ ⬝ᵥ x := by
    rw [← dotProduct_mulVec, vecMul_transpose, dotProduct_comm]
  have hqS : x ᵥ* (q * ⅟D * qᵀ) ⬝ᵥ x = x ᵥ* q ⬝ᵥ ((⅟D * qᵀ) *ᵥ x) := by
    rw [Matrix.mul_assoc, ← vecMul_vecMul, ← dotProduct_mulVec]
  have hyDz : y ᵥ* D ⬝ᵥ ((⅟D * qᵀ) *ᵥ x) = y ᵥ* qᵀ ⬝ᵥ x := by
    rw [← dotProduct_mulVec, hDz, dotProduct_mulVec]
  simp only [vecMul_fromBlocks, Sum.elim_comp_inl, Sum.elim_comp_inr,
    sumElim_dotProduct_sumElim, add_vecMul, vecMul_sub, add_dotProduct,
    dotProduct_add, sub_dotProduct, hz, hyDz, hqS]
  ring

theorem gapsw80_t2_bilin_schur_eq₂₂'
    (P : Matrix (Fin m) (Fin m) R) (q : Matrix (Fin m) (Fin k) R)
    (D : Matrix (Fin k) (Fin k) R) [Invertible D] (hD : Dᵀ = D)
    (x : Fin m → R) (y : Fin k → R) :
    (Sum.elim x y) ⬝ᵥ ((fromBlocks P q qᵀ D) *ᵥ (Sum.elim x y))
      = ((⅟D * qᵀ) *ᵥ x + y) ⬝ᵥ (D *ᵥ ((⅟D * qᵀ) *ᵥ x + y))
        + x ⬝ᵥ ((P - q * ⅟D * qᵀ) *ᵥ x) := by
  rw [dotProduct_mulVec, dotProduct_mulVec, dotProduct_mulVec]
  exact gapsw80_t2_bilin_schur_eq₂₂ P q D hD x y

theorem gapsw80_t2_bilin_schur_inv_scalar
    (P : Matrix (Fin m) (Fin m) R) (q : Matrix (Fin m) (Fin 1) R)
    (a : R) [Invertible a] (hP : Pᵀ = P)
    [Invertible (P - q * ⅟a • qᵀ)]
    (X : Fin m → R) (Y : R) :
    (Sum.elim X (fun _ => Y)) ⬝ᵥ
        ((fromBlocks P q qᵀ ((a : R) • (1 : Matrix (Fin 1) (Fin 1) R)))⁻¹
          *ᵥ (Sum.elim X (fun _ => Y)))
      = (X - (⅟a * Y) • (fun i => q i 0)) ⬝ᵥ
          ((P - q * ⅟a • qᵀ)⁻¹ *ᵥ (X - (⅟a * Y) • (fun i => q i 0)))
        + ⅟a * Y ^ 2 := by
  classical
  set D : Matrix (Fin 1) (Fin 1) R := (a : R) • 1 with hD
  haveI hDi : Invertible D :=
    ⟨⅟a • 1, by rw [hD, smul_mul_smul_comm, invOf_mul_self, one_mul, one_smul],
      by rw [hD, smul_mul_smul_comm, mul_invOf_self, one_mul, one_smul]⟩
  have hiD : ⅟D = (⅟a : R) • (1 : Matrix (Fin 1) (Fin 1) R) :=
    invOf_eq_right_inv
      (by rw [hD, smul_mul_smul_comm, mul_invOf_self, one_mul, one_smul])
  set S : Matrix (Fin m) (Fin m) R := P - q * ⅟a • qᵀ with hS
  have hSeq : P - q * ⅟D * qᵀ = S := by
    rw [hS, hiD, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul]
  haveI : Invertible (P - q * ⅟D * qᵀ) := hSeq ▸ (inferInstance : Invertible S)
  haveI hMi : Invertible (fromBlocks P q qᵀ D) := fromBlocks₂₂Invertible P q qᵀ D

  set q₀ : Fin m → R := fun i => q i 0
  have hq0T : ∀ x : Fin m → R, qᵀ *ᵥ x = fun _ => q₀ ⬝ᵥ x := fun x => by
    funext j; fin_cases j; simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply, q₀]
  have hq0 : ∀ y : Fin 1 → R, q *ᵥ y = y 0 • q₀ := fun y => by
    funext i; simp [Matrix.mulVec, dotProduct, Fin.sum_univ_one, q₀, mul_comm]
  have hF1 : ∀ (c : R) (y : Fin 1 → R), (fun _ => c) ⬝ᵥ y = c * y 0 := fun c y => by
    simp [dotProduct, Fin.sum_univ_one]
  have hSiT : (⅟S)ᵀ = ⅟S := by
    have hST : Sᵀ = S := by
      rw [hS, Matrix.transpose_sub, hP, Matrix.transpose_mul, Matrix.transpose_smul,
        Matrix.transpose_transpose, Matrix.smul_mul, ← Matrix.mul_smul]
    have h1 : Sᵀ * (⅟S)ᵀ = 1 := by rw [← Matrix.transpose_mul, invOf_mul_self,
      Matrix.transpose_one]
    rw [hST] at h1; exact (invOf_eq_right_inv h1).symm
  have hswap : ∀ x y : Fin m → R, x ⬝ᵥ (⅟S *ᵥ y) = y ⬝ᵥ (⅟S *ᵥ x) := fun x y => by
    rw [dotProduct_mulVec, ← Matrix.mulVec_transpose (⅟S) x, hSiT, dotProduct_comm]
  have hDy : ⅟D *ᵥ (fun _ => Y : Fin 1 → R) = fun _ => ⅟a * Y := by
    funext j; fin_cases j
    simp only [hiD, smul_mulVec, Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul]

  rw [← Matrix.invOf_eq_nonsing_inv, invOf_fromBlocks₂₂_eq, Matrix.fromBlocks_mulVec,
    Sum.elim_comp_inl, Sum.elim_comp_inr, sumElim_dotProduct_sumElim]
  simp only [hSeq]

  have hTop : (⅟S *ᵥ X + (-(⅟S * q * ⅟D)) *ᵥ fun _ => Y)
      = ⅟S *ᵥ X - (⅟a * Y) • (⅟S *ᵥ q₀) := by
    rw [Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hDy,
      hq0, Matrix.mulVec_smul, sub_eq_add_neg]
  have hBot : ((-(⅟D * qᵀ * ⅟S)) *ᵥ X + (⅟D + ⅟D * qᵀ * ⅟S * q * ⅟D) *ᵥ fun _ => Y)
      = fun _ => -(⅟a * (q₀ ⬝ᵥ (⅟S *ᵥ X)))
          + (⅟a * Y + ⅟a ^ 2 * Y * (q₀ ⬝ᵥ (⅟S *ᵥ q₀))) := by
    funext j; fin_cases j
    simp only [Matrix.neg_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hDy,
      hq0, Matrix.mulVec_smul, hq0T, hiD, smul_mulVec, Matrix.one_mulVec,
      Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, smul_smul]
    ring
  rw [hTop, hBot, hF1]
  rw [← Matrix.invOf_eq_nonsing_inv, Matrix.mulVec_sub, Matrix.mulVec_smul]
  simp only [dotProduct_sub, sub_dotProduct, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, hswap X q₀]
  ring

theorem gapsw80_t2_posDef_schur
    {P : Matrix (Fin m) (Fin m) ℝ} {q : Matrix (Fin m) (Fin k) ℝ}
    {D : Matrix (Fin k) (Fin k) ℝ} [Invertible D] (hD : D.IsHermitian)
    (hM : (fromBlocks P q qᵀ D).PosDef) :
    (P - q * ⅟D * qᵀ).PosDef := by
  have hMi := (posDef_iff_dotProduct_mulVec).mp hM
  have hDT : Dᵀ = D := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]; exact hD
  have hDiT : (⅟D)ᵀ = ⅟D := by
    have : Dᵀ * (⅟D)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, invOf_mul_self, Matrix.transpose_one]
    rw [hDT] at this; exact (invOf_eq_right_inv this).symm
  have hPherm : P.IsHermitian := (Matrix.isHermitian_fromBlocks_iff.mp hMi.1).1
  have hPT : Pᵀ = P := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]; exact hPherm
  have hSH : (P - q * ⅟D * qᵀ).IsHermitian := by
    show (P - q * ⅟D * qᵀ)ᴴ = P - q * ⅟D * qᵀ
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_sub,
      Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      hPT, hDiT, Matrix.mul_assoc]
  refine (posDef_iff_dotProduct_mulVec).mpr ⟨hSH, fun x hx => ?_⟩

  set y : Fin k → ℝ := -((⅟D * qᵀ) *ᵥ x) with hy
  have hxy : Sum.elim x y ≠ 0 := fun h => hx (funext fun i => by
    have := congrFun h (Sum.inl i); simpa using this)
  have key : 0 < star (Sum.elim x y) ⬝ᵥ ((fromBlocks P q qᵀ D) *ᵥ Sum.elim x y) :=
    hMi.2 hxy
  rw [show star (Sum.elim x y) = Sum.elim x y from rfl,
    gapsw80_t2_bilin_schur_eq₂₂' P q D hDT x y] at key
  simp only [hy, _root_.neg_add_cancel, Matrix.mulVec_zero, dotProduct_zero,
    zero_add] at key
  simpa [show star x = x from rfl] using key

end BilinearSchur
end
end Gapsw80T2RankNGaussianPoisson
end FLT
end
end
end P2MW.S_NumberField_exists_completedDedekindZeta_package
