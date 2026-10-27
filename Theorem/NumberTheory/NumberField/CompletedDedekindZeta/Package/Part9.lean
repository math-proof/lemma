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
import Def.NumberTheory.NumberField.CompletedDedekindZeta.Package.Part9


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

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation"

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation"

section InductionStep

variable {m : ℕ}

set_option maxHeartbeats 999999 in

theorem gapsw80_t2_poisson_step
    (IH : ∀ (S : Matrix (Fin m) (Fin m) ℝ), S.PosDef →
      ∀ {t : ℝ}, 0 < t → ∀ b : Fin m → ℂ, PoissonLaw S t b)
    (M : Matrix (Fin m ⊕ Fin 1) (Fin m ⊕ Fin 1) ℝ) (hM : M.PosDef)
    {t : ℝ} (ht : 0 < t) (b : (Fin m ⊕ Fin 1) → ℂ) :
    PoissonLawBlock M t b := by
  classical

  set P : Matrix (Fin m) (Fin m) ℝ := M.toBlocks₁₁
  set q : Matrix (Fin m) (Fin 1) ℝ := M.toBlocks₁₂
  set a : ℝ := M (Sum.inr 0) (Sum.inr 0)
  set b' : Fin m → ℂ := b ∘ Sum.inl
  set b₁ : ℂ := b (Sum.inr 0)
  set q₀ : Fin m → ℝ := fun i => q i 0
  have hMT : Mᵀ = M := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]; exact hM.1
  have hMblock : M = fromBlocks P q qᵀ ((a : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) := by
    conv_lhs => rw [← M.fromBlocks_toBlocks]
    congr 1
    · ext i j
      have := congrFun (congrFun hMT (Sum.inl j)) (Sum.inr i)
      simp [Matrix.toBlocks₂₁, Matrix.toBlocks₁₂, Matrix.transpose_apply] at this
      exact this
    · ext i j; fin_cases i; fin_cases j
      simp [Matrix.toBlocks₂₂, a, Matrix.smul_apply, Matrix.one_apply]
  have ha : 0 < a := by
    set v₀ : (Fin m ⊕ Fin 1) → ℝ := Sum.elim 0 (fun _ => (1 : ℝ)) with hv₀
    have hne : v₀ ≠ 0 := fun h =>
      (one_ne_zero : (1 : ℝ) ≠ 0) (by have := congrFun h (Sum.inr 0); simpa [hv₀] using this)
    have key : 0 < star v₀ ⬝ᵥ (M *ᵥ v₀) :=
      (posDef_iff_dotProduct_mulVec.mp hM).2 hne
    have heval : star v₀ ⬝ᵥ (M *ᵥ v₀) = a := by
      rw [show (star v₀ : _ → ℝ) = v₀ from rfl, hv₀, hMblock, fromBlocks_mulVec,
        sumElim_dotProduct_sumElim]
      simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.mulVec_zero, zero_add,
        dotProduct_zero, smul_mulVec, Matrix.one_mulVec, dotProduct,
        Fin.sum_univ_one, Pi.smul_apply, smul_eq_mul, mul_one, one_mul,
        Pi.zero_apply, zero_mul, Finset.sum_const_zero]
    rwa [heval] at key
  haveI haI : Invertible a := invertibleOfNonzero ha.ne'
  haveI haCI : Invertible (a : ℂ) := invertibleOfNonzero (Complex.ofReal_ne_zero.mpr ha.ne')
  have hia : (⅟a : ℝ) = a⁻¹ := invOf_eq_inv a
  have hiaC : (⅟(a : ℂ) : ℂ) = (a : ℂ)⁻¹ := invOf_eq_inv (a : ℂ)
  haveI hDi : Invertible ((a : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) :=
    ⟨⅟a • 1, by rw [smul_mul_smul_comm, invOf_mul_self, one_mul, one_smul],
      by rw [smul_mul_smul_comm, mul_invOf_self, one_mul, one_smul]⟩
  have hiD : ⅟((a : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ))
      = (⅟a : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) :=
    invOf_eq_right_inv (by rw [smul_mul_smul_comm, mul_invOf_self, one_mul, one_smul])
  set S : Matrix (Fin m) (Fin m) ℝ := P - q * ⅟a • qᵀ with hS
  have hSpd : S.PosDef := by
    have hDh : ((a : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)).IsHermitian := by
      show _ = _; rw [Matrix.conjTranspose_eq_transpose_of_trivial,
        Matrix.transpose_smul, Matrix.transpose_one]
    have hSalt :
        (P - q * ⅟((a : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) * qᵀ).PosDef :=
      gapsw80_t2_posDef_schur hDh (hMblock ▸ hM)
    rwa [hiD, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      ← Matrix.mul_smul] at hSalt
  have hdetS : 0 < S.det := hSpd.det_pos
  haveI hSI : Invertible S :=
    Matrix.invertibleOfIsUnitDet S (isUnit_iff_ne_zero.mpr hdetS.ne')
  have hPT : Pᵀ = P := by
    ext i j
    have := congrFun (congrFun hMT (Sum.inl i)) (Sum.inl j)
    simpa [Matrix.transpose_apply, P, Matrix.toBlocks₁₁] using this

  set e : ((Fin m ⊕ Fin 1) → ℤ) ≃ (Fin m → ℤ) × ℤ :=
    { toFun := fun v => ⟨v ∘ Sum.inl, v (Sum.inr 0)⟩
      invFun := fun p => Sum.elim p.1 (fun _ => p.2)
      left_inv := fun v => by funext i; cases i with
        | inl i => rfl
        | inr j => fin_cases j; rfl
      right_inv := fun p => rfl }
  set q₀u : (Fin m → ℤ) → ℝ := fun u => ∑ i, q₀ i * (u i : ℝ)

  have hQsplit : ∀ (u : Fin m → ℤ) (k : ℤ),
      (fun i => ((Sum.elim u (fun _ => k) : (Fin m ⊕ Fin 1) → ℤ) i : ℝ))
          ⬝ᵥ (M *ᵥ fun i => ((Sum.elim u (fun _ => k) : (Fin m ⊕ Fin 1) → ℤ) i : ℝ))
        = a * (a⁻¹ * q₀u u + (k : ℝ)) ^ 2 + rQuad S (zcastR u) := by
    intro u k
    have hcast : (fun i => ((Sum.elim u (fun _ => k) : (Fin m ⊕ Fin 1) → ℤ) i : ℝ))
        = Sum.elim (zcastR u) (fun _ => (k : ℝ)) := by
      funext i; cases i with | inl i => rfl | inr j => rfl
    rw [hcast, hMblock,
      gapsw80_t2_bilin_schur_eq₂₂' P q ((a : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ))
        (by rw [Matrix.transpose_smul, Matrix.transpose_one])
        (zcastR u) (fun _ => (k : ℝ))]
    have hSeq : P - q * ⅟((a : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) * qᵀ = S := by
      rw [hiD, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ← Matrix.mul_smul]
    rw [hSeq]
    congr 1
    have hv : (⅟((a : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) * qᵀ) *ᵥ zcastR u
          + (fun _ => (k : ℝ))
        = fun _ => a⁻¹ * q₀u u + (k : ℝ) := by
      funext j
      simp only [hiD, Matrix.smul_mul, Matrix.one_mul, smul_mulVec, Matrix.mulVec,
        dotProduct, Matrix.transpose_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply,
        q₀u, q₀, zcastR, hia, Fin.eq_zero j]
    rw [hv, smul_mulVec, Matrix.one_mulVec]
    simp only [dotProduct, Fin.sum_univ_one, Pi.smul_apply, smul_eq_mul]
    ring

  have hLsplit : ∀ (u : Fin m → ℤ) (k : ℤ),
      (∑ i, b i * ((Sum.elim u (fun _ => k) : (Fin m ⊕ Fin 1) → ℤ) i : ℂ))
        = (∑ i, b' i * (u i : ℂ)) + b₁ * (k : ℂ) := by
    intro u k
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Fin.sum_univ_one, b', b₁,
      Function.comp_apply]

  set β : (Fin m → ℤ) → ℂ := fun u => b₁ - (t : ℂ) * (q₀u u : ℂ)
  have htare : 0 < ((t * a : ℝ) : ℂ).re := by
    rw [Complex.ofReal_re]; exact mul_pos ht ha

  have h1D : ∀ u : Fin m → ℤ,
      (∑' k : ℤ, cexp (-(π : ℂ) * ((t * a : ℝ) : ℂ) * (k : ℂ) ^ 2
          + 2 * π * (β u) * (k : ℂ)))
        = 1 / (((t * a : ℝ) : ℂ)) ^ (1 / 2 : ℂ)
          * ∑' w : ℤ, cexp (-(π : ℂ) / ((t * a : ℝ) : ℂ)
              * ((w : ℂ) + Complex.I * (β u)) ^ 2) :=
    fun u => Complex.tsum_exp_neg_quadratic htare (β u)

  set β' : ℤ → (Fin m → ℂ) :=
    fun w i => b' i + Complex.I * (a : ℂ)⁻¹ * ((w : ℂ) + Complex.I * b₁) * (q₀ i : ℂ)
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hqsum : ∀ u : Fin m → ℤ,
      (∑ i, (q₀ i : ℂ) * (u i : ℂ)) = ((q₀u u : ℝ) : ℂ) := fun u => by
    simp only [q₀u, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_intCast]
  have hβ'sum : ∀ (w : ℤ) (u : Fin m → ℤ), (∑ i, (β' w) i * (u i : ℂ))
      = (∑ i, b' i * (u i : ℂ))
        + Complex.I * (a : ℂ)⁻¹ * ((w : ℂ) + Complex.I * b₁) * (q₀u u : ℂ) := fun w u => by
    rw [← hqsum u]
    simp only [β', add_mul, Finset.sum_add_distrib, Finset.mul_sum]; ring_nf

  have hExpEq : ∀ (u : Fin m → ℤ) (w : ℤ),
      (-(π : ℂ) * (t : ℂ)
            * ((a * (a⁻¹ * q₀u u) ^ 2 : ℝ) : ℂ)
          + 2 * π * (∑ i, b' i * (u i : ℂ))
          + (-(π : ℂ) / ((t * a : ℝ) : ℂ) * ((w : ℂ) + Complex.I * (β u)) ^ 2))
        = (-(π : ℂ) / ((t * a : ℝ) : ℂ) * ((w : ℂ) + Complex.I * b₁) ^ 2)
          + 2 * π * (∑ i, (β' w) i * (u i : ℂ)) := by
    intro u w
    rw [hβ'sum w u]
    simp only [β, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_add,
      Complex.ofReal_inv]
    have hI2 : (Complex.I : ℂ) ^ 2 = -1 := Complex.I_sq
    field_simp
    ring_nf
    simp only [hI2]
    ring

  set Fuw : (Fin m → ℤ) × ℤ → ℂ := fun p =>
    cexp (-(π : ℂ) / ((t * a : ℝ) : ℂ) * ((p.2 : ℂ) + Complex.I * b₁) ^ 2)
      * thetaTerm S t (β' p.2) p.1
  have haiC : ((a : ℂ))⁻¹ = (((a⁻¹ : ℝ)) : ℂ) := by
    rw [Complex.ofReal_inv]
  have hReβ' : ∀ w i, (β' w i).re = (b' i).re - a⁻¹ * b₁.re * q₀ i := fun w i => by
    have h1 : β' w i
        = b' i + (((a⁻¹ * q₀ i : ℝ)) : ℂ) * (Complex.I * (w : ℂ) - b₁) := by
      simp only [β', haiC, Complex.I_sq]; push_cast; ring_nf; simp [Complex.I_sq]; ring
    rw [h1, Complex.add_re, Complex.re_ofReal_mul, Complex.sub_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.intCast_im]
    ring
  have hR2' : Summable fun p : (Fin m → ℤ) × ℤ => ‖Fuw p‖ := by
    obtain ⟨c, hc, hQ⟩ := gapsw80_t2_posDef_quadForm_lower hSpd
    set gU : Fin m → ℤ → ℝ := fun i k =>
      rexp (-(π * t * c * (k : ℝ) ^ 2)
        + 2 * π * ((b' i).re - a⁻¹ * b₁.re * q₀ i) * (k : ℝ))
    have hUmaj : Summable fun u : Fin m → ℤ => ∏ i, gU i (u i) :=
      gapsw80_t2_summable_prod_fin (n := m) (f := gU)
        (fun _ _ => (Real.exp_pos _).le)
        (fun i => (gapsw80_t2_summable_1D_real (a := π * t * c) (by positivity)
            (2 * π * ((b' i).re - a⁻¹ * b₁.re * q₀ i))).congr
          fun k => by unfold gU; ring_nf)
    have hWmaj : Summable fun w : ℤ =>
        ‖cexp (-(π : ℂ) / ((t * a : ℝ) : ℂ)
          * ((w : ℂ) + Complex.I * b₁) ^ 2)‖ := by
      have hcoef : (-(π : ℂ) / ((t * a : ℝ) : ℂ))
          = (((-(π / (t * a))) : ℝ) : ℂ) := by push_cast; ring
      have hnorm : ∀ w : ℤ,
          ‖cexp (-(π : ℂ) / ((t * a : ℝ) : ℂ) * ((w : ℂ) + Complex.I * b₁) ^ 2)‖
            = rexp (-(π / (t * a)) * ((w : ℝ) - b₁.im) ^ 2)
              * rexp ((π / (t * a)) * b₁.re ^ 2) := fun w => by
        rw [Complex.norm_exp, hcoef, Complex.re_ofReal_mul, ← Real.exp_add]
        congr 1
        have : ((w : ℂ) + Complex.I * b₁).re = (w : ℝ) - b₁.im ∧
            ((w : ℂ) + Complex.I * b₁).im = b₁.re := by
          refine ⟨?_, ?_⟩ <;>
            simp only [Complex.add_re, Complex.add_im, Complex.mul_re,
              Complex.mul_im, Complex.I_re, Complex.I_im, Complex.intCast_re,
              Complex.intCast_im, zero_mul, one_mul, zero_sub, sub_zero,
              mul_zero, zero_add] <;> ring
        rw [show (((w : ℂ) + Complex.I * b₁) ^ 2).re
            = ((w : ℝ) - b₁.im) ^ 2 - b₁.re ^ 2 by
          rw [sq, Complex.mul_re, this.1, this.2]; ring]
        ring
      simp_rw [hnorm]
      exact (((gapsw80_t2_summable_1D_real (a := π / (t * a))
          (div_pos pi_pos (mul_pos ht ha)) (2 * (π / (t * a)) * b₁.im)).mul_left
        (rexp (-(π / (t * a)) * b₁.im ^ 2))).congr fun w => by
          rw [← Real.exp_add]; ring_nf).mul_right _

    have hbound : ∀ p : (Fin m → ℤ) × ℤ,
        ‖Fuw p‖ ≤ ‖cexp (-(π : ℂ) / ((t * a : ℝ) : ℂ)
            * ((p.2 : ℂ) + Complex.I * b₁) ^ 2)‖ * ∏ i, gU i (p.1 i) := fun p => by
      unfold Fuw
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      unfold thetaTerm
      rw [Complex.norm_exp,
        show (∏ i, gU i (p.1 i)) = rexp (∑ i,
          (-(π * t * c * (p.1 i : ℝ) ^ 2)
            + 2 * π * ((b' i).re - a⁻¹ * b₁.re * q₀ i) * (p.1 i : ℝ))) from
          (Real.exp_sum _ _).symm]
      apply Real.exp_le_exp.mpr
      have hre : (-(π : ℂ) * (t : ℂ) * (rQuad S (zcastR p.1) : ℂ)
            + 2 * π * ∑ i, (β' p.2) i * (p.1 i : ℂ)).re
          = -(π * t * rQuad S (zcastR p.1))
            + 2 * π * ∑ i, ((b' i).re - a⁻¹ * b₁.re * q₀ i) * (p.1 i : ℝ) := by
        have h1 : -(π : ℂ) * (t : ℂ) * (rQuad S (zcastR p.1) : ℂ)
            = (((-(π * t * rQuad S (zcastR p.1))) : ℝ) : ℂ) := by push_cast; ring
        have h2 : (2 : ℂ) * (π : ℂ) = (((2 * π) : ℝ) : ℂ) := by push_cast; ring
        rw [h1, h2, Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul,
          Complex.re_sum]
        congr 2
        exact Finset.sum_congr rfl fun i _ => by
          rw [Complex.mul_re, hReβ' p.2 i, Complex.intCast_re, Complex.intCast_im,
            mul_zero, sub_zero]
      rw [hre]
      have hxx : zcastR p.1 ⬝ᵥ zcastR p.1 = ∑ i, (p.1 i : ℝ) ^ 2 := by
        simp only [dotProduct, zcastR]
        exact Finset.sum_congr rfl fun i _ => (sq _).symm
      have hQv := hQ (zcastR p.1); rw [hxx] at hQv
      have hsplit : (∑ i, (-(π * t * c * (p.1 i : ℝ) ^ 2)
            + 2 * π * ((b' i).re - a⁻¹ * b₁.re * q₀ i) * (p.1 i : ℝ)))
          = -(π * t) * (c * ∑ i, (p.1 i : ℝ) ^ 2)
            + (2 * π) * ∑ i, ((b' i).re - a⁻¹ * b₁.re * q₀ i) * (p.1 i : ℝ) := by
        rw [Finset.sum_add_distrib]; congr 1
        · rw [← mul_assoc, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
        · rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      rw [hsplit]
      nlinarith [mul_pos pi_pos ht]
    exact (hUmaj.mul_of_nonneg hWmaj
        (fun u => Finset.prod_nonneg fun i _ => (Real.exp_pos _).le)
        (fun w => norm_nonneg _)).of_nonneg_of_le
      (fun p => norm_nonneg _)
      (fun p => by rw [mul_comm]; exact hbound p)

  have hdetM : M.det = a * S.det := by
    have hdD : ((a : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)).det = a := by
      rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, pow_one]
    rw [hMblock, Matrix.det_fromBlocks₂₂, hdD, hiD, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, ← Matrix.mul_smul]
  have hpref : (1 / (((t * a : ℝ) : ℂ)) ^ (1 / 2 : ℂ))
        * (((t ^ m * S.det : ℝ) : ℂ)) ^ (-(1 / 2) : ℂ)
      = (((t ^ (m + 1) * M.det : ℝ) : ℂ)) ^ (-(1 / 2) : ℂ) := by
    have hta : (0 : ℝ) < t * a := mul_pos ht ha
    have htmS : (0 : ℝ) < t ^ m * S.det := mul_pos (pow_pos ht m) hdetS
    rw [one_div, ← Complex.cpow_neg,
      show ((t ^ (m + 1) * M.det : ℝ) : ℂ)
        = ((t * a : ℝ) : ℂ) * ((t ^ m * S.det : ℝ) : ℂ) by
          push_cast; rw [hdetM]; push_cast; ring,
      ← Complex.mul_cpow_ofReal_nonneg hta.le htmS.le]

  set Pc : Matrix (Fin m) (Fin m) ℂ := P.map ((↑) : ℝ → ℂ)
  set qc : Matrix (Fin m) (Fin 1) ℂ := q.map ((↑) : ℝ → ℂ)
  have hqcT : qcᵀ = qᵀ.map ((↑) : ℝ → ℂ) := by
    ext i j; simp [qc, Matrix.transpose_apply, Matrix.map_apply]
  have hPcT : Pcᵀ = Pc := by
    ext i j; simp only [Pc, Matrix.transpose_apply, Matrix.map_apply]
    rw [← congrFun (congrFun hPT i) j, Matrix.transpose_apply]
  have hMc : (M.map ((↑) : ℝ → ℂ))
      = fromBlocks Pc qc qcᵀ ((a : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ)) := by
    rw [hMblock]; ext (i | i) (j | j) <;>
      simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.map_apply,
        Pc, qc, Matrix.smul_apply, Matrix.one_apply, Matrix.transpose_apply,
        apply_ite ((↑) : ℝ → ℂ)]

  haveI hMI : Invertible M :=
    Matrix.invertibleOfIsUnitDet M (isUnit_iff_ne_zero.mpr hM.det_pos.ne')
  have hMinvC : (M⁻¹).map ((↑) : ℝ → ℂ) = (M.map ((↑) : ℝ → ℂ))⁻¹ := by
    refine (Matrix.inv_eq_right_inv ?_).symm
    have h1 : M.map ((↑) : ℝ → ℂ) * (M⁻¹).map ((↑) : ℝ → ℂ)
        = (M * M⁻¹).map ((↑) : ℝ → ℂ) := by
      ext i j
      simp only [Matrix.map_apply, Matrix.mul_apply, Complex.ofReal_sum,
        Complex.ofReal_mul]
    rw [h1, ← Matrix.invOf_eq_nonsing_inv, mul_invOf_self]
    ext i j; simp [Matrix.map_apply, Matrix.one_apply, apply_ite ((↑) : ℝ → ℂ)]
  have hSinvC' : (S⁻¹).map ((↑) : ℝ → ℂ) = (S.map ((↑) : ℝ → ℂ))⁻¹ := by
    refine (Matrix.inv_eq_right_inv ?_).symm
    have h1 : S.map ((↑) : ℝ → ℂ) * (S⁻¹).map ((↑) : ℝ → ℂ)
        = (S * S⁻¹).map ((↑) : ℝ → ℂ) := by
      ext i j
      simp only [Matrix.map_apply, Matrix.mul_apply, Complex.ofReal_sum,
        Complex.ofReal_mul]
    rw [h1, ← Matrix.invOf_eq_nonsing_inv, mul_invOf_self]
    ext i j; simp [Matrix.map_apply, Matrix.one_apply, apply_ite ((↑) : ℝ → ℂ)]
  have hdetSc : (liftC S).det = ((S.det : ℝ) : ℂ) := by
    have := (RingHom.map_det Complex.ofRealHom S).symm
    simp [liftC, RingHom.mapMatrix_apply] at this
    exact this
  have hSc : liftC S = Pc - qc * ⅟(a : ℂ) • qcᵀ := by
    unfold liftC; rw [hS]
    ext i j
    simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.mul_apply, Pc, qc,
      Matrix.smul_apply, Matrix.transpose_apply, Fin.sum_univ_one, hiaC, hia,
      Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_inv, smul_eq_mul]
  haveI hScI : Invertible (Pc - qc * ⅟(a : ℂ) • qcᵀ) := by
    rw [← hSc]
    exact (liftC S).invertibleOfIsUnitDet
      (hdetSc ▸ isUnit_iff_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hdetS.ne'))
  have hSinvC : liftC S⁻¹ = (Pc - qc * ⅟(a : ℂ) • qcᵀ)⁻¹ := by
    have h1 : liftC S⁻¹ = (S⁻¹).map ((↑) : ℝ → ℂ) := rfl
    have h2 : S.map ((↑) : ℝ → ℂ) = liftC S := rfl
    rw [h1, hSinvC', h2, hSc]
  have hDualSplit : ∀ (w' : Fin m → ℤ) (w : ℤ),
      cexp (-(π : ℂ) / (t : ℂ)
          * ((fun i => ((Sum.elim w' (fun _ => w) : (Fin m ⊕ Fin 1) → ℤ) i : ℂ)
                + Complex.I * b i)
            ⬝ᵥ ((M⁻¹).map ((↑) : ℝ → ℂ)
              *ᵥ fun i => ((Sum.elim w' (fun _ => w) : (Fin m ⊕ Fin 1) → ℤ) i : ℂ)
                + Complex.I * b i)))
        = cexp (-(π : ℂ) / ((t * a : ℝ) : ℂ) * ((w : ℂ) + Complex.I * b₁) ^ 2)
          * dualTerm S t (β' w) w' := by
    intro w' w
    set X : Fin m → ℂ := fun i => (w' i : ℂ) + Complex.I * b' i
    set Y : ℂ := (w : ℂ) + Complex.I * b₁
    have hcast : (fun i => ((Sum.elim w' (fun _ => w) : (Fin m ⊕ Fin 1) → ℤ) i : ℂ)
          + Complex.I * b i)
        = Sum.elim X (fun _ => Y) := by
      funext i; cases i with
      | inl i => simp [X, b']
      | inr j => fin_cases j; simp [Y, b₁]
    rw [hcast, hMinvC, hMc,
      gapsw80_t2_bilin_schur_inv_scalar Pc qc (a : ℂ) hPcT X Y]
    unfold dualTerm cQuad
    rw [hSinvC, ← Complex.exp_add]
    congr 1
    have hXshift : (X - (⅟(a : ℂ) * Y) • fun i => qc i 0)
        = fun i => (w' i : ℂ) + Complex.I * (β' w) i := by
      funext i
      have hlhs : (X - (⅟(a : ℂ) * Y) • fun i => qc i 0) i
          = ((w' i : ℂ) + Complex.I * b' i)
            - (a : ℂ)⁻¹ * ((w : ℂ) + Complex.I * b₁) * (q₀ i : ℂ) := by
        simp only [X, Y, qc, Matrix.map_apply, Pi.sub_apply, Pi.smul_apply,
          smul_eq_mul, hiaC, q₀]
      have hrhs : (w' i : ℂ) + Complex.I * (β' w) i
          = ((w' i : ℂ) + Complex.I * b' i)
            - (a : ℂ)⁻¹ * ((w : ℂ) + Complex.I * b₁) * (q₀ i : ℂ) := by
        have hβ'i : (β' w) i
            = b' i + Complex.I * (a : ℂ)⁻¹ * ((w : ℂ) + Complex.I * b₁)
              * (q₀ i : ℂ) := rfl
        rw [hβ'i, mul_add,
          show Complex.I * (Complex.I * (a : ℂ)⁻¹
              * ((w : ℂ) + Complex.I * b₁) * (q₀ i : ℂ))
            = -((a : ℂ)⁻¹ * ((w : ℂ) + Complex.I * b₁) * (q₀ i : ℂ)) by
              rw [show Complex.I * (Complex.I * (a : ℂ)⁻¹
                    * ((w : ℂ) + Complex.I * b₁) * (q₀ i : ℂ))
                  = (Complex.I * Complex.I) * ((a : ℂ)⁻¹
                    * ((w : ℂ) + Complex.I * b₁) * (q₀ i : ℂ)) from by ring,
                Complex.I_mul_I]; ring]
        ring
      rw [hlhs, hrhs]
    rw [hXshift, hiaC]
    have hcoef2 : (-(π : ℂ) / ((t * a : ℝ) : ℂ))
        = (-(π : ℂ) / (t : ℂ)) * (a : ℂ)⁻¹ := by push_cast; field_simp
    rw [hcoef2, mul_add]
    ring

  set eF : Fin m ⊕ Fin 1 ≃ Fin (m + 1) := finSumFinEquiv
  have hA' : (Matrix.reindex eF eF M).PosDef := by
    refine (posDef_iff_dotProduct_mulVec).mpr ⟨?_, ?_⟩
    · show _ = _
      rw [Matrix.conjTranspose_eq_transpose_of_trivial]
      ext i j; simp [Matrix.reindex_apply, Matrix.submatrix_apply,
        ← congrFun (congrFun hMT (eF.symm i)) (eF.symm j), Matrix.transpose_apply]
    · intro x hx
      have hxe : (fun i => x (eF i)) ≠ 0 := fun h => hx (funext fun j => by
        have := congrFun h (eF.symm j); simpa using this)
      have key := (posDef_iff_dotProduct_mulVec.mp hM).2 hxe
      refine lt_of_lt_of_eq key ?_
      simp only [dotProduct, Matrix.mulVec, Matrix.reindex_apply,
        Matrix.submatrix_apply, star_trivial]
      refine Fintype.sum_equiv eF (fun i => x (eF i) * ∑ j, M i j * x (eF j))
        (fun i => x i * ∑ j, M (eF.symm i) (eF.symm j) * x j) fun i => ?_
      simp only [Equiv.symm_apply_apply]
      congr 1
      exact Fintype.sum_equiv eF (fun j => M i j * x (eF j))
        (fun j => M i (eF.symm j) * x j) fun j => by
          simp only [Equiv.symm_apply_apply]

  set ePi : (Fin (m + 1) → ℤ) ≃ ((Fin m ⊕ Fin 1) → ℤ) :=
    ⟨fun w => w ∘ eF, fun v => v ∘ eF.symm,
      fun w => funext fun j => congrArg w (eF.apply_symm_apply j),
      fun v => funext fun i => congrArg v (eF.symm_apply_apply i)⟩

  have hQeq : ∀ w : Fin (m + 1) → ℤ,
      rQuad (Matrix.reindex eF eF M) (zcastR w)
        = (fun i => ((ePi w) i : ℝ)) ⬝ᵥ (M *ᵥ fun i => ((ePi w) i : ℝ)) := fun w => by
    simp only [rQuad, zcastR, dotProduct, Matrix.mulVec, Matrix.reindex_apply,
      Matrix.submatrix_apply, ePi, Equiv.coe_fn_mk, Function.comp_apply]
    exact Fintype.sum_equiv eF.symm _ _ fun i => by
      simp only [Equiv.apply_symm_apply]
      exact congrArg _ (Fintype.sum_equiv eF.symm _ _ fun i' => by
        simp only [Equiv.apply_symm_apply])
  have hLeq : ∀ w : Fin (m + 1) → ℤ,
      (∑ j, (b ∘ eF.symm) j * (w j : ℂ)) = ∑ i, b i * ((ePi w) i : ℂ) := fun w =>
    Fintype.sum_equiv eF.symm _ _ fun j => by
      simp only [ePi, Equiv.coe_fn_mk, Function.comp_apply, Equiv.apply_symm_apply]

  let LB : ((Fin m ⊕ Fin 1) → ℤ) → ℂ := fun v =>
    cexp (-(π : ℂ) * t
        * (((fun i => (v i : ℝ)) ⬝ᵥ (M *ᵥ fun i => (v i : ℝ)) : ℝ) : ℂ)
      + 2 * π * ∑ i, b i * (v i : ℂ))
  let RB : ((Fin m ⊕ Fin 1) → ℤ) → ℂ := fun v =>
    cexp (-(π : ℂ) / t *
      ((fun i => (v i : ℂ) + Complex.I * b i) ⬝ᵥ
        ((M⁻¹).map ((↑) : ℝ → ℂ) *ᵥ fun i => (v i : ℂ) + Complex.I * b i)))
  have hLBsum : Summable LB := by
    refine (Equiv.summable_iff ePi).mp
      (((gapsw80_t2_summable_thetaTerm hA' ht (b ∘ eF.symm)).of_norm).congr fun w => ?_)
    show thetaTerm _ _ _ w = LB (ePi w)
    simp only [thetaTerm, LB, hQeq w, hLeq w]
  have hLHSsum : Summable fun p : (Fin m → ℤ) × ℤ => LB (e.symm p) :=
    (e.symm.summable_iff (f := LB)).mpr hLBsum

  have hRBsum : Summable RB := by
    refine (Equiv.summable_iff ePi).mp
      (((gapsw80_t2_summable_dualTerm hA' ht (b ∘ eF.symm)).of_norm).congr fun w => ?_)
    show dualTerm _ _ _ w = RB (ePi w)
    simp only [dualTerm, cQuad, liftC, RB, Matrix.inv_reindex]
    congr 2
    simp only [dotProduct, Matrix.mulVec, Matrix.reindex_apply,
      Matrix.submatrix_apply, Matrix.map_apply, ePi, Equiv.coe_fn_mk,
      Function.comp_apply]
    exact Fintype.sum_equiv eF.symm _ _ fun i => by
      simp only [Equiv.apply_symm_apply]
      exact congrArg₂ _ rfl (Fintype.sum_equiv eF.symm _ _ fun i' => by
        simp only [Equiv.apply_symm_apply])
  have hRHSsum : Summable fun p : (Fin m → ℤ) × ℤ => RB (e.symm p) :=
    (e.symm.summable_iff (f := RB)).mpr hRBsum

  have hLHSrw : ∀ p : (Fin m → ℤ) × ℤ,
      LB (e.symm p)
        = cexp (-(π : ℂ) * t * (rQuad S (zcastR p.1) : ℂ)
              + 2 * π * (∑ i, b' i * (p.1 i : ℂ))
            + (-(π : ℂ) * t * ((a * (a⁻¹ * q₀u p.1) ^ 2 : ℝ) : ℂ)))
          * cexp (-(π : ℂ) * ((t * a : ℝ) : ℂ) * (p.2 : ℂ) ^ 2
              + 2 * π * (β p.1) * (p.2 : ℂ)) := fun p => by
    show cexp _ = _
    rw [show e.symm p = Sum.elim p.1 (fun _ => p.2) from rfl,
      hQsplit p.1 p.2, hLsplit p.1 p.2, ← Complex.exp_add]
    congr 1; simp only [β]; push_cast; field_simp; ring

  have hFuwEq : ∀ p : (Fin m → ℤ) × ℤ,
      cexp (-(π : ℂ) * t * (rQuad S (zcastR p.1) : ℂ)
            + 2 * π * (∑ i, b' i * (p.1 i : ℂ))
          + (-(π : ℂ) * t * ((a * (a⁻¹ * q₀u p.1) ^ 2 : ℝ) : ℂ)))
        * cexp (-(π : ℂ) / ((t * a : ℝ) : ℂ) * ((p.2 : ℂ) + Complex.I * (β p.1)) ^ 2)
      = Fuw p := fun p => by
    unfold Fuw thetaTerm rQuad; rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    have key := hExpEq p.1 p.2
    linear_combination key

  have hR2'a : Summable Fuw := hR2'.of_norm
  have hFuwcomm : (∑' u, ∑' w, Fuw (u, w)) = ∑' w, ∑' u, Fuw (u, w) :=
    (Summable.tsum_comm (f := fun u w => Fuw (u, w))
      (show Summable (Function.uncurry fun u w => Fuw (u, w)) from hR2'a)).symm
  have hRHScomm : (∑' (w' : Fin m → ℤ), ∑' (w : ℤ), RB (e.symm (w', w)))
      = ∑' (w : ℤ), ∑' (w' : Fin m → ℤ), RB (e.symm (w', w)) :=
    (Summable.tsum_comm (f := fun w' w => RB (e.symm (w', w)))
      (show Summable (Function.uncurry fun w' w => RB (e.symm (w', w))) from
        hRHSsum)).symm
  show (∑' v, LB v) = (((t ^ (m + 1) * M.det : ℝ) : ℂ)) ^ (-(1 / 2) : ℂ) * ∑' w, RB w
  calc (∑' v, LB v)
      = ∑' p : (Fin m → ℤ) × ℤ, LB (e.symm p) := (e.symm.tsum_eq LB).symm
    _ = ∑' u : Fin m → ℤ, ∑' k : ℤ,
          cexp (-(π : ℂ) * t * (rQuad S (zcastR u) : ℂ)
                + 2 * π * (∑ i, b' i * (u i : ℂ))
              + (-(π : ℂ) * t * ((a * (a⁻¹ * q₀u u) ^ 2 : ℝ) : ℂ)))
            * cexp (-(π : ℂ) * ((t * a : ℝ) : ℂ) * (k : ℂ) ^ 2
                + 2 * π * (β u) * (k : ℂ)) := by
        rw [tsum_congr hLHSrw, (hLHSsum.congr hLHSrw).tsum_prod]
    _ = 1 / (((t * a : ℝ) : ℂ)) ^ (1 / 2 : ℂ)
          * ∑' u : Fin m → ℤ, ∑' w : ℤ, Fuw (u, w) := by
        rw [← tsum_mul_left]
        exact tsum_congr fun u => by
          rw [tsum_mul_left, h1D u, ← mul_assoc,
            mul_comm _ (1 / (((t * a : ℝ) : ℂ)) ^ (1 / 2 : ℂ)), mul_assoc,
            ← tsum_mul_left]
          exact congrArg _ (tsum_congr fun w => hFuwEq (u, w))
    _ = 1 / (((t * a : ℝ) : ℂ)) ^ (1 / 2 : ℂ)
          * ∑' w : ℤ, cexp (-(π : ℂ) / ((t * a : ℝ) : ℂ)
                * ((w : ℂ) + Complex.I * b₁) ^ 2)
              * ((((t ^ m * S.det : ℝ) : ℂ)) ^ (-(1 / 2) : ℂ)
                  * ∑' w', dualTerm S t (β' w) w') := by
        rw [hFuwcomm]
        exact congrArg _ (tsum_congr fun w => by
          simp only [Fuw]; rw [tsum_mul_left]
          exact congrArg _ (IH S hSpd ht (β' w)))
    _ = (((t ^ (m + 1) * M.det : ℝ) : ℂ)) ^ (-(1 / 2) : ℂ)
          * ∑' w : ℤ, ∑' w' : Fin m → ℤ, RB (e.symm (w', w)) := by
        have hperm : ∀ w : ℤ,
            cexp (-(π : ℂ) / ((t * a : ℝ) : ℂ) * ((w : ℂ) + Complex.I * b₁) ^ 2)
                * ((((t ^ m * S.det : ℝ) : ℂ)) ^ (-(1 / 2) : ℂ)
                    * ∑' w', dualTerm S t (β' w) w')
              = (((t ^ m * S.det : ℝ) : ℂ)) ^ (-(1 / 2) : ℂ)
                * ∑' w', RB (e.symm (w', w)) := fun w => by
          rw [← mul_assoc,
            mul_comm _ ((((t ^ m * S.det : ℝ) : ℂ)) ^ (-(1 / 2) : ℂ)), mul_assoc,
            ← tsum_mul_left]
          exact congrArg _ (tsum_congr fun w' => (hDualSplit w' w).symm)
        rw [tsum_congr hperm, tsum_mul_left, ← mul_assoc, hpref]
    _ = (((t ^ (m + 1) * M.det : ℝ) : ℂ)) ^ (-(1 / 2) : ℂ) * ∑' w, RB w := by
        rw [← hRHScomm, ← hRHSsum.tsum_prod, e.symm.tsum_eq]

end InductionStep

p2m_reactivate "P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT P2MW.S_NumberField_exists_completedDedekindZeta_package.FLT.Gapsw80T3IdealLatticeThetaTransformation"

theorem gapsw80_t2_poissonLaw_reindex {m : ℕ}
    (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (t : ℝ) (b : Fin (m + 1) → ℂ) :
    PoissonLaw A t b ↔
      PoissonLawBlock (reindex finSumFinEquiv.symm finSumFinEquiv.symm A) t
        (b ∘ finSumFinEquiv) := by
  set eF : Fin m ⊕ Fin 1 ≃ Fin (m + 1) := finSumFinEquiv
  set M := reindex eF.symm eF.symm A with hM
  set ePi : (Fin (m + 1) → ℤ) ≃ ((Fin m ⊕ Fin 1) → ℤ) :=
    ⟨fun w => w ∘ eF, fun v => v ∘ eF.symm,
      fun w => funext fun j => congrArg w (eF.apply_symm_apply j),
      fun v => funext fun i => congrArg v (eF.symm_apply_apply i)⟩
  have hMentry : ∀ i j, M i j = A (eF i) (eF j) := fun i j => by
    simp only [hM, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
  have hdet : M.det = A.det := Matrix.det_reindex_self _ _
  have hMinv : ∀ i j, M⁻¹ i j = A⁻¹ (eF i) (eF j) := fun i j => by
    rw [hM, Matrix.inv_reindex]
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm]
  have hQeq : ∀ v : Fin (m + 1) → ℤ,
      rQuad A (zcastR v)
        = (fun i => ((ePi v) i : ℝ)) ⬝ᵥ (M *ᵥ fun i => ((ePi v) i : ℝ)) := fun v => by
    simp only [rQuad, zcastR, dotProduct, Matrix.mulVec, ePi, Equiv.coe_fn_mk,
      Function.comp_apply, hMentry]
    exact (Fintype.sum_equiv eF _ _ fun i => by
      exact congrArg _ (Fintype.sum_equiv eF _ _ fun i' => rfl)).symm
  have hLeq : ∀ v : Fin (m + 1) → ℤ,
      (∑ j, b j * (v j : ℂ)) = ∑ i, (b ∘ eF) i * ((ePi v) i : ℂ) := fun v =>
    (Fintype.sum_equiv eF _ _ fun i => rfl).symm
  have hDeq : ∀ w : Fin (m + 1) → ℤ,
      cQuad (liftC A⁻¹) (fun j => (w j : ℂ) + Complex.I * b j)
        = (fun i => ((ePi w) i : ℂ) + Complex.I * (b ∘ eF) i)
          ⬝ᵥ ((M⁻¹).map ((↑) : ℝ → ℂ)
            *ᵥ fun i => ((ePi w) i : ℂ) + Complex.I * (b ∘ eF) i) := fun w => by
    simp only [cQuad, liftC, dotProduct, Matrix.mulVec, Matrix.map_apply, ePi,
      Equiv.coe_fn_mk, Function.comp_apply, hMinv]
    refine (Fintype.sum_equiv eF _ _ fun i => ?_).symm
    exact congrArg _ (Fintype.sum_equiv eF _ _ fun i' => rfl)
  have hLHSeq : (∑' v, thetaTerm A t b v)
      = ∑' x : (Fin m ⊕ Fin 1) → ℤ,
        cexp (-(π : ℂ) * t
            * (((fun i => (x i : ℝ)) ⬝ᵥ (M *ᵥ fun i => (x i : ℝ)) : ℝ) : ℂ)
          + 2 * π * ∑ i, (b ∘ eF) i * (x i : ℂ)) := by
    rw [← ePi.tsum_eq]
    exact tsum_congr fun v => by unfold thetaTerm; rw [hQeq v, hLeq v]
  have hRHSeq : (∑' w, dualTerm A t b w)
      = ∑' x : (Fin m ⊕ Fin 1) → ℤ,
        cexp (-(π : ℂ) / t
            * ((fun i => (x i : ℂ) + Complex.I * (b ∘ eF) i)
              ⬝ᵥ ((M⁻¹).map ((↑) : ℝ → ℂ)
                *ᵥ fun i => (x i : ℂ) + Complex.I * (b ∘ eF) i))) := by
    rw [← ePi.tsum_eq]
    exact tsum_congr fun w => by unfold dualTerm; rw [hDeq w]
  unfold PoissonLaw PoissonLawBlock
  rw [hLHSeq, hRHSeq, hdet]

theorem gapsw80_t2_rankNGaussianPoisson :
    ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ), A.PosDef →
      ∀ {t : ℝ}, 0 < t → ∀ b : Fin n → ℂ, PoissonLaw A t b := by
  intro n
  induction n with
  | zero =>
    intro A hA t ht b
    unfold PoissonLaw thetaTerm dualTerm rQuad cQuad
    simp only [dotProduct, Matrix.mulVec, Finset.univ_eq_empty, Finset.sum_empty,
      Complex.ofReal_zero, mul_zero, _root_.neg_zero, add_zero, Complex.exp_zero, pow_zero,
      one_mul, Matrix.det_fin_zero, Complex.ofReal_one, Complex.one_cpow]
  | succ m IH =>
    intro A hA t ht b
    rw [gapsw80_t2_poissonLaw_reindex]
    refine gapsw80_t2_poisson_step IH _ ?_ ht _
    have hAT : Aᵀ = A := by
      rw [← Matrix.conjTranspose_eq_transpose_of_trivial]; exact hA.1
    refine (posDef_iff_dotProduct_mulVec).mpr ⟨?_, ?_⟩
    · show _ = _
      rw [Matrix.conjTranspose_eq_transpose_of_trivial]
      ext i j
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.transpose_apply,
        Equiv.symm_symm,
        ← congrFun (congrFun hAT (finSumFinEquiv i)) (finSumFinEquiv j)]
    · intro x hx
      have hxe : (fun j => x (finSumFinEquiv.symm j)) ≠ 0 := fun h =>
        hx (funext fun i => by
          have := congrFun h (finSumFinEquiv i); simpa using this)
      have key := (posDef_iff_dotProduct_mulVec.mp hA).2 hxe
      refine lt_of_lt_of_eq key ?_
      simp only [dotProduct, Matrix.mulVec, Matrix.reindex_apply,
        Matrix.submatrix_apply, star_trivial, Equiv.symm_symm]
      refine Fintype.sum_equiv finSumFinEquiv.symm _ _ fun j => ?_
      simp only [Equiv.apply_symm_apply]
      exact congrArg _ (Fintype.sum_equiv finSumFinEquiv.symm _ _ fun j' => by
        simp only [Equiv.apply_symm_apply])

theorem gapsw80_t2_rankNGaussianPoisson_real
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) {t : ℝ} (ht : 0 < t) :
    (∑' v : Fin n → ℤ,
        cexp ((-(π * t * (zcastR v ⬝ᵥ A *ᵥ zcastR v)) : ℝ) : ℂ))
      = (((t ^ n * A.det) ^ (-(1/2) : ℝ) : ℝ) : ℂ) *
        ∑' w : Fin n → ℤ,
          cexp ((-(π * (zcastR w ⬝ᵥ A⁻¹ *ᵥ zcastR w) / t) : ℝ) : ℂ) := by
  have h := gapsw80_t2_rankNGaussianPoisson n A hA ht (fun _ => 0)
  have hpos : (0 : ℝ) < t ^ n * A.det := mul_pos (pow_pos ht n) hA.det_pos
  have hpref : (((t ^ n * A.det : ℝ) : ℂ)) ^ (-(1 / 2) : ℂ)
      = (((t ^ n * A.det) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) := by
    rw [show (-(1 / 2) : ℂ) = (((-(1 / 2) : ℝ)) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow hpos.le]
  have hθ0 : ∀ v, thetaTerm A t (fun _ => 0) v
      = cexp ((-(π * t * (zcastR v ⬝ᵥ A *ᵥ zcastR v)) : ℝ) : ℂ) := fun v => by
    unfold thetaTerm rQuad
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, mul_zero, add_zero]
    push_cast; ring_nf
  have hδ0 : ∀ w, dualTerm A t (fun _ => 0) w
      = cexp ((-(π * (zcastR w ⬝ᵥ A⁻¹ *ᵥ zcastR w) / t) : ℝ) : ℂ) := fun w => by
    unfold dualTerm cQuad liftC
    simp only [Pi.zero_apply, mul_zero, add_zero]
    congr 1
    have hQ : (fun i => (w i : ℂ)) ⬝ᵥ ((A⁻¹).map ((↑) : ℝ → ℂ) *ᵥ fun i => (w i : ℂ))
        = (((zcastR w ⬝ᵥ A⁻¹ *ᵥ zcastR w : ℝ)) : ℂ) := by
      simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, zcastR,
        Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_intCast]
    rw [hQ]; push_cast; ring
  unfold PoissonLaw at h
  rw [tsum_congr hθ0, tsum_congr hδ0, hpref] at h
  exact h

end
end Gapsw80T2RankNGaussianPoisson
end FLT
end
end
end P2MW.S_NumberField_exists_completedDedekindZeta_package
