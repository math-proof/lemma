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
import Abbrev.NumberTheory.NumberField.CompletedDedekindZeta.Package.Part5


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

theorem gapsw80_t8_hasFDerivAt_sq (σ : realSpace K) :
    HasFDerivAt (fun σ' : realSpace K => fun w => σ' w ^ 2) (gapsw80_t8_fderiv_sq K σ) σ := by
  simp only [hasFDerivAt_pi', ContinuousLinearMap.proj_pi]
  intro w
  have hd : HasDerivAt (fun x : ℝ => x ^ 2) (2 * σ w) (σ w) := by
    simpa using hasDerivAt_pow 2 (σ w)
  exact hd.hasFDerivAt.comp (f := fun σ' : realSpace K => σ' w) σ (hasFDerivAt_apply w σ)

open _root_.ContinuousLinearMap _root_.P2MW.S_NumberField_exists_completedDedekindZeta_package.ContinuousLinearMap in
theorem gapsw80_t8_abs_det_fderiv_sq (σ : realSpace K) :
    |(gapsw80_t8_fderiv_sq K σ).det|
      = 2 ^ (nrRealPlaces K + nrComplexPlaces K) * ∏ w : InfinitePlace K, |σ w| := by
  simp only [gapsw80_t8_fderiv_sq, ContinuousLinearMap.det, coe_pi]
  erw [LinearMap.det_pi]
  simp only [LinearMap.det_ring, ContinuousLinearMap.coe_coe, smulRight_apply,
    ContinuousLinearMap.one_apply, one_smul, Finset.abs_prod, abs_mul, abs_pow, abs_two,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    card_eq_nrRealPlaces_add_nrComplexPlaces]

theorem gapsw80_t8_setLIntegral_sq_pos {g : realSpace K → ENNReal} (hg : Measurable g) :
    ∫⁻ τ in {τ : realSpace K | ∀ w, 0 < τ w}, g τ
      = (2 : ENNReal) ^ (nrRealPlaces K + nrComplexPlaces K) *
        ∫⁻ σ in {σ : realSpace K | ∀ w, 0 < σ w},
          (∏ w : InfinitePlace K, ENNReal.ofReal (σ w)) * g (fun w => σ w ^ 2) := by
  set P : Set (realSpace K) := {σ | ∀ w, 0 < σ w}
  have hPmeas : MeasurableSet P := by
    rw [show P = Set.univ.pi fun _ => Set.Ioi (0:ℝ) from Set.ext fun σ => by
      simp [P, Set.mem_univ_pi]]
    exact MeasurableSet.univ_pi fun _ => measurableSet_Ioi
  have himg : (fun σ : realSpace K => fun w => σ w ^ 2) '' P = P := by
    refine Set.ext fun τ => ⟨fun ⟨σ, hσ, hστ⟩ w => hστ ▸ pow_pos (hσ w) 2, fun hτ => ?_⟩
    exact ⟨fun w => Real.sqrt (τ w), fun w => Real.sqrt_pos.mpr (hτ w),
      funext fun w => Real.sq_sqrt (hτ w).le⟩
  have hinj : Set.InjOn (fun σ : realSpace K => fun w => σ w ^ 2) P :=
    fun σ₁ h₁ σ₂ h₂ heq => funext fun w =>
      (pow_left_inj₀ (h₁ w).le (h₂ w).le two_ne_zero).mp (congrFun heq w)
  conv_lhs => rw [show P = (fun σ : realSpace K => fun w => σ w ^ 2) '' P from himg.symm]
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hPmeas
      (fun σ _ => (gapsw80_t8_hasFDerivAt_sq K σ).hasFDerivWithinAt) hinj g,
    ← lintegral_const_mul' _ _ (by finiteness)]
  refine setLIntegral_congr_fun hPmeas fun σ hσ => ?_
  rw [gapsw80_t8_abs_det_fderiv_sq, ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 2),
    show ENNReal.ofReal (2:ℝ) = (2:ENNReal) from by simp,
    ENNReal.ofReal_prod_of_nonneg fun w _ => abs_nonneg _,
    show (∏ w, ENNReal.ofReal |σ w|) = ∏ w, ENNReal.ofReal (σ w) from
      Finset.prod_congr rfl fun w _ => by rw [abs_of_pos (hσ w)],
    mul_assoc]

theorem gapsw80_t8_setLIntegral_placeParam_stepL
    {f : realSpace K → ENNReal} (hf : Measurable f) :
    ∫⁻ p in (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
        ENNReal.ofReal (p.1 ^ (nK K - 1)) * f (gapsw80_t8_placeParam K p)
      = (2 : ENNReal) * ∫⁻ c,
          ENNReal.ofReal (Real.exp (c w₀) ^ (2 * nK K)) * f (fun w => (expMapBasis c w) ^ 2) := by
  have hmeB : Measurable (fun c : realSpace K => expMapBasis c) :=
    (continuous_expMapBasis K).measurable
  have hmsq : Measurable (fun σ : realSpace K => fun w => σ w ^ 2) :=
    Measurable.of_eval fun w => (measurable_pi_apply w).pow_const 2
  set H : realSpace K → ENNReal := fun c =>
    ENNReal.ofReal (Real.exp (c w₀) ^ (2 * nK K)) * f (fun w => (expMapBasis c w) ^ 2) with hHdef
  have hH : Measurable H :=
    (ENNReal.measurable_ofReal.comp
        ((Real.measurable_exp.comp (measurable_pi_apply w₀)).pow_const _)).mul (hf.comp (hmsq.comp hmeB))
  rw [gapsw80_t8_setLIntegral_mkParam_halflog K hH,
    ← lintegral_const_mul' _ _ (by finiteness)]
  refine setLIntegral_congr_fun (measurableSet_Ioi.prod MeasurableSet.univ) fun p hp => ?_
  have ht : (0:ℝ) < p.1 := hp.1
  have hcw : gapsw80_t5_mkParam K (Real.log p.1 / 2) p.2 w₀ = Real.log p.1 / 2 := mkParam_w₀ K _ _
  have hplace : (fun w => (expMapBasis (gapsw80_t5_mkParam K (Real.log p.1 / 2) p.2) w) ^ 2)
      = gapsw80_t8_placeParam K p := funext fun w =>
    gapsw80_t7_yParam_mkParam_factor K ht p.2 w
  have hn : 1 ≤ nK K := Module.finrank_pos
  simp only [hHdef, hcw, hplace, exp_half_log_pow_two_n K ht]
  rw [show (2:ENNReal) = ENNReal.ofReal (2:ℝ) from by simp, ← mul_assoc, ← mul_assoc,
    ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
    ← ENNReal.ofReal_mul (by positivity),
    show (2:ℝ) * (2 * p.1)⁻¹ * p.1 ^ nK K = p.1 ^ (nK K - 1) by
      rw [show p.1 ^ nK K = p.1 * p.1 ^ (nK K - 1) by
        conv_lhs => rw [← Nat.sub_add_cancel hn, pow_succ']]
      field_simp]

theorem gapsw80_t8_setLIntegral_placeParam_hPaPc
    (c : realSpace K) :
    (∏ w, ENNReal.ofReal (expMapBasis c w))
        * (∏ w : {w // IsComplex w}, ENNReal.ofReal (expMapBasis c w.1))
      = ENNReal.ofReal (Real.exp (c w₀) ^ nK K) := by
  have heBpos : ∀ w, (0:ℝ) < expMapBasis c w := fun w => expMapBasis_pos c w
  rw [← ENNReal.ofReal_prod_of_nonneg (fun w _ => (heBpos w).le),
    ← ENNReal.ofReal_prod_of_nonneg (fun w _ => (heBpos w.1).le),
    ← ENNReal.ofReal_mul (Finset.prod_nonneg fun w _ => (heBpos w).le),
    prod_eq_prod_mul_prod (fun w => expMapBasis c w), mul_assoc, ← sq,
    ← prod_expMapBasis_pow c, prod_eq_prod_mul_prod (fun w => expMapBasis c w ^ w.mult)]
  congr 2
  · exact Finset.prod_congr rfl fun w _ => by rw [mult_isReal w, pow_one]
  · rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun w _ => by rw [mult_isComplex w]

theorem gapsw80_t8_setLIntegral_placeParam_stepR_point
    {f : realSpace K → ENNReal} (c : realSpace K) :
    ENNReal.ofReal (Real.exp (c w₀ * Module.finrank ℚ K)) *
        (∏ w : {w // IsComplex w}, ENNReal.ofReal (expMapBasis c w.1))⁻¹ *
        ((∏ w, ENNReal.ofReal (expMapBasis c w)) *
          ((∏ w : {w // IsComplex w}, ENNReal.ofReal (expMapBasis c w.1 ^ 2)) *
            f (fun w => expMapBasis c w ^ 2)))
      = ENNReal.ofReal (Real.exp (c w₀) ^ (2 * nK K)) * f (fun w => (expMapBasis c w) ^ 2) := by
  have heBpos : ∀ w, (0:ℝ) < expMapBasis c w := fun w => expMapBasis_pos c w
  have hPc0 : (∏ w : {w // IsComplex w}, ENNReal.ofReal (expMapBasis c w.1)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun w _ => (ENNReal.ofReal_pos.mpr (heBpos w.1)).ne'
  have hPcT : (∏ w : {w // IsComplex w}, ENNReal.ofReal (expMapBasis c w.1)) ≠ ⊤ :=
    (ENNReal.prod_lt_top fun w _ => ENNReal.ofReal_lt_top).ne
  have hPaPc := gapsw80_t8_setLIntegral_placeParam_hPaPc K c
  rw [show (c w₀) * (Module.finrank ℚ K : ℝ) = (nK K : ℝ) * c w₀ from mul_comm _ _,
    Real.exp_nat_mul,
    show (∏ w : {w // IsComplex w}, ENNReal.ofReal (expMapBasis c w.1 ^ 2))
        = (∏ w : {w // IsComplex w}, ENNReal.ofReal (expMapBasis c w.1))
          * (∏ w : {w // IsComplex w}, ENNReal.ofReal (expMapBasis c w.1)) from by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun w _ => by rw [sq, ENNReal.ofReal_mul (heBpos w.1).le],
    show Real.exp (c w₀) ^ (2 * nK K)
        = Real.exp (c w₀) ^ nK K * Real.exp (c w₀) ^ nK K from by rw [two_mul, pow_add],
    ENNReal.ofReal_mul (pow_nonneg (Real.exp_nonneg _) _)]
  rw [← mul_assoc _ _ (f _), ← mul_assoc (∏ w, ENNReal.ofReal (expMapBasis c w)),
    ← mul_assoc, ← mul_assoc]
  congr 1
  calc ENNReal.ofReal (Real.exp (c w₀) ^ nK K)
          * (∏ w : {w // IsComplex w}, ENNReal.ofReal (expMapBasis c w.1))⁻¹
          * ((∏ w, ENNReal.ofReal (expMapBasis c w))
            * (∏ w : {w // IsComplex w}, ENNReal.ofReal (expMapBasis c w.1)))
          * (∏ w : {w // IsComplex w}, ENNReal.ofReal (expMapBasis c w.1))
      = ENNReal.ofReal (Real.exp (c w₀) ^ nK K)
          * ((∏ w, ENNReal.ofReal (expMapBasis c w))
            * (∏ w : {w // IsComplex w}, ENNReal.ofReal (expMapBasis c w.1)))
          * ((∏ w : {w // IsComplex w}, ENNReal.ofReal (expMapBasis c w.1))⁻¹
            * (∏ w : {w // IsComplex w}, ENNReal.ofReal (expMapBasis c w.1))) := by ring
    _ = ENNReal.ofReal (Real.exp (c w₀) ^ nK K)
          * ENNReal.ofReal (Real.exp (c w₀) ^ nK K) := by
        rw [hPaPc, ENNReal.inv_mul_cancel hPc0 hPcT, mul_one]

theorem gapsw80_t8_setLIntegral_placeParam_stepR_meas
    {f : realSpace K → ENNReal} (hf : Measurable f) :
    Measurable (fun τ : realSpace K =>
      (∏ w : {w : InfinitePlace K // IsComplex w}, ENNReal.ofReal (τ w.1)) * f τ) :=
  (Finset.measurable_prod _ fun w _ =>
    ENNReal.measurable_ofReal.comp (measurable_pi_apply w.1)).mul hf

theorem gapsw80_t8_measurable_sq_pi :
    Measurable (fun σ : realSpace K => fun w => σ w ^ 2) :=
  Measurable.of_eval fun w => (measurable_pi_apply w).pow_const 2

theorem gapsw80_t8_setLIntegral_placeParam_stepR_hσ
    {f : realSpace K → ENNReal} (hf : Measurable f) :
    Measurable (fun σ : realSpace K =>
      (∏ w, ENNReal.ofReal (σ w)) *
        ((∏ w : {w // IsComplex w}, ENNReal.ofReal (σ w.1 ^ 2)) * f (fun w => σ w ^ 2))) := by
  fun_prop

set_option maxHeartbeats 999999 in
theorem gapsw80_t8_setLIntegral_placeParam_stepR_image
    {f : realSpace K → ENNReal} (hf : Measurable f) :
    ∫⁻ τ in {τ : realSpace K | ∀ w, 0 < τ w},
        (∏ w : {w : InfinitePlace K // IsComplex w}, ENNReal.ofReal (τ w.1)) * f τ
      = (2 : ENNReal) ^ (nrRealPlaces K + nrComplexPlaces K)
        * ((2 : ENNReal)⁻¹ ^ nrComplexPlaces K * ENNReal.ofReal (regulator K)
            * (nK K : ENNReal))
        * ∫⁻ c,
          ENNReal.ofReal (Real.exp (c w₀ * Module.finrank ℚ K)) *
            (∏ w : {w // IsComplex w}, ENNReal.ofReal (expMapBasis c w.1))⁻¹ *
            ((∏ w, ENNReal.ofReal (expMapBasis c w)) *
              ((∏ w : {w // IsComplex w}, ENNReal.ofReal (expMapBasis c w.1 ^ 2)) *
                f (fun w => expMapBasis c w ^ 2))) := by
  let hf' := gapsw80_t8_setLIntegral_placeParam_stepR_meas K hf
  let hσ := gapsw80_t8_setLIntegral_placeParam_stepR_hσ K hf
  rw [gapsw80_t8_setLIntegral_sq_pos K hf']
  rw [← gapsw80_t8_expMapBasis_image_univ K]
  rw [setLIntegral_expMapBasis_image MeasurableSet.univ hσ]
  rw [setLIntegral_univ, ← mul_assoc]

set_option maxHeartbeats 999999 in
theorem gapsw80_t8_setLIntegral_placeParam_stepR
    {f : realSpace K → ENNReal} (hf : Measurable f) :
    ∫⁻ τ in {τ : realSpace K | ∀ w, 0 < τ w},
        (∏ w : {w : InfinitePlace K // IsComplex w}, ENNReal.ofReal (τ w.1)) * f τ
      = (2 : ENNReal) ^ (nrRealPlaces K + nrComplexPlaces K)
        * ((2 : ENNReal)⁻¹ ^ nrComplexPlaces K * ENNReal.ofReal (regulator K) * (nK K : ENNReal))
        * ∫⁻ c,
          ENNReal.ofReal (Real.exp (c w₀) ^ (2 * nK K)) * f (fun w => (expMapBasis c w) ^ 2) := by
  rw [gapsw80_t8_setLIntegral_placeParam_stepR_image K hf]
  refine congrArg _ ?_
  exact lintegral_congr fun c => gapsw80_t8_setLIntegral_placeParam_stepR_point K (f := f) c

theorem gapsw80_t8_setLIntegral_placeParam_combine
    {f : realSpace K → ENNReal} (hf : Measurable f)
    (stepL : ∫⁻ p in (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
        ENNReal.ofReal (p.1 ^ (nK K - 1)) * f (gapsw80_t8_placeParam K p)
      = (2 : ENNReal) * ∫⁻ c,
          ENNReal.ofReal (Real.exp (c w₀) ^ (2 * nK K)) * f (fun w => (expMapBasis c w) ^ 2))
    (stepR : ∫⁻ τ in {τ : realSpace K | ∀ w, 0 < τ w},
        (∏ w : {w : InfinitePlace K // IsComplex w}, ENNReal.ofReal (τ w.1)) * f τ
      = (2 : ENNReal) ^ (nrRealPlaces K + nrComplexPlaces K)
        * ((2 : ENNReal)⁻¹ ^ nrComplexPlaces K * ENNReal.ofReal (regulator K) * (nK K : ENNReal))
        * ∫⁻ c,
          ENNReal.ofReal (Real.exp (c w₀) ^ (2 * nK K)) * f (fun w => (expMapBasis c w) ^ 2)) :
    ∫⁻ p in (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
        ENNReal.ofReal (p.1 ^ (nK K - 1)) * f (gapsw80_t8_placeParam K p)
      = ENNReal.ofReal ((2 : ℝ) ^ ((nrRealPlaces K : ℤ) - 1) * nK K * regulator K)⁻¹ *
        ∫⁻ τ in {τ : realSpace K | ∀ w, 0 < τ w},
          (∏ w : {w : InfinitePlace K // IsComplex w}, ENNReal.ofReal (τ w.1)) * f τ := by
  rw [stepL, stepR, ← mul_assoc]
  congr 1
  have hR : (0:ℝ) < regulator K := regulator_pos K
  have hn : 0 < nK K := Module.finrank_pos
  have hX : (0:ℝ) < (2:ℝ) ^ ((nrRealPlaces K : ℤ) - 1) * (nK K : ℝ) * regulator K :=
    mul_pos (mul_pos (zpow_pos two_pos _) (Nat.cast_pos.mpr hn)) hR
  have h2X : (2:ℝ) * ((2:ℝ) ^ ((nrRealPlaces K : ℤ) - 1) * (nK K : ℝ) * regulator K)
      = (2:ℝ) ^ nrRealPlaces K * (nK K : ℝ) * regulator K := by
    have key : (2:ℝ) ^ ((nrRealPlaces K : ℤ) - 1) * 2 = (2:ℝ) ^ nrRealPlaces K := by
      rw [← zpow_add_one₀ (two_ne_zero (α := ℝ)), sub_add_cancel, zpow_natCast]
    rw [← key]; ring
  have hB : (2:ENNReal) ^ (nrRealPlaces K + nrComplexPlaces K)
        * ((2:ENNReal)⁻¹ ^ nrComplexPlaces K * ENNReal.ofReal (regulator K) * (nK K : ENNReal))
      = ENNReal.ofReal ((2:ℝ) ^ nrRealPlaces K * (nK K : ℝ) * regulator K) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_natCast,
      show ENNReal.ofReal (2:ℝ) = (2:ENNReal) from by simp,
      pow_add, mul_assoc ((2:ENNReal) ^ nrRealPlaces K),
      show (2:ENNReal) ^ nrComplexPlaces K * ((2:ENNReal)⁻¹ ^ nrComplexPlaces K
            * ENNReal.ofReal (regulator K) * (nK K : ENNReal))
          = (nK K : ENNReal) * ENNReal.ofReal (regulator K)
            * ((2:ENNReal) * (2:ENNReal)⁻¹) ^ nrComplexPlaces K from by rw [mul_pow]; ring,
      ENNReal.mul_inv_cancel (by norm_num) (by simp), one_pow, mul_one, ← mul_assoc]
  rw [hB, ← h2X, ← ENNReal.ofReal_mul (inv_nonneg.mpr hX.le),
    show ((2:ℝ) ^ ((nrRealPlaces K : ℤ) - 1) * (nK K : ℝ) * regulator K)⁻¹
          * ((2:ℝ) * ((2:ℝ) ^ ((nrRealPlaces K : ℤ) - 1) * (nK K : ℝ) * regulator K))
        = (2:ℝ) from by field_simp,
    show ENNReal.ofReal (2:ℝ) = (2:ENNReal) from by simp]

theorem gapsw80_t8_setLIntegral_placeParam {f : realSpace K → ENNReal} (hf : Measurable f) :
    ∫⁻ p in (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
        ENNReal.ofReal (p.1 ^ (nK K - 1)) * f (gapsw80_t8_placeParam K p)
      = ENNReal.ofReal ((2 : ℝ) ^ ((nrRealPlaces K : ℤ) - 1) * nK K * regulator K)⁻¹ *
        ∫⁻ τ in {τ : realSpace K | ∀ w, 0 < τ w},
          (∏ w : {w : InfinitePlace K // IsComplex w}, ENNReal.ofReal (τ w.1)) * f τ :=
  gapsw80_t8_setLIntegral_placeParam_combine K hf
    (gapsw80_t8_setLIntegral_placeParam_stepL K hf)
    (gapsw80_t8_setLIntegral_placeParam_stepR K hf)

theorem gapsw80_t8_continuous_placeParam :
    Continuous (gapsw80_t8_placeParam K) :=
  continuous_pi fun w => continuous_fst.mul ((continuous_unitPart K w).comp continuous_snd)

theorem gapsw80_t8_placeParam_measure_eq :
    Measure.map (gapsw80_t8_placeParam K)
        ((volume.restrict ((Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)))).withDensity
          (fun p => ENNReal.ofReal (p.1 ^ (nK K - 1))))
      = ENNReal.ofReal ((2 : ℝ) ^ ((nrRealPlaces K : ℤ) - 1) * nK K * regulator K)⁻¹
        • (volume.restrict {τ : realSpace K | ∀ w, 0 < τ w}).withDensity
            (fun τ => ∏ w : {w : InfinitePlace K // IsComplex w}, ENNReal.ofReal (τ w.1)) := by
  have hφ : Measurable (gapsw80_t8_placeParam K) := (gapsw80_t8_continuous_placeParam K).measurable
  have hdL : Measurable (fun p : ℝ × logSpace K => ENNReal.ofReal (p.1 ^ (nK K - 1))) :=
    ENNReal.measurable_ofReal.comp (measurable_fst.pow_const _)
  have hdR : Measurable (fun τ : realSpace K =>
      ∏ w : {w : InfinitePlace K // IsComplex w}, ENNReal.ofReal (τ w.1)) :=
    Finset.measurable_prod _ fun w _ => ENNReal.measurable_ofReal.comp (measurable_pi_apply w.1)
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  have hgL : Measurable fun p => f (gapsw80_t8_placeParam K p) := hf.comp hφ
  rw [lintegral_map hf hφ, lintegral_withDensity_eq_lintegral_mul _ hdL hgL,
    lintegral_smul_measure, lintegral_withDensity_eq_lintegral_mul _ hdR hf, smul_eq_mul]
  simp only [Pi.mul_apply]
  exact gapsw80_t8_setLIntegral_placeParam K hf

theorem gapsw80_t8_setIntegral_placeParam {G : realSpace K → ℂ}
    (hG : AEStronglyMeasurable G (volume.restrict {τ : realSpace K | ∀ w, 0 < τ w})) :
    ∫ p in (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
        ((p.1 ^ (nK K - 1) : ℝ) : ℂ) * G (gapsw80_t8_placeParam K p)
      = (((2 : ℝ) ^ ((nrRealPlaces K : ℤ) - 1) * nK K * regulator K : ℝ)⁻¹ : ℂ) *
        ∫ τ in {τ : realSpace K | ∀ w, 0 < τ w},
          ((∏ w : {w : InfinitePlace K // IsComplex w}, τ w.1 : ℝ) : ℂ) * G τ := by
  have hC : (0:ℝ) ≤ ((2:ℝ) ^ ((nrRealPlaces K : ℤ) - 1) * nK K * regulator K)⁻¹ :=
    inv_nonneg.mpr (mul_nonneg
      (mul_nonneg (zpow_nonneg (by norm_num) _) (Nat.cast_nonneg _)) (regulator_pos K).le)
  have hBmeas : MeasurableSet {τ : realSpace K | ∀ w, 0 < τ w} := by
    rw [show {τ : realSpace K | ∀ w, 0 < τ w} = Set.univ.pi fun _ => Set.Ioi (0:ℝ) from
      Set.ext fun τ => by simp [Set.mem_univ_pi]]
    exact MeasurableSet.univ_pi fun _ => measurableSet_Ioi
  have hφ : Measurable (gapsw80_t8_placeParam K) := (gapsw80_t8_continuous_placeParam K).measurable
  have hdL : Measurable (fun p : ℝ × logSpace K => ENNReal.ofReal (p.1 ^ (nK K - 1))) :=
    ENNReal.measurable_ofReal.comp (measurable_fst.pow_const _)
  have hdR : Measurable (fun τ : realSpace K =>
      ∏ w : {w : InfinitePlace K // IsComplex w}, ENNReal.ofReal (τ w.1)) :=
    Finset.measurable_prod _ fun w _ => ENNReal.measurable_ofReal.comp (measurable_pi_apply w.1)

  have hGmap : AEStronglyMeasurable G (Measure.map (gapsw80_t8_placeParam K)
      ((volume.restrict ((Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)))).withDensity
        (fun p => ENNReal.ofReal (p.1 ^ (nK K - 1))))) := by
    rw [gapsw80_t8_placeParam_measure_eq]
    exact .mono_ac
      (Measure.smul_absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _)) hG

  have key := (integral_map hφ.aemeasurable hGmap).symm
  rw [gapsw80_t8_placeParam_measure_eq, integral_smul_measure,
    integral_withDensity_eq_integral_toReal_smul hdR
      (Filter.Eventually.of_forall fun _ => ENNReal.prod_lt_top fun _ _ => ENNReal.ofReal_lt_top),
    integral_withDensity_eq_integral_toReal_smul hdL
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    ENNReal.toReal_ofReal hC, Complex.real_smul] at key

  have stepL : (∫ p in (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
        ((p.1 ^ (nK K - 1) : ℝ) : ℂ) * G (gapsw80_t8_placeParam K p))
      = ∫ p in (Set.Ioi (0:ℝ)) ×ˢ (Set.univ : Set (logSpace K)),
        (ENNReal.ofReal (p.1 ^ (nK K - 1))).toReal • G (gapsw80_t8_placeParam K p) :=
    setIntegral_congr_fun (measurableSet_Ioi.prod MeasurableSet.univ) fun p hp => by
      rw [ENNReal.toReal_ofReal (pow_nonneg (le_of_lt hp.1) _), Complex.real_smul]
  have stepR : (∫ τ in {τ : realSpace K | ∀ w, 0 < τ w},
        (∏ w : {w : InfinitePlace K // IsComplex w}, ENNReal.ofReal (τ w.1)).toReal • G τ)
      = ∫ τ in {τ : realSpace K | ∀ w, 0 < τ w},
        ((∏ w : {w : InfinitePlace K // IsComplex w}, τ w.1 : ℝ) : ℂ) * G τ :=
    setIntegral_congr_fun hBmeas fun τ hτ => by
      rw [ENNReal.toReal_prod,
        show (∏ w : {w : InfinitePlace K // IsComplex w}, (ENNReal.ofReal (τ w.1)).toReal)
            = ∏ w : {w : InfinitePlace K // IsComplex w}, τ w.1 from
          Finset.prod_congr rfl fun w _ => ENNReal.toReal_ofReal (le_of_lt (hτ w.1)),
        Complex.real_smul]
  rw [stepL, key, stepR, Complex.ofReal_inv]

theorem gapsw80_t8_prod_gammaFactor_eq {s : ℂ} (hs : 1 < s.re) {x : mixedSpace K}
    (hx : ∀ w, normAtPlace w x ≠ 0) :
    ∏ w : InfinitePlace K,
        (((π * normAtPlace w x ^ 2 : ℝ) : ℂ) ^ (-(w.mult * s / 2)) * Complex.Gamma (w.mult * s / 2))
      = Gammaℝ s ^ nrRealPlaces K * (Gammaℂ s * (2:ℂ) ^ (s - 1)) ^ nrComplexPlaces K
        * ∏ w : InfinitePlace K, ((normAtPlace w x : ℝ) : ℂ) ^ (-(w.mult * s)) := by
  have hpos : ∀ w, 0 < normAtPlace w x := fun w =>
    (normAtPlace_nonneg w x).lt_of_ne (Ne.symm (hx w))

  have hreal : ∀ w : {w : InfinitePlace K // IsReal w},
      ((π * normAtPlace w.1 x ^ 2 : ℝ):ℂ) ^ (-((w.1.mult:ℂ) * s / 2))
        * Complex.Gamma ((w.1.mult:ℂ) * s / 2)
      = Gammaℝ s * ((normAtPlace w.1 x:ℝ):ℂ) ^ (-((w.1.mult:ℂ) * s)) := fun w => by
    simp only [mult_isReal w, Nat.cast_one, one_mul]
    rw [gapsw80_t8_gammaFactor_isReal (pow_pos (hpos w.1) 2) s, Complex.ofReal_pow,
      gapsw80_t8_ofReal_pow_cpow (hpos w.1).le 2 (-(s/2)),
      show ((2:ℕ):ℂ) * -(s/2) = -s from by push_cast; ring]

  have hcplx : ∀ w : {w : InfinitePlace K // IsComplex w},
      ((π * normAtPlace w.1 x ^ 2 : ℝ):ℂ) ^ (-((w.1.mult:ℂ) * s / 2))
        * Complex.Gamma ((w.1.mult:ℂ) * s / 2)
      = (Gammaℂ s * (2:ℂ)^(s-1)) * ((normAtPlace w.1 x:ℝ):ℂ) ^ (-((w.1.mult:ℂ) * s)) := fun w => by
    simp only [mult_isComplex w, Nat.cast_ofNat]
    rw [show ((2:ℂ) * s / 2) = s from by ring,
      gapsw80_t8_gammaFactor_isComplex (pow_pos (hpos w.1) 2) s, Complex.ofReal_pow,
      gapsw80_t8_ofReal_pow_cpow (hpos w.1).le 2 (-s),
      show ((2:ℕ):ℂ) * -s = -((2:ℂ)*s) from by push_cast; ring, mul_assoc]
  rw [prod_eq_prod_mul_prod (K := K), prod_eq_prod_mul_prod (K := K)
      (f := fun w => ((normAtPlace w x:ℝ):ℂ) ^ (-((w.mult:ℂ) * s)))]
  simp only [hreal, hcplx, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    nrRealPlaces, nrComplexPlaces]
  ring

theorem gapsw80_t8_prod_normAtPlace_cpow {x : mixedSpace K} (hx : ∀ w, normAtPlace w x ≠ 0)
    (s : ℂ) :
    ∏ w : InfinitePlace K, ((normAtPlace w x : ℝ) : ℂ) ^ (-(w.mult * s))
      = ((mixedEmbedding.norm x : ℝ) : ℂ) ^ (-s) := by
  rw [mixedEmbedding.norm_apply,
    gapsw80_t8_prod_ofReal_cpow Finset.univ
      (fun w _ => pow_nonneg (normAtPlace_nonneg w x) _) (-s)]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [Complex.ofReal_pow,
    gapsw80_t8_ofReal_pow_cpow (normAtPlace_nonneg w x) w.mult (-s)]
  congr 1; push_cast; ring

end Gapsw80T8MellinGammaPartialZeta
end FLT
end
end
end
end
end
end
end P2MW.S_NumberField_exists_completedDedekindZeta_package
