import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
import Lemma.Int.RothFinsuppL1_Single.eq.NatAbs
import Lemma.Finset.RothFinsuppL1_Sum.le.Sum_RothFinsuppL1
import Lemma.Fin.RothKroneckerEncode.eq.Add_Mul_RothKroneckerEncode
import Lemma.Fin.RothWeight_RothRidoutBoxComplement.eq.Sub_RothWeight.of.All_Gt_0.RothBox
import Lemma.Fin.CoeffCoeffRothLastEquiv.eq.CoeffRothLastIndex.of.RothMvIndex
import Lemma.Matrix.Mul_SubDiv1'2.le.RothWeightAndRothWeight.le.Sub_Mul_SubDiv1'2.of.Ne_0.RothBox.EqMulVecRothRidoutAuxMatrix_0.All_Gt_0.RothCoeff
import Lemma.Polynomial.Map_AlgebraMapRothLastSlice.eq.MulCCoeff.of.EqRothLastEquiv_MapAlgebraMap_MulC_MapAlgebraMapMapC.RothMvIndex
import Lemma.MvPolynomial.RothKronecker.eq.Monomial
import Lemma.Fin.RothMvHasse_RothMvHasse.eq.SMul_RothMvHasse.of.RothMvIndex
import Lemma.Fin.CardRothLowIndex.Gt_0.of.Lt_Div1'2.Gt_0.Gt_0
import Lemma.Fin.Sum_SquareRothCenteredSum.le.DivMul_CardRothBox4.of.All_Gt_0
import Lemma.Fin.RothDegreeBound_Sum.of.All_RothDegreeBound
import Lemma.MvPolynomial.EvalAlgebraMap.eq.Eval_AlgebraMapFun
import Lemma.Fin.RothMvHasse_Single1.eq.Pderiv
import Lemma.Fin.Eval_0RothMvHasse.eq.Coeff.of.RothMvIndex
import Lemma.Nat.MulChooseS
import Lemma.Fin.MulMulMul4SquareCardRothLowIndices.le.CardRothBox.of.Gt_0.Gt_0.All_Gt_0
import Lemma.Fin.Any_And_Det_RothMvHasse.ne.Zero.of.All_RothKroneckerBounded.LinearIndependent.Gt_1
import Lemma.Real.Rpow.le.Prod_MulPowSRpow.of.All_Le.All_Le_PowDen.Ge_0.Ge_0.All_Gt_0.Gt_0.RothMvIndex
import Lemma.Fin.Any_All_Eq_RothRidoutExponentAndAll_All_Le_RothRidoutExponentAndDvdProd_PowRothClearEval.of.All_DvdProd_Pow_Den.All_DvdProd_PowNum.NonemptySupport
import Lemma.Fin.RothMvHasse0.eq.Zero.of.RothMvIndex
import Lemma.Fin.EqRothLastTail.of.RothMvIndexAdd_1
import Lemma.Fin.RothZeroBox.in.RothLowIndices.of.Lt_Div1'2.Gt_0
import Lemma.Fin.RothMvVanishesBelow.of.Le_0
import Lemma.Polynomial.LtDegreeMulC.of.LtDegree
import Lemma.Finset.Prod_Pow_RothRidoutExponent.dvd.Prod_MulPowNumPowDenSub.of.RothMvIndex.All_DvdProd_Pow_Den.All_DvdProd_PowNum
import Lemma.Fin.Pow_RothRidoutExponent.eq.Prod_MulPowPowPowPowSub.of.RothMvIndex
import Lemma.Fin.RothMvL1'1.eq.One
import Lemma.MvPolynomial.Eval.eq.RothHasseEval.of.RothBox.RothCoeff
import Lemma.Fin.NatAbsCoeff.le.RothMvL1.of.RothMvIndex
import Lemma.MvPolynomial.All_EqRothTranslateC
import Lemma.Nat.RothMvOrderAdd.eq.AddRothSMvOrder.of.RothMvIndex
import Lemma.Real.FiniteSetOfLtAbsSub_Div1RpowDenAndLeDen.of.Gt_0
import Lemma.Fin.SquareRothCentered.le.Div1'4.of.RothBox.All_Gt_0
import Lemma.Fin.RothMvL1.le.MulPowS
import Lemma.Polynomial.Any_Eq_SMul.of.EqWronskian_0.Ne_0
import Lemma.Fin.GetRothFlip.eq.Sub.of.RothBox
import Lemma.Rat.NatDegreeRothIntPolynomial.Gt_0.of.IsAlgebraic
import Lemma.Fin.EqRothMvOrder_Single
import Lemma.Fin.RothLastEquiv_Map.eq.Map_MapRothLastEquiv
import Lemma.Fin.RothMvOrderAdd_Single1.eq.AddRothMvOrder1.of.RothMvIndex
import Lemma.Polynomial.LeDiv.of.LeNatAbsLeadingCoeffRpow_DenMul.Gt_0.GeDen_2.Ne_0
import Lemma.Real.LiouvilleWith.of.InfiniteSetOfLtAbsSub_Div1RpowDen.Gt_0.Irrational
import Lemma.Nat.EqEquivMapDomain_EquivMapDomainSymm
import Lemma.Fin.RothMvVanishesBelow.of.All_RothMvVanishesBelow
import Lemma.Fin.LeNatDegreeRothLastEquiv
import Lemma.Polynomial.RothLastEquiv.eq.Sum_MulCMap.of.RothMvIndex.Eq_Sum_MulCMapC
import Lemma.Fin.RothMvVanishesBelow
import Lemma.Submodule.RothPolyWronskianRow.in.Span_XRothPolyJetRows1
import Lemma.Fin.RothRidoutAuxMatrix_CastSuccLastNatDegreeRothIntegralPolynomial.eq.Eq_1.of.RothBox
import Lemma.Fin.MapRothHasseDet.eq.RothHasseDet_Map
import Lemma.Polynomial.RothPolyL1_RothPowerCoordAdd_1.le.MulAddRothPolyL1'1RothPolyL1_RothPowerCoord
import Lemma.Polynomial.Eval.eq.PowMulLeadingCoeffRothIntPolynomial.of.IsAlgebraic
import Lemma.Fin.RothDegreeBound.of.All_RothDegreeBound
import Lemma.Fin.LeNatDegreeRothLastSlice.of.RothMvIndex
import Lemma.Fin.MulRothDenProductEvalAlgebraMap.eq.RothClearEval
import Lemma.Fin.Any_And_Det_RothMvHasse.ne.Zero.of.All_RothDegreeBoundOver.LinearIndependent
import Lemma.Fin.RothMvWeight_Mul.eq.DivRothMvWeight.of.All_Gt_0.Gt_0.RothMvIndex
import Lemma.Fin.Pderiv.eq.SMul.of.RothMvIndex
import Lemma.Nat.Factorial.le.Pow2Mul.of.Gt_0
import Lemma.Fin.EqCoeffRothMvOfCoeffRothBoxIndex.of.RothBox.RothCoeff
import Lemma.Real.Prod_PowAbsSub.le.RpowMulNegRothMvWeight.of.All_LeAbsSub_RpowDivNeg.Gt_0
import Lemma.Polynomial.RothPolyWronskianDerivativeRow0.eq.Zero
import Lemma.Int.RothFinsuppL1_Sub.le.AddRothSFinsuppL1
import Lemma.Fin.RothDegreeBoundNeg
import Lemma.Rat.RothIntPolynomial.ne.Zero.of.IsAlgebraic
import Lemma.Fin.RothDegreeBound
import Lemma.Matrix.Eq_0.of.EqMulVecRothRidoutAuxMatrix_0.RothCoeff
import Lemma.Real.Prod_MulPowRpowDenPowRpowDenSub.le.Pow_RothRidoutExponent.of.All_LeRpowDenPow.All_LeRpowDenPow.RothMvIndex
import Lemma.Polynomial.LinearIndependent_J.of.LinearIndependent
import Lemma.MvPolynomial.CoeffGetFinSuccEquivRothMvHasse_Cons.eq.RothMvHasse_CoeffHasseDerivGetFinSuccEquiv
import Lemma.Submodule.DetUpdateRow.ne.Zero.of.In_Span.NeDet_0
import Lemma.MvPolynomial.CoeffRothTranslate_Eval_C.eq.Sum_MulCoeffRothTranslate_CoeffPow.of.RothMvIndex
import Lemma.Polynomial.Eval.eq.MulPowLeadingCoeffRothIntPolynomialSumRothHasseEval.of.RothCoeff.RothBox.IsAlgebraic
import Lemma.Fin.RothTermDegree.le.Sum.of.RothBox
import Lemma.Polynomial.NatAbsCoeff.le.RothPolyL1
import Lemma.Fin.Nonempty_RothIntegralFactorData.of.RothDeterminantData
import Lemma.Matrix.MulVecRothAuxMatrix.eq.Zero.of.EqMulVecRothRidoutAuxMatrix_0.RothCoeff
import Lemma.Fin.RothMvWeight_RothRidoutComplement.eq.Sub_RothMvWeight.of.All_Le.All_Gt_0.RothMvIndex
import Lemma.MvPolynomial.RothMvL1_Monomial.eq.NatAbs.of.RothMvIndex
import Lemma.Polynomial.RothPolyJetRows.sub.RothPolyJetRows.of.Le
import Lemma.MvPolynomial.Eval_LastCases.eq.Eval_Map_EvalRothLastEquiv
import Lemma.MvPolynomial.DerivativeRothKronecker.eq.Sum_MulMulCPowPowXSubPow1RothKronecker_Pderiv
import Lemma.Submodule.RothPolyWronskianDerivativeRow.in.Span_XRothPolyJetRowsAdd_1
import Lemma.Rat.MonicRothIntegralPolynomial.of.IsAlgebraic
import Lemma.Fin.RothDegreeBoundSMul
import Lemma.Fin.RothMvHasseAdd.eq.AddRothSMvHasse.of.RothMvIndex
import Lemma.Fin.RothMvL1_Sub.le.AddRothSMvL1
import Lemma.Fin.LinearIndependent_RothKronecker.of.All_RothKroneckerBounded.LinearIndependent.Gt_1
import Lemma.Fin.RothPolyL1_RothAuxTerm.le.PowMul2RothCoordinateBaseSum.of.RothBox
import Lemma.MvPolynomial.CoeffRothTranslate
import Lemma.Fin.RothMvVanishesBelow.of.All_LeRothMvWeight
import Lemma.Fin.RothMvL1_RothMvHasse.le.MulPow2SumRothMvL1.of.RothMvIndex
import Lemma.Polynomial.Eval_AlgebraMapMulLeadingCoeffRothIntPolynomialRothIntegralPolynomial.eq.Zero.of.IsAlgebraic
import Lemma.Polynomial.Eval.eq.MulMulProd_ChoosePowLeadingCoeffRothIntPolynomialSumPow_RothTermDegree.of.RothBox.IsAlgebraic
import Lemma.Polynomial.RothPolyL1X.eq.One
import Lemma.Fin.RothMvOfCoeff.ne.Zero.of.Ne_0
import Lemma.Fin.RothKronHasseJetRows.sub.RothKronHasseJetRows.of.Le
import Lemma.Fin.RothMvVanishesBelow_Sum.of.All_RothMvVanishesBelow
import Lemma.Fin.RothMvL1_Sum.le.Sum_RothMvL1
import Lemma.Real.RothPolyL1_RothScaledPowerCoord.le.PowRothCoordinateBase.of.Le
import Lemma.Real.RpowMul.le.RpowMul.of.LePow_Pow.Ge_0
import Lemma.Polynomial.RothPolyL1Mul.le.MulRothSPolyL1
import Lemma.Fin.Sub.le.RothMvWeightAndLe_RothMvWeight_RothRidoutComplement.of.In_SupportRothMvHasse_RothMvOfCoeff.LeRothMvWeight.RothMvIndex.All_Le_RothWeightAndLeRothWeight_Sub.RothCoeff.All_Gt_0
import Lemma.Fin.RothMvVanishesBelow.of.Le
import Lemma.Fin.RothKroneckerBounded_Sum.of.All_RothKroneckerBounded
import Lemma.Fin.RothPolyL1.le.MulAdd_1RothMvL1.of.RothMvIndex
import Lemma.Polynomial.Det_HasseDerivVal.ne.Zero.of.LinearIndependent
import Lemma.Finset.RothFinsuppL1.eq.Sum_NatAbs.of.SubsetSupport
import Lemma.Fin.CardRothBox.eq.Prod_Add_1
import Lemma.Fin.RothMvL1_RothHasseDet.le.MulFactorialPowMulPow2SumRothMvL1
import Lemma.Fin.CardRothBox.le.Pow2Sum.of.All_Gt_0
import Lemma.Fin.MapRothMvHasse.eq.RothMvHasse_Map.of.RothMvIndex
import Lemma.Fin.Nonempty_RothDeterminantData.of.Ne_0
import Lemma.Finset.Prod_Pow_RothRidoutExponent.eq.Prod_MulPowProd_PowPowProd_PowSub.of.RothMvIndex
import Lemma.Fin.RothHasseEval0.eq.RothEval.of.RothCoeff
import Lemma.Fin.Sum_MulRothSCentered.eq.Zero.of.Ne.All_Gt_0
import Lemma.Fin.Mul2CardRothLowIndex.le.CardRothBox.of.Le_MulMul2Square.Gt_0.Gt_0.All_Gt_0
import Lemma.Int.RothFinsuppL1Neg.eq.RothFinsuppL1
import Lemma.MvPolynomial.RothMvHasse.eq.Monomial.of.RothMvIndex
import Lemma.Fin.RothCentered_RothFlip.eq.NegRothCentered.of.RothBox.All_Gt_0
import Lemma.Fin.EqRothLastIndex_Last.of.RothMvIndex
import Lemma.Fin.RothMvL1_CoeffRothLastEquiv.le.RothMvL1
import Lemma.Fin.InvolutiveRothRidoutBoxComplement
import Lemma.Fin.RothMvL1Add.le.AddRothSMvL1
import Lemma.MvPolynomial.Eval_AlgebraMapRothMvHasse_RothMvOfCoeff.eq.RothHasseEval.of.RothMvIndex.RothCoeff
import Lemma.Set.FiniteSetOfLeAbsQAndLeDen
import Lemma.Real.RpowDivMul.le.PowRpow.of.Le_Pow.Ge_0.Gt_0.Gt_0.Gt_0
import Lemma.Submodule.RothPolyRowDerivative.in.Span_XRothKronHasseJetRowsAdd_1.of.In_Span_XRothKronHasseJetRows
import Lemma.MvPolynomial.RothMvVanishesBelow_Map_AlgebraMapRothMvOfCoeff
import Lemma.Submodule.RothPolyRowDerivative.in.Span_XRothPolyJetRowsAdd_1.of.In_Span_XRothPolyJetRows
import Lemma.Polynomial.RothPolyL1_RothPowerCoord.le.PowAddRothPolyL1'1
import Lemma.MvPolynomial.RothMvVanishesBelow_MapAlgebraMap.of.All_EqEval_AlgebraMapFunRothMvHasse_0
import Lemma.Polynomial.IsPrimitiveSubMulCDenXCNum
import Lemma.Polynomial.Any_LtDivAndNeEvalHasseDeriv_MapAlgebraMap_0.of.Le_Rpow.Ne_0.GeDen_2.Gt_0.Gt_0
import Lemma.Polynomial.RothPolyL1.eq.Sum_NatAbsCoeff
import Lemma.Real.RpowMulAddSub.le.Pow_RothRidoutExponent.of.In_SupportRothMvHasse_RothMvOfCoeff.LeRothMvWeight.All_Le_RothWeightAndLeRothWeight_Sub.All_LeRpowDenPow.All_LeRpowDenPow.All_Le_PowDen.Ge_0.Ge_0.Ge_0.Gt_1.All_Gt_0.RothMvIndex.RothCoeff
import Lemma.Fin.EqRothMvHasse0
import Lemma.Fin.InjectiveRothBoxIndex
import Lemma.Fin.RothMvWeight.ge.Zero.of.RothMvIndex
import Lemma.Matrix.RothHasseEval_1.eq.Zero.of.EqMulVecRothAuxMatrix_0.RothCoeff.IsAlgebraic
import Lemma.Fin.RothRidoutComplement.eq.Sub.of.RothMvIndex
import Lemma.Fin.DegreeRothAuxTerm.lt.NatDegreeRothIntegralPolynomial.of.RothBox.IsAlgebraic
import Lemma.Rat.NatDegreeRothIntegralPolynomial.Gt_0.of.IsAlgebraic
import Lemma.Nat.Add_1.le.Pow2.of.Gt_0
import Lemma.Fin.RothMvVanishesBelowAdd
import Lemma.Polynomial.Eval.of.RothMvIndex
import Lemma.Polynomial.DvdPowSubMulCDenXCNum
import Lemma.Fin.CoeffRothLastSlice.eq.CoeffRothLastIndex.of.RothMvIndex
import Lemma.Polynomial.EvalRothPowerCoord.eq.Pow.of.EqEval_0
import Lemma.Real.NormRothRidoutAuxMatrix.le.PowMul_2RothCoordinateBaseSum
import Lemma.Fin.RothMvL1.Gt_0.of.Ne_0
import Lemma.Fin.Any_LtRothMvWeightAndNeEvalRothMvHasse_0.of.NotRothMvVanishesBelow
import Lemma.Fin.GetRothRidoutBoxComplement.eq.Sub.of.RothBox
import Lemma.Fin.RothMvHasse.eq.SMul.of.RothMvIndex
import Lemma.Polynomial.Det_PowDerivativeGetVal.ne.Zero.of.LinearIndependent
import Lemma.Polynomial.PowDen.le.NatAbsLeadingCoeff.of.Ne_0
import Lemma.Fin.EqRothFlip.of.RothBox.Ne
import Lemma.Fin.AbsEval.le.MulRothMvL1Prod_PowMax
import Lemma.Fin.RothWeight.eq.AddRothCenteredSumDiv_2.of.RothBox
import Lemma.Fin.NatAbsRothAuxMatrix.le.PowMul2RothCoordinateBaseSum.of.RothBox
import Lemma.Fin.RothCentered_RothFlip.eq.RothCentered.of.RothBox.Ne
import Lemma.Fin.EqRothLastIndexCastSucc.of.RothMvIndex
import Lemma.Fin.RothMvL1_RothMvOfCoeff.le.Sum_NatAbs.of.RothCoeff
import Lemma.Fin.RothRidoutAuxMatrix_CastSuccCastSucc.eq.RothAuxMatrix.of.RothBox.RothLowIndex
import Lemma.Polynomial.Eval.eq.MulPowS.of.Le.IsAlgebraic
import Lemma.Fin.RothPolyL1.le.MulPow2AddAddMulKMulKSMulKSumPowRothMvL1K.of.Gt_0
import Lemma.Polynomial.RothPolyL1Add.le.AddRothSPolyL1
import Lemma.Submodule.Any_And_All_In.of.All_In_Span.NeDet_0
import Lemma.Polynomial.RothPolyL1_Sub.le.AddRothSPolyL1
import Lemma.Nat.Injective_I
import Lemma.Fin.RothMvVanishesBelow_Sub
import Lemma.Polynomial.RothPolyL1_C.eq.NatAbs
import Lemma.Fin.RothDegreeBound_RothMvOfCoeff.of.RothCoeff
import Lemma.Fin.RothKronecker.ne.Zero.of.Ne_0.Gt_1
import Lemma.Fin.RothDegreeBoundAdd
import Lemma.Real.FiniteSetOfLtAbsSub_Div1RpowDen.of.NotLiouvilleWith.Gt_0.Irrational
import Lemma.Fin.RothDegreeBoundOver_RothMvHasse.of.RothMvIndex
import Lemma.Int.RothFinsuppL1CoeffMul.le.MulRothSFinsuppL1Coeff
import Lemma.Fin.EqRothLastIndex.of.RothMvIndexAdd_1
import Lemma.Fin.Ne_0AndRothVanishesBelowAndMul_SubDiv1'2.le.RothWeightAndRothWeight.le.Sub_Mul_SubDiv1'2AndRothMvL1.le.PowMul8RothCoordinateBaseSum.of.LeAddNatDegreeRothIntegralPolynomial2MulMul2Square.LtAddNatDegreeRothIntegralPolynomial2MulMul4Square.Lt_Div1'2.Gt_0.Gt_0.All_Gt_0.IsAlgebraic
import Lemma.Fin.EqRothBoxIndex.of.RothBox
import Lemma.Fin.RothMvVanishesBelowNeg
import Lemma.Fin.RothKronecker.eq.Sum_Monomial
import Lemma.Fin.RothMvL1Mul.le.MulRothSMvL1
import Lemma.MvPolynomial.AbsCoeffRothTranslate.le.MulMulPow4SumRothMvL1Prod_PowMax.of.RothMvIndex
import Lemma.Fin.RothMvL1Det.le.MulFactorialPow.of.All_LeRothMvL1
import Lemma.Polynomial.IsPrimitivePow.of.IsPrimitive
import Lemma.Polynomial.Eval_LastCasesRothMvHasse_RothLastIndex.eq.MulEvalRothMvHasseEvalHasseDeriv.of.RothMvIndex.EqRothLastEquiv_MulCMapC
import Lemma.Fin.CoeffRothAuxCombination.eq.Sum_MulCoeffRothAuxTerm.of.RothCoeff.RothBox
import Lemma.Fin.RothMvL1_Prod.le.Prod_RothMvL1
import Lemma.Polynomial.RothLastEquiv.eq.MulCMap.of.EqRothLastEquiv_Sum_MulCMapC
import Lemma.Real.AbsEval.le.MulMulMulPow8SumRothMvL1Prod_PowMaxRpow.of.All_LeProd_PowAbsSub_RpowMulNegRothMvWeight.Ge_1.Ge_0.RothMvIndex.All_Gt_0
import Lemma.Int.RothFinsuppL1Add.le.AddRothSFinsuppL1
import Lemma.Fin.RothMvL1Neg.eq.RothMvL1
import Lemma.Polynomial.RothPolyRowDerivative_RothPolyDerivativeRow.eq.RothPolyDerivativeRowAdd_1
import Lemma.Fin.RothMvWeight.le.DivRothMvOrder.of.All_Le.Gt_0.RothMvIndex
import Lemma.Fin.RothMvWeight.eq.AddRothMvWeightDiv.of.RothMvIndex
import Lemma.Real.RpowMulSum_AddSub.le.Prod_Pow.of.All_Any_Eq_RothRidoutExponent.LeRothMvWeight.All_Le_RothWeightAndLeRothWeight_Sub.All_LeRpowDenPow.All_LeRpowDenPow.All_Le_PowDen.All_Ge_0.All_Ge_0.Ge_0.Gt_1.All_Gt_0.RothMvIndex.RothCoeff
import Lemma.Polynomial.DegreeRothPowerCoord.lt.NatDegree.of.GtNatDegree_0.Monic
import Lemma.Polynomial.CoeffRothLastEquiv_RothMvHasse_RothLastIndex.eq.RothMvHasse_CoeffHasseDerivRothLastEquiv.of.RothMvIndex
import Lemma.Fin.RothMvL1.eq.Sum_NatAbsCoeff
import Lemma.Fin.RothMvVanishesBelow_MulDiv.of.All_Gt_0.Gt_0
import Lemma.Fin.RothDegreeBound_ProdMulCard.of.All_RothDegreeBound
import Lemma.Fin.RothMvVanishesBelow_Max
import Lemma.Fin.CoeffRothMvHasse.eq.MulProd_ChooseExtAddCoeffAdd.of.RothMvIndex
import Lemma.Polynomial.Any_And_Le_AddNatDegree1AndAll_Eq_CoeffAndAll_LeNatDegreeAndLinearIndependentAndLinearIndependentAndEq_Sum_MulCMap.of.Ne_0
import Lemma.Matrix.RothAuxCombination1.eq.Zero.of.EqMulVecRothAuxMatrix_0.RothCoeff.IsAlgebraic
import Lemma.Fin.AddMul_RothMvWeightMul_RothMvWeight_RothRidoutComplement.eq.Sum_AddDivMulDivMul_Sub.of.All_Le.RothMvIndex
import Lemma.Fin.RothDegreeBoundOver
import Lemma.Fin.CoeffRothTranslateM.eq.EvalRothMvHasse
import Lemma.Real.MulPowS.le.RpowMulMulAdd_Mul.of.Le_MulMul.Le_RpowMul.Le_Rpow.Ge_0.Ge
import Lemma.Fin.RothLastSlice0.ne.Zero.of.Ne_0
import Lemma.Fin.RothMvVanishesBelowSMul
import Lemma.Fin.RothMvWeightAdd.eq.AddRothSMvWeight.of.RothMvIndex
import Lemma.Fin.Sum_SquareRothCentered.le.DivCardRothBox4.of.All_Gt_0
import Lemma.Fin.Div_RothDenProduct.le.AbsEval.of.NeEval_AlgebraMapFun_0
import Lemma.Fin.Eq.of.EqRothKroneckerEncode.All_Lt.All_Lt.Gt_1
import Lemma.Real.Any_Lt_Den.of.Infinite.Subset_SetOfLtAbsSub_Div1RpowDen.Gt_0
import Lemma.Fin.RothDegreeBoundOver_Map
import Lemma.Fin.RothKronecker_X.eq.PowXPow
import Lemma.Fin.RothDegreeBound_RothHasseDetMul
import Lemma.Fin.RothRidoutAuxMatrix_LastAddNatDegreeRothIntegralPolynomial1.eq.Eq_RothRidoutBoxComplement1.of.RothBox
import Lemma.Polynomial.RothPolyL1Neg.eq.RothPolyL1
import Lemma.MvPolynomial.FinSuccEquiv.eq.Map
import Lemma.Fin.RothDegreeBoundOver_RothTranslate
import Lemma.Real.Any_LtAbsSub_Div1RpowDenAndLt_Den.of.InfiniteSetOfLtAbsSub_Div1RpowDen.Gt_0
import Lemma.Int.NatAbs.le.RothFinsuppL1
import Lemma.Fin.RothMvVanishesBelow0
import Lemma.Fin.EvalRothTranslateM.eq.Eval_Add
import Lemma.Submodule.RothPolyDerivativeRow_RothKronecker.in.Span_XRothKronHasseJetRows
import Lemma.Fin.NatAbsRothRidoutAuxMatrix.le.PowMul2RothCoordinateBaseSum.of.RothBox
import Lemma.Fin.DivSquare64.le.DivSum_Max_Sub.of.Le_Add_1.Gt_0.GeMul_16.Gt_0.Le_Div_4.Le_1.Gt_0
import Lemma.Polynomial.RothPolyL1.le.MulAddNatDegree1.of.All_LeNatAbsCoeff
import Lemma.Real.Any_Ge_2AndAll_Le2Rpow.of.Gt_0
import Lemma.Fin.RothMvVanishesBelow_Sub.of.RothMvIndex
import Lemma.Polynomial.Eval_MapRothIntPolynomialAlgebraMap.eq.Zero
import Lemma.Real.AbsSub.le.RpowDivNeg.of.LtAbsSub_Div1RpowDen.Le_PowDen.Gt_0.Ge_0.Gt_0
import Lemma.Polynomial.DvdPowSubXC.of.All_EqEvalHasseDeriv_0
import Lemma.Fin.CardRothLowIndex.lt.CardRothBox.of.Lt_MulMul4Square.Gt_0.Gt_0.All_Gt_0
import Lemma.Real.Abs.le.AddAbs1.of.LtAbsSub_Div1RpowDen.Gt_0
import Lemma.Fin.RothMvHasse_Sum.eq.Sum_RothMvHasse.of.RothMvIndex
import Lemma.Nat.RothLastIndex.eq.AddRothSLastIndex.of.RothMvIndex
import Lemma.Fin.InvolutiveRothFlip
import Lemma.Fin.CardSupport.le.CardRothBox
import Lemma.Polynomial.Any_And_Det_PowDerivative.ne.Zero.of.LinearIndependent
import Lemma.Fin.RothMvHasse.eq.Zero.of.Lt
import Lemma.Polynomial.Wronskian.ne.Zero.of.NeNatDegree_NatDegree.Ne_0.Ne_0
import Lemma.Real.RothFiniteDeps
import Lemma.Real.RothCoordinateBase.Gt_0
import Lemma.Real.Any_All_Le_Rpow.of.Gt_0
import Lemma.Real.All_LeAndAntitoneAndAll_Le_MulAndAll_LePowAndSum.le.Mul2AndAll_LePowRpow.of.GeMul_2.LeMul_1.Gt_0.Le.Gt_0.All_LtPow.Monotone.All_Ge_2
import Lemma.Real.RothDenProduct.le.RpowMul_Add1.of.All_LePowDen_RpowAdd1.Ge_0
import Lemma.Real.Pow.le.RpowMul.of.LeSquare_Rpow.Le_Mul2.Ge_0.Ge_1
import Lemma.Real.Mul.lt.Rpow.of.LtAdd.Le_Rpow.Le_Rpow.Ge_0.Gt_1
import Lemma.Real.Prod_PowAbsSub.le.RpowMulNegRothMvWeight.of.All_LtAbsSub_Div1RpowDen.All_Le_PowDen.Gt_0.Ge_0.All_Gt_0
import Lemma.Real.Any_LeRpowMulSum_AddSubAndDvd_RothClearEval_RothMvHasse_RothMvOfCoeff.of.LeRothMvWeight.All_Le_RothWeightAndLeRothWeight_Sub.All_LeRpowDenPow.All_LeRpowDenPow.All_DvdProd_Pow_Den.All_DvdProd_PowNum.All_Le_PowDen.All_Ge_0.All_Ge_0.Ge_0.Gt_1.All_Gt_0.RothMvIndex.RothCoeff
import Lemma.Real.All_Eval_AlgebraMapFunRothMvHasse.eq.Zero.of.LeRothMvWeight.Mul_MulMulPow8SumRothMvL1Prod_PowMax.lt.Rpow.All_Any_LeRpowAndDvd_RothClearEval_RothMvHasse.All_LeProd_PowAbsSub_RpowMulNegRothMvWeight.Gt_1.Ge_0.All_Gt_0.RothMvIndex
open MathlibExt.NumberTheory.RothAuxiliary
open scoped BigOperators
open Real
set_option maxHeartbeats 999999


attribute [local instance] Matrix.seminormedAddCommGroup

/--
[finite_of_divisible_approximations](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  (α : ℝ) (hα : IsAlgebraic ℚ α) (ε : ℝ) (hε : 0 < ε) (hεone : ε ≤ 1)
  {ι : Type*} (S : Finset ι) (p : ι → ℕ) (μ ν : ι → ℝ)
  (hμ : ∀ l ∈ S, 0 ≤ μ l) (hν : ∀ l ∈ S, 0 ≤ ν l)
  (hσ : ∑ l ∈ S, (μ l + ν l) < 2 + ε) :
  Set.Finite {q : ℚ |
    |α - (q : ℝ)| <
        1 / Real.rpow (q.den : ℝ) (2 + ε - ∑ l ∈ S, (μ l + ν l)) ∧
      ∃ a b : ι → ℕ,
        ((∏ l ∈ S, p l ^ a l : ℕ) : ℤ) ∣ q.num ∧
        (∏ l ∈ S, p l ^ b l) ∣ q.den ∧
        ∀ l ∈ S,
          Real.rpow (q.den : ℝ) (μ l) ≤ (p l : ℝ) ^ a l ∧
          Real.rpow (q.den : ℝ) (ν l) ≤ (p l : ℝ) ^ b l} := by
  classical
  let σ := ∑ l ∈ S, (μ l + ν l)
  let A : Set ℚ := {q : ℚ |
    |α - (q : ℝ)| < 1 / Real.rpow (q.den : ℝ) (2 + ε - σ) ∧
      ∃ a b : ι → ℕ,
        ((∏ l ∈ S, p l ^ a l : ℕ) : ℤ) ∣ q.num ∧
        (∏ l ∈ S, p l ^ b l) ∣ q.den ∧
        ∀ l ∈ S,
          Real.rpow (q.den : ℝ) (μ l) ≤ (p l : ℝ) ^ a l ∧
          Real.rpow (q.den : ℝ) (ν l) ≤ (p l : ℝ) ^ b l}
  change A.Finite
  by_contra hinf
  let γ := ε / 16
  let θ := ε / 16
  let η := ε / 16
  let aR := 2 + ε
  let a := aR - σ
  let D := (rothIntegralPolynomial α).natDegree
  let n := ⌈(((D + 2 : ℕ) : ℝ) / (2 * γ ^ 2))⌉₊
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hγhalf : γ < 1 / 2 := by dsimp [γ]; linarith
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθone : θ ≤ 1 := by dsimp [θ]; linarith
  have hη : 0 < η := by dsimp [η]; positivity
  have hD : 0 < D := rothIntegralPolynomial_natDegree_pos_h hα
  have hdenom : 0 < 2 * γ ^ 2 := by positivity
  have hnceil : (((D + 2 : ℕ) : ℝ) / (2 * γ ^ 2)) ≤ n := Nat.le_ceil _
  have hnR : 0 < (n : ℝ) :=
    (div_pos (by positivity) hdenom).trans_le hnceil
  have hn : 0 < n := by exact_mod_cast hnR
  have hparamHalf : (((D + 2 : ℕ) : ℝ)) ≤ 2 * (n + 1 : ℕ) * γ ^ 2 := by
    have hbase : (((D + 2 : ℕ) : ℝ)) ≤ 2 * (n : ℝ) * γ ^ 2 := calc
      _ = (2 * γ ^ 2) * (((D + 2 : ℕ) : ℝ) / (2 * γ ^ 2)) := by
        field_simp
      _ ≤ (2 * γ ^ 2) * n := mul_le_mul_of_nonneg_left hnceil hdenom.le
      _ = 2 * (n : ℝ) * γ ^ 2 := by ring
    calc
      _ ≤ 2 * (n : ℝ) * γ ^ 2 := hbase
      _ ≤ 2 * (n + 1 : ℕ) * γ ^ 2 := by
        push_cast
        nlinarith [sq_nonneg γ]
  have hparamStrict : (((D + 2 : ℕ) : ℝ)) < 4 * (n + 1 : ℕ) * γ ^ 2 := by
    have hpos : 0 < 2 * (n + 1 : ℕ) * γ ^ 2 := by positivity
    nlinarith
  obtain ⟨δ, Q, R, hδ, hδone, hQtwo, hRone, hRoth⟩ :=
    roth_lemma_h n θ hθ hθone
  let β := min δ (1 / (2 * (n + 1 : ℕ)))
  have hβ : 0 < β := lt_min hδ (by positivity)
  have hβδ : β ≤ δ := min_le_left _ _
  have hβn : (n : ℝ) * β ≤ 1 := by
    have hβfrac : β ≤ 1 / (2 * (n + 1 : ℕ)) := min_le_right _ _
    calc
      _ ≤ (n : ℝ) * (1 / (2 * (n + 1 : ℕ))) :=
        mul_le_mul_of_nonneg_left hβfrac (Nat.cast_nonneg _)
      _ ≤ 1 := by
        rw [mul_one_div, div_le_one (by positivity)]
        push_cast
        nlinarith
  let K := ⌈2 / β⌉₊
  have hK : 2 ≤ β * K := by
    have hc : 2 / β ≤ (K : ℝ) := Nat.le_ceil _
    calc
      _ = β * (2 / β) := by field_simp
      _ ≤ β * K := mul_le_mul_of_nonneg_left hc hβ.le
  have hKpos : 0 < K := by
    by_contra hnot
    have hz : K = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hz, Nat.cast_zero, mul_zero] at hK
    norm_num at hK
  let T := (n + 1 : ℕ) * (1 / 2 - γ)
  let g := aR * (T - θ) - (n + 1 : ℕ) * (1 + η)
  have hgform : g = ε / 16 * ((5 - ε) * (n + 1 : ℕ) - (2 + ε)) := by
    dsimp [g, aR, T, θ, η, γ]
    push_cast
    ring
  have hg : 0 < g := by
    rw [hgform]
    have hfive : 0 ≤ 5 - ε := by linarith
    have hmul : 5 - ε ≤ (5 - ε) * (n + 1 : ℕ) := by
      have hn1 : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast (Nat.le_add_left 1 n)
      nlinarith
    have hbracket : 0 < (5 - ε) * (n + 1 : ℕ) - (2 + ε) := by
      nlinarith
    positivity
  let H : ℕ := 8 * rothCoordinateBase α
  let C : ℝ := 8 * H * max 1 |α|
  have hH : 1 ≤ H := by
    dsimp [H]
    have := RothCoordinateBase.Gt_0 α
    omega
  have hC : 1 ≤ C := by
    dsimp [C]
    have hmax : (1 : ℝ) ≤ max 1 |α| := le_max_left _ _
    have hHR : (1 : ℝ) ≤ H := by exact_mod_cast hH
    nlinarith
  obtain ⟨QH, hQH⟩ := Any_All_Le_Rpow.of.Gt_0 ((H : ℝ) ^ 2) hδ
  obtain ⟨QC, hQC⟩ := Any_All_Le_Rpow.of.Gt_0 (C ^ 2) (by positivity : 0 < g / 2)
  let N := max Q (max 2 (max QH QC))
  have hQN : Q ≤ N := le_max_left _ _
  have htwoN : 2 ≤ N :=
    (le_max_left 2 (max QH QC)).trans (le_max_right Q (max 2 (max QH QC)))
  have hQHN : QH ≤ N :=
    (le_max_left QH QC).trans (le_max_right 2 (max QH QC)) |>.trans
      (le_max_right Q (max 2 (max QH QC)))
  have hQCN : QC ≤ N :=
    (le_max_right QH QC).trans (le_max_right 2 (max QH QC)) |>.trans
      (le_max_right Q (max 2 (max QH QC)))
  have ha : 0 < a := by
    dsimp [a, aR, σ]
    linarith
  have hAsub : A ⊆ {q : ℚ |
      |α - (q : ℝ)| < 1 / Real.rpow (q.den : ℝ) a} := by
    intro q hq
    simpa [A, a] using hq.1
  obtain ⟨q, hqA, hq0N, hchain⟩ :=
    roth_ridout_exists_approximation_chain_h (α := α) (p := a) ha A hAsub hinf
      n N K
  have happrox : ∀ h,
      |α - (q h : ℝ)| < 1 / Real.rpow ((q h).den : ℝ) a :=
    fun h ↦ hAsub (hqA h)
  have hwit : ∀ h, ∃ av bv : ι → ℕ,
      ((∏ l ∈ S, p l ^ av l : ℕ) : ℤ) ∣ (q h).num ∧
      (∏ l ∈ S, p l ^ bv l) ∣ (q h).den ∧
      ∀ l ∈ S,
        Real.rpow ((q h).den : ℝ) (μ l) ≤ (p l : ℝ) ^ av l ∧
        Real.rpow ((q h).den : ℝ) (ν l) ≤ (p l : ℝ) ^ bv l := by
    intro h
    exact (hqA h).2
  choose av bv hav using hwit
  let d : Fin (n + 1) → ℕ := fun h ↦ (q h).den
  have hKone : 1 ≤ K := hKpos
  have hdstep : ∀ i : Fin n, d i.castSucc ≤ d i.succ := by
    intro i
    calc
      _ = d i.castSucc ^ 1 := (pow_one _).symm
      _ ≤ d i.castSucc ^ K :=
        pow_le_pow_right₀ (q i.castSucc).pos hKone
      _ ≤ d i.succ := (hchain i).le
  have hdmono : Monotone d := Fin.monotone_iff_le_succ.mpr hdstep
  have hd0two : 2 ≤ d 0 := htwoN.trans hq0N.le
  have hd : ∀ h, 2 ≤ d h := fun h ↦ hd0two.trans (hdmono (Fin.zero_le h))
  obtain ⟨r, hrlarge, hranti, hsep, hpower, hsum, hupper⟩ :=
    All_LeAndAntitoneAndAll_Le_MulAndAll_LePowAndSum.le.Mul2AndAll_LePowRpow.of.GeMul_2.LeMul_1.Gt_0.Le.Gt_0.All_LtPow.Monotone.All_Ge_2 d K R δ β η hd hdmono hchain
      hβ hβδ hη hβn hK
  have hrpos : ∀ h, 0 < r h := fun h ↦
    lt_of_lt_of_le Nat.zero_lt_one (hRone.trans (hrlarge h))
  obtain ⟨c, hc, hcvan, hcbalanced, hcl1⟩ :=
    roth_ridout_exists_auxiliary_coeff_h α hα hrpos
      (by omega : 0 < n + 1) hγ hγhalf
      (by simpa [D] using hparamStrict) (by simpa [D] using hparamHalf)
  let P := rothMvOfCoeff c
  have hPne : P ≠ 0 := rothMvOfCoeff_ne_zero_h hc
  have hPdegree : rothDegreeBound P r := rothMvOfCoeff_degreeBound_h c
  have hPvan : rothMvVanishesBelow
    (MvPolynomial.map (algebraMap ℤ ℝ) P) (fun h ↦ α) r T := by
    exact rothVanishesBelow_to_mv_h hcvan
  have hheight : (rothMvL1 P : ℝ) ≤
      Real.rpow (q 0).den (δ * r 0) := by
    have hbase : (H : ℝ) ^ 2 ≤ Real.rpow (q 0).den δ :=
      hQH _ (hQHN.trans hq0N.le)
    calc
      _ ≤ ((H ^ (∑ h, r h) : ℕ) : ℝ) := by
        exact_mod_cast hcl1
      _ = (H : ℝ) ^ (∑ h, r h) := by norm_cast
      _ ≤ Real.rpow (q 0).den (δ * r 0) :=
        Pow.le.RpowMul.of.LeSquare_Rpow.Le_Mul2.Ge_0.Ge_1 H (q 0).den δ (∑ h, r h) (r 0)
          (by exact_mod_cast hH) (by positivity) hsum hbase
  let Q₀ : ℝ := ((q 0).den : ℝ) ^ r 0
  have hQ₀ : 1 < Q₀ := by
    dsimp [Q₀]
    apply one_lt_pow₀
    · exact_mod_cast hd0two
    · exact (hrpos 0).ne'
  have hpowerR : ∀ h, Q₀ ≤ ((q h).den : ℝ) ^ r h := by
    intro h
    dsimp [Q₀]
    exact_mod_cast hpower h
  have herr : ∀ l : RothMvIndex (n + 1),
      ∏ h, |(q h : ℝ) - α| ^ l h ≤
        Real.rpow Q₀ (-a * rothMvWeight r l) := by
    exact Prod_PowAbsSub.le.RpowMulNegRothMvWeight.of.All_LtAbsSub_Div1RpowDen.All_Le_PowDen.Gt_0.Ge_0.All_Gt_0 (fun h ↦ α) q r a Q₀
      hrpos ha.le (zero_lt_one.trans hQ₀) hpowerR happrox
  have hdenUpper : (rothDenProduct q r : ℝ) ≤
      Real.rpow Q₀ ((n + 1 : ℕ) * (1 + η)) := by
    apply RothDenProduct.le.RpowMul_Add1.of.All_LePowDen_RpowAdd1.Ge_0 q r Q₀ η (zero_le_one.trans hQ₀.le)
    intro h
    simpa [Q₀, d] using hupper h
  let F : ℝ :=
    (((8 ^ (∑ h, r h) * rothMvL1 P : ℕ) : ℝ) *
      ∏ h : Fin (n + 1), max 1 |α| ^ r h)
  have hFnonneg : 0 ≤ F := by dsimp [F]; positivity
  have hF : F ≤ Real.rpow Q₀ (g / 2) := by
    have hCbase : C ^ 2 ≤ Real.rpow (q 0).den (g / 2) :=
      hQC _ (hQCN.trans hq0N.le)
    have hCpow : C ^ (∑ h, r h) ≤
        Real.rpow (q 0).den ((g / 2) * r 0) :=
      Pow.le.RpowMul.of.LeSquare_Rpow.Le_Mul2.Ge_0.Ge_1 C (q 0).den (g / 2) (∑ h, r h) (r 0)
        hC (by positivity) hsum hCbase
    have hraw : F ≤ C ^ (∑ h, r h) := by
      dsimp [F, C]
      rw [Finset.prod_pow_eq_pow_sum]
      calc
        _ ≤ ((8 : ℝ) ^ (∑ h, r h) * (H : ℝ) ^ (∑ h, r h)) *
            max 1 |α| ^ (∑ h, r h) := by
          push_cast
          gcongr
          · exact_mod_cast hcl1
        _ = (8 * (H : ℝ) * max 1 |α|) ^ (∑ h, r h) := by
          rw [mul_pow, mul_pow]
    refine hraw.trans (hCpow.trans_eq ?_)
    dsimp [Q₀]
    calc
      _ = Real.rpow (q 0).den ((r 0 : ℝ) * (g / 2)) := by
        congr 1; ring
      _ = Real.rpow (Real.rpow (q 0).den (r 0 : ℝ)) (g / 2) :=
        Real.rpow_mul (by positivity) _ _
      _ = Real.rpow (((q 0).den : ℝ) ^ r 0) (g / 2) := by
        congr 1
        exact Real.rpow_natCast _ _
  have hmaster : (rothDenProduct q r : ℝ) * F <
      Real.rpow Q₀ (aR * (T - θ)) := by
    apply Mul.lt.Rpow.of.LtAdd.Le_Rpow.Le_Rpow.Ge_0.Gt_1 Q₀ (rothDenProduct q r) F
      ((n + 1 : ℕ) * (1 + η)) (g / 2) (aR * (T - θ)) hQ₀
      hFnonneg hdenUpper hF
    dsimp [g]
    nlinarith
  let s := σ * (T - θ)
  have hdiv : ∀ i : RothMvIndex (n + 1), rothMvWeight r i ≤ θ →
      ∃ G : ℕ, Real.rpow Q₀ s ≤ G ∧
        (G : ℤ) ∣ rothClearEval (rothMvHasse i P) q r := by
    intro i hi
    simpa [P, s, σ] using
      Any_LeRpowMulSum_AddSubAndDvd_RothClearEval_RothMvHasse_RothMvOfCoeff.of.LeRothMvWeight.All_Le_RothWeightAndLeRothWeight_Sub.All_LeRpowDenPow.All_LeRpowDenPow.All_DvdProd_Pow_Den.All_DvdProd_PowNum.All_Le_PowDen.All_Ge_0.All_Ge_0.Ge_0.Gt_1.All_Gt_0.RothMvIndex.RothCoeff S p q r av bv μ ν c Q₀ T θ i
        hrpos hQ₀ hθ.le hμ hν hpowerR
        (fun h ↦ (hav h).1) (fun h ↦ (hav h).2.1)
        (fun h l hl ↦ (hav h).2.2 l hl |>.1)
        (fun h l hl ↦ (hav h).2.2 l hl |>.2)
        hcbalanced hi
  have hmaster' : (rothDenProduct q r : ℝ) *
        (((8 ^ (∑ h, r h) * rothMvL1 P : ℕ) : ℝ) *
          ∏ h, max 1 |(fun h : Fin (n + 1) ↦ α) h| ^ r h) <
      Real.rpow Q₀ (s + a * (T - θ)) := by
    have hs : s + a * (T - θ) = aR * (T - θ) := by
      dsimp [s, a]
      ring
    rw [hs]
    simpa [F] using hmaster
  have hzero := All_Eval_AlgebraMapFunRothMvHasse.eq.Zero.of.LeRothMvWeight.Mul_MulMulPow8SumRothMvL1Prod_PowMax.lt.Rpow.All_Any_LeRpowAndDvd_RothClearEval_RothMvHasse.All_LeProd_PowAbsSub_RpowMulNegRothMvWeight.Gt_1.Ge_0.All_Gt_0.RothMvIndex P
    (fun h ↦ α) q r T a Q₀ θ s hrpos hPdegree hPvan
    ha.le hQ₀ herr hdiv hmaster'
  have hratvan := roth_rational_vanishing_of_real_hasse_zero_h P q r θ hzero
  let X : RothLemmaInput n δ Q R := {
    P := P
    r := r
    q := q
    P_ne := hPne
    P_degree := hPdegree
    r_large := hrlarge
    den_large := hQN.trans hq0N.le
    den_monotone := by simpa [d] using hdmono
    r_antitone := hranti
    separated := hsep
    den_power := by simpa [d] using hpower
    height := hheight
  }
  exact hRoth X hratvan


-- created on 2026-10-21
