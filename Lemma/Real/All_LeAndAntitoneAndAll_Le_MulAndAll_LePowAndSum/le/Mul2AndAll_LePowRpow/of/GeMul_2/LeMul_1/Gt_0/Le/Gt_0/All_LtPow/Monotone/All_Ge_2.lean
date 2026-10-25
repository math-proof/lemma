import Mathlib
import sympy.Basic
import Theorem.NumberTheory.RothAuxiliary.Part7
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
import Lemma.Real.Any_LeRpowMulSum_AddSubAndDvd_RothClearEval_RothMvHasse_RothMvOfCoeff.of.LeRothMvWeight.All_Le_RothWeightAndLeRothWeight_Sub.All_LeRpowDenPow.All_LeRpowDenPow.All_DvdProd_Pow_Den.All_DvdProd_PowNum.All_Le_PowDen.All_Ge_0.All_Ge_0.Ge_0.Gt_1.All_Gt_0.RothMvIndex.RothCoeff
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
import Lemma.Real.RothCoordinateBase.Gt_0
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
import Lemma.Real.Prod_PowAbsSub.le.RpowMulNegRothMvWeight.of.All_LtAbsSub_Div1RpowDen.All_Le_PowDen.Gt_0.Ge_0.All_Gt_0
import Lemma.Real.Finite.of.LtSum_Add_Add2.All_Ge_0.All_Ge_0.Le_1.Gt_0.IsAlgebraic
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
import Lemma.Real.Mul.lt.Rpow.of.LtAdd.Le_Rpow.Le_Rpow.Ge_0.Gt_1
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
import Lemma.Real.Any_All_Le_Rpow.of.Gt_0
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
import Lemma.Real.RothDenProduct.le.RpowMul_Add1.of.All_LePowDen_RpowAdd1.Ge_0
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
import Lemma.Real.Pow.le.RpowMul.of.LeSquare_Rpow.Le_Mul2.Ge_0.Ge_1
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
import Lemma.Real.All_Eval_AlgebraMapFunRothMvHasse.eq.Zero.of.LeRothMvWeight.Mul_MulMulPow8SumRothMvL1Prod_PowMax.lt.Rpow.All_Any_LeRpowAndDvd_RothClearEval_RothMvHasse.All_LeProd_PowAbsSub_RpowMulNegRothMvWeight.Gt_1.Ge_0.All_Gt_0.RothMvIndex
import Lemma.Fin.RothMvHasse_Sum.eq.Sum_RothMvHasse.of.RothMvIndex
import Lemma.Nat.RothLastIndex.eq.AddRothSLastIndex.of.RothMvIndex
import Lemma.Fin.InvolutiveRothFlip
import Lemma.Fin.CardSupport.le.CardRothBox
import Lemma.Polynomial.Any_And_Det_PowDerivative.ne.Zero.of.LinearIndependent
import Lemma.Fin.RothMvHasse.eq.Zero.of.Lt
import Lemma.Polynomial.Wronskian.ne.Zero.of.NeNatDegree_NatDegree.Ne_0.Ne_0
open MathlibExt.NumberTheory.RothAuxiliary


/--
[roth_exists_balanced_degrees](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ}
  (d : Fin (m + 1) → ℕ)
  (K R : ℕ)
  (δ β η : ℝ)
-- given
  (hd : ∀ h, 2 ≤ d h)
  (hdmono : Monotone d)
  (hchain : ∀ i : Fin m, d i.castSucc ^ K < d i.succ)
  (hβ : 0 < β)
  (hβδ : β ≤ δ)
  (hη : 0 < η)
  (hβm : (m : ℝ) * β ≤ 1)
  (hK : 2 ≤ β * K) :
-- imply
  ∃ r : Fin (m + 1) → ℕ,
    (∀ h, R ≤ r h) ∧ Antitone r ∧
    (∀ i : Fin m, (r i.succ : ℝ) ≤ δ * r i.castSucc) ∧
    (∀ h, d 0 ^ r 0 ≤ d h ^ r h) ∧
    (∑ h, r h) ≤ 2 * r 0 ∧
    (∀ h, ((d h : ℝ) ^ r h) ≤
      Real.rpow ((d 0 : ℝ) ^ r 0) (1 + η)) := by
-- proof
  classical
  have hdone : ∀ h, 1 ≤ d h := fun h ↦ (by norm_num : (1 : ℕ) ≤ 2).trans (hd h)
  have hd0 : 1 < d 0 := lt_of_lt_of_le Nat.one_lt_two (hd 0)
  choose e he using fun h : Fin (m + 1) ↦ pow_unbounded_of_one_lt (d h) hd0
  let E := ∑ h, e h
  let R' := max R ⌈2 / β⌉₊
  let B := ∑ h, d h ^ R'
  obtain ⟨s₀, hs₀⟩ := pow_unbounded_of_one_lt B hd0
  obtain ⟨s₁, hs₁⟩ := exists_nat_ge ((E : ℝ) / η)
  let s := max 1 (max s₀ s₁)
  have hspos : 0 < s := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hs₀s : s₀ ≤ s := (le_max_left s₀ s₁).trans
    (le_max_right 1 (max s₀ s₁))
  have hs₁s : s₁ ≤ s := (le_max_right s₀ s₁).trans
    (le_max_right 1 (max s₀ s₁))
  have hBpow : B < d 0 ^ s := hs₀.trans_le
    (pow_le_pow_right₀ (by omega : 1 ≤ d 0) hs₀s)
  have hEη : (E : ℝ) ≤ η * s := by
    have hs₁R : (s₁ : ℝ) ≤ s := by exact_mod_cast hs₁s
    have hηne : η ≠ 0 := hη.ne'
    calc
      _ = η * ((E : ℝ) / η) := by field_simp
      _ ≤ η * s₁ := mul_le_mul_of_nonneg_left hs₁ hη.le
      _ ≤ η * s := mul_le_mul_of_nonneg_left hs₁R hη.le
  have hceil : 2 / β ≤ (⌈2 / β⌉₊ : ℝ) := Nat.le_ceil _
  have hR'β : 2 ≤ β * R' := by
    have hcR : (⌈2 / β⌉₊ : ℝ) ≤ R' := by
      exact_mod_cast (le_max_right R ⌈2 / β⌉₊)
    calc
      _ = β * (2 / β) := by field_simp
      _ ≤ β * (⌈2 / β⌉₊ : ℝ) := mul_le_mul_of_nonneg_left hceil hβ.le
      _ ≤ β * R' := mul_le_mul_of_nonneg_left hcR hβ.le
  have hR'pos : 0 < R' := by
    by_contra hnot
    have hz : R' = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hz, Nat.cast_zero, mul_zero] at hR'β
    norm_num at hR'β
  have hexists : ∀ h : Fin (m + 1), ∃ n, d 0 ^ s ≤ d h ^ n := by
    intro h
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (d 0 ^ s)
      (lt_of_lt_of_le Nat.one_lt_two (hd h))
    exact ⟨n, hn.le⟩
  let r : Fin (m + 1) → ℕ := fun h ↦ Nat.find (hexists h)
  have hrpow : ∀ h, d 0 ^ s ≤ d h ^ r h := fun h ↦ Nat.find_spec (hexists h)
  have hrmin : ∀ h n, d 0 ^ s ≤ d h ^ n → r h ≤ n :=
    fun h n hn ↦ Nat.find_min' (hexists h) hn
  have hrzero : r 0 = s := by
    apply le_antisymm (hrmin 0 s le_rfl)
    exact (Nat.pow_le_pow_iff_right hd0).mp (hrpow 0)
  have hR'large : ∀ h, R' ≤ r h := by
    intro h
    by_contra hnot
    have hrR : r h ≤ R' := Nat.le_of_lt (lt_of_not_ge hnot)
    refine (not_lt_of_ge ((hrpow h).trans
      ((pow_le_pow_right₀ (hdone h) hrR).trans ?_))) hBpow
    have ht := Finset.single_le_sum
      (s := Finset.univ) (f := fun j : Fin (m + 1) ↦ d j ^ R')
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ h)
    simpa [B] using ht
  have hrlarge : ∀ h, R ≤ r h := fun h ↦
    (le_max_left R ⌈2 / β⌉₊).trans (hR'large h)
  have hranti : Antitone r := by
    intro i j hij
    apply hrmin j (r i)
    exact (hrpow i).trans (by gcongr; exact hdmono hij)
  have hβr : ∀ h, 2 ≤ β * r h := by
    intro h
    exact hR'β.trans (mul_le_mul_of_nonneg_left
      (by exact_mod_cast hR'large h : (R' : ℝ) ≤ r h) hβ.le)
  have hKpos : 0 < K := by
    by_contra hnot
    have hz : K = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hz, Nat.cast_zero, mul_zero] at hK
    norm_num at hK
  have hsepβ : ∀ i : Fin m, (r i.succ : ℝ) ≤ β * r i.castSucc := by
    intro i
    let t := r i.castSucc / K + 1
    have hrit : r i.castSucc ≤ K * t := by
      dsimp [t]
      exact (Nat.lt_mul_div_succ (r i.castSucc) hKpos).le
    have hcandidate : d 0 ^ s ≤ d i.succ ^ t := calc
      _ ≤ d i.castSucc ^ r i.castSucc := hrpow i.castSucc
      _ ≤ d i.castSucc ^ (K * t) :=
        pow_le_pow_right₀ (hdone i.castSucc) hrit
      _ = (d i.castSucc ^ K) ^ t := by rw [pow_mul]
      _ ≤ d i.succ ^ t := by gcongr; exact (hchain i).le
    have hrnext : r i.succ ≤ t := hrmin i.succ t hcandidate
    have hKreal : (0 : ℝ) < K := by exact_mod_cast hKpos
    have hdiv : (1 : ℝ) / K ≤ β / 2 := by
      apply (div_le_iff₀ hKreal).2
      nlinarith
    have hfirst : (r i.castSucc : ℝ) / K ≤
        β * r i.castSucc / 2 := calc
      _ = (r i.castSucc : ℝ) * (1 / K) := by ring
      _ ≤ (r i.castSucc : ℝ) * (β / 2) := by gcongr
      _ = β * r i.castSucc / 2 := by ring
    have hsecond : (1 : ℝ) ≤ β * r i.castSucc / 2 := by
      nlinarith [hβr i.castSucc]
    calc
      _ ≤ (t : ℝ) := by exact_mod_cast hrnext
      _ = ((r i.castSucc / K : ℕ) : ℝ) + 1 := by simp [t]
      _ ≤ (r i.castSucc : ℝ) / K + 1 := by
        gcongr
        exact Nat.cast_div_le
      _ ≤ β * r i.castSucc := by linarith
  have hsep : ∀ i : Fin m, (r i.succ : ℝ) ≤ δ * r i.castSucc := by
    intro i
    exact (hsepβ i).trans
      (mul_le_mul_of_nonneg_right hβδ (Nat.cast_nonneg _))
  have hsum : (∑ h, r h) ≤ 2 * r 0 := by
    have htail : ∀ i : Fin m, (r i.succ : ℝ) ≤ β * r 0 := by
      intro i
      exact (hsepβ i).trans (mul_le_mul_of_nonneg_left
        (by exact_mod_cast hranti (Fin.zero_le i.castSucc)) hβ.le)
    have hsumR : ((∑ h, r h : ℕ) : ℝ) ≤ 2 * (r 0 : ℝ) := by
      rw [Fin.sum_univ_succ, Nat.cast_add, Nat.cast_sum]
      calc
        _ ≤ (r 0 : ℝ) + ∑ _ : Fin m, β * r 0 := by gcongr with i; exact htail i
        _ = (r 0 : ℝ) + (m : ℝ) * (β * r 0) := by simp
        _ ≤ 2 * (r 0 : ℝ) := by
          have hr0nonneg : (0 : ℝ) ≤ r 0 := by positivity
          nlinarith [mul_le_mul_of_nonneg_right hβm hr0nonneg]
    exact_mod_cast hsumR
  refine ⟨r, hrlarge, hranti, hsep, fun h ↦ by simpa [hrzero] using hrpow h,
    hsum, ?_⟩
  intro h
  have hrpos : 0 < r h := hR'pos.trans_le (hR'large h)
  have hpred : d h ^ (r h - 1) < d 0 ^ s := by
    apply lt_of_not_ge
    exact Nat.find_min (hexists h) (Nat.sub_lt (Nat.zero_lt_of_lt hrpos) Nat.zero_lt_one)
  have hstep : d h ^ r h < d 0 ^ s * d h := calc
    _ = d h ^ (r h - 1) * d h := by
      conv_lhs => rw [show r h = (r h - 1) + 1 by omega, pow_succ]
    _ < d 0 ^ s * d h := Nat.mul_lt_mul_of_pos_right hpred
      (lt_of_lt_of_le Nat.zero_lt_two (hd h))
  have heE : e h ≤ E := by
    have ht := Finset.single_le_sum
      (s := Finset.univ) (f := fun j : Fin (m + 1) ↦ e j)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ h)
    simpa [E] using ht
  have hdE : d h ≤ d 0 ^ E :=
    (he h).le.trans (pow_le_pow_right₀ hd0.le heE)
  have hnat : d h ^ r h ≤ d 0 ^ (s + E) := calc
    _ ≤ d 0 ^ s * d h := hstep.le
    _ ≤ d 0 ^ s * d 0 ^ E := Nat.mul_le_mul_left _ hdE
    _ = d 0 ^ (s + E) := (pow_add _ _ _).symm
  have hexp : ((s + E : ℕ) : ℝ) ≤ (s : ℝ) * (1 + η) := by
    push_cast
    nlinarith
  calc
    _ = ((d h ^ r h : ℕ) : ℝ) := by norm_num
    _ ≤ ((d 0 ^ (s + E) : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = (d 0 : ℝ) ^ (s + E) := by norm_cast
    _ = Real.rpow (d 0 : ℝ) (s + E : ℕ) :=
      (Real.rpow_natCast _ _).symm
    _ ≤ Real.rpow (d 0 : ℝ) ((s : ℝ) * (1 + η)) :=
      Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast (hdone 0) : (1 : ℝ) ≤ d 0) hexp
    _ = Real.rpow (Real.rpow (d 0 : ℝ) (s : ℝ)) (1 + η) :=
      Real.rpow_mul (by positivity) _ _
    _ = Real.rpow ((d 0 : ℝ) ^ s) (1 + η) := by
      congr 1
      exact Real.rpow_natCast _ _
    _ = Real.rpow ((d 0 : ℝ) ^ r 0) (1 + η) := by rw [hrzero]


-- created on 2026-10-21
