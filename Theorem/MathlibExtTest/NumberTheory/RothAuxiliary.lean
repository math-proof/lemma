/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/RothAuxiliary.lean -/


import Theorem.NumberTheory.RothAuxiliary.Part7
import Theorem.Int.RothFinsuppL1_Single.eq.NatAbs
import Theorem.Finset.RothFinsuppL1_Sum.le.Sum_RothFinsuppL1
import Theorem.Fin.RothKroneckerEncode.eq.Add_Mul_RothKroneckerEncode
import Theorem.Fin.RothWeight_RothRidoutBoxComplement.eq.Sub_RothWeight.of.All_Gt_0.RothBox
import Theorem.Fin.CoeffCoeffRothLastEquiv.eq.CoeffRothLastIndex.of.RothMvIndex
import Lemma.Matrix.Mul_SubDiv1'2.le.RothWeightAndRothWeight.le.Sub_Mul_SubDiv1'2.of.Ne_0.RothBox.EqMulVecRothRidoutAuxMatrix_0.All_Gt_0.RothCoeff
import Theorem.Polynomial.Map_AlgebraMapRothLastSlice.eq.MulCCoeff.of.EqRothLastEquiv_MapAlgebraMap_MulC_MapAlgebraMapMapC.RothMvIndex
import Lemma.MvPolynomial.RothKronecker.eq.Monomial
import Theorem.Fin.RothMvHasse_RothMvHasse.eq.SMul_RothMvHasse.of.RothMvIndex
import Lemma.Fin.CardRothLowIndex.Gt_0.of.Lt_Div1'2.Gt_0.Gt_0
import Theorem.Fin.Sum_SquareRothCenteredSum.le.DivMul_CardRothBox4.of.All_Gt_0
import Theorem.Fin.RothDegreeBound_Sum.of.All_RothDegreeBound
import Lemma.MvPolynomial.EvalAlgebraMap.eq.Eval_AlgebraMapFun
import Theorem.Fin.RothMvHasse_Single1.eq.Pderiv
import Theorem.Fin.Eval_0RothMvHasse.eq.Coeff.of.RothMvIndex
import Theorem.Nat.MulChooseS
import Lemma.Fin.MulMulMul4SquareCardRothLowIndices.le.CardRothBox.of.Gt_0.Gt_0.All_Gt_0
import Lemma.Fin.Any_And_Det_RothMvHasse.ne.Zero.of.All_RothKroneckerBounded.LinearIndependent.Gt_1
import Theorem.Real.Rpow.le.Prod_MulPowSRpow.of.All_Le.All_Le_PowDen.Ge_0.Ge_0.All_Gt_0.Gt_0.RothMvIndex
import Lemma.Fin.Any_All_Eq_RothRidoutExponentAndAll_All_Le_RothRidoutExponentAndDvdProd_PowRothClearEval.of.All_DvdProd_Pow_Den.All_DvdProd_PowNum.NonemptySupport
import Theorem.Fin.RothMvHasse0.eq.Zero.of.RothMvIndex
import Theorem.Fin.EqRothLastTail.of.RothMvIndexAdd_1
import Lemma.Fin.RothZeroBox.in.RothLowIndices.of.Lt_Div1'2.Gt_0
import Theorem.Fin.RothMvVanishesBelow.of.Le_0
import Theorem.Polynomial.LtDegreeMulC.of.LtDegree
import Lemma.Finset.Prod_Pow_RothRidoutExponent.dvd.Prod_MulPowNumPowDenSub.of.RothMvIndex.All_DvdProd_Pow_Den.All_DvdProd_PowNum
import Lemma.Fin.Pow_RothRidoutExponent.eq.Prod_MulPowPowPowPowSub.of.RothMvIndex
import Theorem.Fin.RothMvL1'1.eq.One
import Lemma.MvPolynomial.Eval.eq.RothHasseEval.of.RothBox.RothCoeff
import Theorem.Fin.NatAbsCoeff.le.RothMvL1.of.RothMvIndex
import Lemma.MvPolynomial.All_EqRothTranslateC
import Theorem.Nat.RothMvOrderAdd.eq.AddRothSMvOrder.of.RothMvIndex
import Theorem.Real.FiniteSetOfLtAbsSub_Div1RpowDenAndLeDen.of.Gt_0
import Theorem.Fin.SquareRothCentered.le.Div1'4.of.RothBox.All_Gt_0
import Theorem.Fin.RothMvL1.le.MulPowS
import Theorem.Polynomial.Any_Eq_SMul.of.EqWronskian_0.Ne_0
import Theorem.Fin.GetRothFlip.eq.Sub.of.RothBox
import Lemma.Real.Any_LeRpowMulSum_AddSubAndDvd_RothClearEval_RothMvHasse_RothMvOfCoeff.of.LeRothMvWeight.All_Le_RothWeightAndLeRothWeight_Sub.All_LeRpowDenPow.All_LeRpowDenPow.All_DvdProd_Pow_Den.All_DvdProd_PowNum.All_Le_PowDen.All_Ge_0.All_Ge_0.Ge_0.Gt_1.All_Gt_0.RothMvIndex.RothCoeff
import Lemma.Rat.NatDegreeRothIntPolynomial.Gt_0.of.IsAlgebraic
import Theorem.Fin.EqRothMvOrder_Single
import Theorem.Fin.RothLastEquiv_Map.eq.Map_MapRothLastEquiv
import Theorem.Fin.RothMvOrderAdd_Single1.eq.AddRothMvOrder1.of.RothMvIndex
import Theorem.Polynomial.LeDiv.of.LeNatAbsLeadingCoeffRpow_DenMul.Gt_0.GeDen_2.Ne_0
import Theorem.Real.LiouvilleWith.of.InfiniteSetOfLtAbsSub_Div1RpowDen.Gt_0.Irrational
import Theorem.Nat.EqEquivMapDomain_EquivMapDomainSymm
import Theorem.Fin.RothMvVanishesBelow.of.All_RothMvVanishesBelow
import Theorem.Fin.LeNatDegreeRothLastEquiv
import Theorem.Polynomial.RothLastEquiv.eq.Sum_MulCMap.of.RothMvIndex.Eq_Sum_MulCMapC
import Theorem.Fin.RothMvVanishesBelow
import Lemma.Submodule.RothPolyWronskianRow.in.Span_XRothPolyJetRows1
import Lemma.Real.RothCoordinateBase.Gt_0
import Lemma.Fin.RothRidoutAuxMatrix_CastSuccLastNatDegreeRothIntegralPolynomial.eq.Eq_1.of.RothBox
import Theorem.Fin.MapRothHasseDet.eq.RothHasseDet_Map
import Theorem.Polynomial.RothPolyL1_RothPowerCoordAdd_1.le.MulAddRothPolyL1'1RothPolyL1_RothPowerCoord
import Lemma.Polynomial.Eval.eq.PowMulLeadingCoeffRothIntPolynomial.of.IsAlgebraic
import Theorem.Fin.RothDegreeBound.of.All_RothDegreeBound
import Theorem.Fin.LeNatDegreeRothLastSlice.of.RothMvIndex
import Lemma.Fin.MulRothDenProductEvalAlgebraMap.eq.RothClearEval
import Lemma.Fin.Any_And_Det_RothMvHasse.ne.Zero.of.All_RothDegreeBoundOver.LinearIndependent
import Theorem.Fin.RothMvWeight_Mul.eq.DivRothMvWeight.of.All_Gt_0.Gt_0.RothMvIndex
import Theorem.Fin.Pderiv.eq.SMul.of.RothMvIndex
import Theorem.Nat.Factorial.le.Pow2Mul.of.Gt_0
import Theorem.Fin.EqCoeffRothMvOfCoeffRothBoxIndex.of.RothBox.RothCoeff
import Theorem.Real.Prod_PowAbsSub.le.RpowMulNegRothMvWeight.of.All_LeAbsSub_RpowDivNeg.Gt_0
import Theorem.Polynomial.RothPolyWronskianDerivativeRow0.eq.Zero
import Theorem.Int.RothFinsuppL1_Sub.le.AddRothSFinsuppL1
import Theorem.Fin.RothDegreeBoundNeg
import Lemma.Rat.RothIntPolynomial.ne.Zero.of.IsAlgebraic
import Theorem.Fin.RothDegreeBound
import Lemma.Matrix.Eq_0.of.EqMulVecRothRidoutAuxMatrix_0.RothCoeff
import Lemma.Real.Prod_MulPowRpowDenPowRpowDenSub.le.Pow_RothRidoutExponent.of.All_LeRpowDenPow.All_LeRpowDenPow.RothMvIndex
import Theorem.Polynomial.LinearIndependent_J.of.LinearIndependent
import Lemma.MvPolynomial.CoeffGetFinSuccEquivRothMvHasse_Cons.eq.RothMvHasse_CoeffHasseDerivGetFinSuccEquiv
import Theorem.Submodule.DetUpdateRow.ne.Zero.of.In_Span.NeDet_0
import Lemma.MvPolynomial.CoeffRothTranslate_Eval_C.eq.Sum_MulCoeffRothTranslate_CoeffPow.of.RothMvIndex
import Lemma.Polynomial.Eval.eq.MulPowLeadingCoeffRothIntPolynomialSumRothHasseEval.of.RothCoeff.RothBox.IsAlgebraic
import Lemma.Fin.RothTermDegree.le.Sum.of.RothBox
import Theorem.Polynomial.NatAbsCoeff.le.RothPolyL1
import Theorem.Fin.Nonempty_RothIntegralFactorData.of.RothDeterminantData
import Lemma.Matrix.MulVecRothAuxMatrix.eq.Zero.of.EqMulVecRothRidoutAuxMatrix_0.RothCoeff
import Theorem.Fin.RothMvWeight_RothRidoutComplement.eq.Sub_RothMvWeight.of.All_Le.All_Gt_0.RothMvIndex
import Lemma.MvPolynomial.RothMvL1_Monomial.eq.NatAbs.of.RothMvIndex
import Theorem.Polynomial.RothPolyJetRows.sub.RothPolyJetRows.of.Le
import Lemma.MvPolynomial.Eval_LastCases.eq.Eval_Map_EvalRothLastEquiv
import Lemma.MvPolynomial.DerivativeRothKronecker.eq.Sum_MulMulCPowPowXSubPow1RothKronecker_Pderiv
import Lemma.Submodule.RothPolyWronskianDerivativeRow.in.Span_XRothPolyJetRowsAdd_1
import Lemma.Rat.MonicRothIntegralPolynomial.of.IsAlgebraic
import Theorem.Fin.RothDegreeBoundSMul
import Theorem.Fin.RothMvHasseAdd.eq.AddRothSMvHasse.of.RothMvIndex
import Theorem.Fin.RothMvL1_Sub.le.AddRothSMvL1
import Theorem.Fin.LinearIndependent_RothKronecker.of.All_RothKroneckerBounded.LinearIndependent.Gt_1
import Lemma.Fin.RothPolyL1_RothAuxTerm.le.PowMul2RothCoordinateBaseSum.of.RothBox
import Lemma.MvPolynomial.CoeffRothTranslate
import Theorem.Fin.RothMvVanishesBelow.of.All_LeRothMvWeight
import Theorem.Fin.RothMvL1_RothMvHasse.le.MulPow2SumRothMvL1.of.RothMvIndex
import Lemma.Polynomial.Eval_AlgebraMapMulLeadingCoeffRothIntPolynomialRothIntegralPolynomial.eq.Zero.of.IsAlgebraic
import Lemma.Polynomial.Eval.eq.MulMulProd_ChoosePowLeadingCoeffRothIntPolynomialSumPow_RothTermDegree.of.RothBox.IsAlgebraic
import Theorem.Polynomial.RothPolyL1X.eq.One
import Theorem.Fin.RothMvOfCoeff.ne.Zero.of.Ne_0
import Theorem.Fin.RothKronHasseJetRows.sub.RothKronHasseJetRows.of.Le
import Theorem.Fin.RothMvVanishesBelow_Sum.of.All_RothMvVanishesBelow
import Theorem.Fin.RothMvL1_Sum.le.Sum_RothMvL1
import Lemma.Real.RothPolyL1_RothScaledPowerCoord.le.PowRothCoordinateBase.of.Le
import Theorem.Real.RpowMul.le.RpowMul.of.LePow_Pow.Ge_0
import Theorem.Polynomial.RothPolyL1Mul.le.MulRothSPolyL1
import Theorem.Fin.Sub.le.RothMvWeightAndLe_RothMvWeight_RothRidoutComplement.of.In_SupportRothMvHasse_RothMvOfCoeff.LeRothMvWeight.RothMvIndex.All_Le_RothWeightAndLeRothWeight_Sub.RothCoeff.All_Gt_0
import Theorem.Fin.RothMvVanishesBelow.of.Le
import Theorem.Fin.RothKroneckerBounded_Sum.of.All_RothKroneckerBounded
import Theorem.Fin.RothPolyL1.le.MulAdd_1RothMvL1.of.RothMvIndex
import Theorem.Polynomial.Det_HasseDerivVal.ne.Zero.of.LinearIndependent
import Theorem.Finset.RothFinsuppL1.eq.Sum_NatAbs.of.SubsetSupport
import Theorem.Fin.CardRothBox.eq.Prod_Add_1
import Theorem.Fin.RothMvL1_RothHasseDet.le.MulFactorialPowMulPow2SumRothMvL1
import Theorem.Fin.CardRothBox.le.Pow2Sum.of.All_Gt_0
import Theorem.Fin.MapRothMvHasse.eq.RothMvHasse_Map.of.RothMvIndex
import Lemma.Fin.Nonempty_RothDeterminantData.of.Ne_0
import Lemma.Finset.Prod_Pow_RothRidoutExponent.eq.Prod_MulPowProd_PowPowProd_PowSub.of.RothMvIndex
import Theorem.Fin.RothHasseEval0.eq.RothEval.of.RothCoeff
import Theorem.Fin.Sum_MulRothSCentered.eq.Zero.of.Ne.All_Gt_0
import Theorem.Fin.Mul2CardRothLowIndex.le.CardRothBox.of.Le_MulMul2Square.Gt_0.Gt_0.All_Gt_0
import Theorem.Int.RothFinsuppL1Neg.eq.RothFinsuppL1
import Lemma.MvPolynomial.RothMvHasse.eq.Monomial.of.RothMvIndex
import Theorem.Fin.RothCentered_RothFlip.eq.NegRothCentered.of.RothBox.All_Gt_0
import Theorem.Fin.EqRothLastIndex_Last.of.RothMvIndex
import Theorem.Fin.RothMvL1_CoeffRothLastEquiv.le.RothMvL1
import Theorem.Fin.InvolutiveRothRidoutBoxComplement
import Theorem.Fin.RothMvL1Add.le.AddRothSMvL1
import Lemma.MvPolynomial.Eval_AlgebraMapRothMvHasse_RothMvOfCoeff.eq.RothHasseEval.of.RothMvIndex.RothCoeff
import Theorem.Set.FiniteSetOfLeAbsQAndLeDen
import Theorem.Real.RpowDivMul.le.PowRpow.of.Le_Pow.Ge_0.Gt_0.Gt_0.Gt_0
import Lemma.Submodule.RothPolyRowDerivative.in.Span_XRothKronHasseJetRowsAdd_1.of.In_Span_XRothKronHasseJetRows
import Lemma.MvPolynomial.RothMvVanishesBelow_Map_AlgebraMapRothMvOfCoeff
import Lemma.Submodule.RothPolyRowDerivative.in.Span_XRothPolyJetRowsAdd_1.of.In_Span_XRothPolyJetRows
import Theorem.Polynomial.RothPolyL1_RothPowerCoord.le.PowAddRothPolyL1'1
import Lemma.MvPolynomial.RothMvVanishesBelow_MapAlgebraMap.of.All_EqEval_AlgebraMapFunRothMvHasse_0
import Theorem.Polynomial.IsPrimitiveSubMulCDenXCNum
import Theorem.Polynomial.Any_LtDivAndNeEvalHasseDeriv_MapAlgebraMap_0.of.Le_Rpow.Ne_0.GeDen_2.Gt_0.Gt_0
import Theorem.Polynomial.RothPolyL1.eq.Sum_NatAbsCoeff
import Lemma.Real.RpowMulAddSub.le.Pow_RothRidoutExponent.of.In_SupportRothMvHasse_RothMvOfCoeff.LeRothMvWeight.All_Le_RothWeightAndLeRothWeight_Sub.All_LeRpowDenPow.All_LeRpowDenPow.All_Le_PowDen.Ge_0.Ge_0.Ge_0.Gt_1.All_Gt_0.RothMvIndex.RothCoeff
import Theorem.Fin.EqRothMvHasse0
import Theorem.Fin.InjectiveRothBoxIndex
import Theorem.Fin.RothMvWeight.ge.Zero.of.RothMvIndex
import Lemma.Matrix.RothHasseEval_1.eq.Zero.of.EqMulVecRothAuxMatrix_0.RothCoeff.IsAlgebraic
import Theorem.Fin.RothRidoutComplement.eq.Sub.of.RothMvIndex
import Lemma.Fin.DegreeRothAuxTerm.lt.NatDegreeRothIntegralPolynomial.of.RothBox.IsAlgebraic
import Lemma.Rat.NatDegreeRothIntegralPolynomial.Gt_0.of.IsAlgebraic
import Theorem.Nat.Add_1.le.Pow2.of.Gt_0
import Theorem.Fin.RothMvVanishesBelowAdd
import Theorem.Polynomial.Eval.of.RothMvIndex
import Theorem.Polynomial.DvdPowSubMulCDenXCNum
import Theorem.Fin.CoeffRothLastSlice.eq.CoeffRothLastIndex.of.RothMvIndex
import Theorem.Real.Prod_PowAbsSub.le.RpowMulNegRothMvWeight.of.All_LtAbsSub_Div1RpowDen.All_Le_PowDen.Gt_0.Ge_0.All_Gt_0
import Lemma.Real.Finite.of.LtSum_Add_Add2.All_Ge_0.All_Ge_0.Le_1.Gt_0.IsAlgebraic
import Theorem.Polynomial.EvalRothPowerCoord.eq.Pow.of.EqEval_0
import Lemma.Real.NormRothRidoutAuxMatrix.le.PowMul_2RothCoordinateBaseSum
import Theorem.Fin.RothMvL1.Gt_0.of.Ne_0
import Theorem.Fin.Any_LtRothMvWeightAndNeEvalRothMvHasse_0.of.NotRothMvVanishesBelow
import Theorem.Fin.GetRothRidoutBoxComplement.eq.Sub.of.RothBox
import Theorem.Fin.RothMvHasse.eq.SMul.of.RothMvIndex
import Theorem.Polynomial.Det_PowDerivativeGetVal.ne.Zero.of.LinearIndependent
import Theorem.Polynomial.PowDen.le.NatAbsLeadingCoeff.of.Ne_0
import Theorem.Fin.EqRothFlip.of.RothBox.Ne
import Lemma.Fin.AbsEval.le.MulRothMvL1Prod_PowMax
import Theorem.Fin.RothWeight.eq.AddRothCenteredSumDiv_2.of.RothBox
import Lemma.Fin.NatAbsRothAuxMatrix.le.PowMul2RothCoordinateBaseSum.of.RothBox
import Theorem.Fin.RothCentered_RothFlip.eq.RothCentered.of.RothBox.Ne
import Theorem.Fin.EqRothLastIndexCastSucc.of.RothMvIndex
import Theorem.Fin.RothMvL1_RothMvOfCoeff.le.Sum_NatAbs.of.RothCoeff
import Lemma.Fin.RothRidoutAuxMatrix_CastSuccCastSucc.eq.RothAuxMatrix.of.RothBox.RothLowIndex
import Lemma.Polynomial.Eval.eq.MulPowS.of.Le.IsAlgebraic
import Theorem.Fin.RothPolyL1.le.MulPow2AddAddMulKMulKSMulKSumPowRothMvL1K.of.Gt_0
import Theorem.Polynomial.RothPolyL1Add.le.AddRothSPolyL1
import Theorem.Submodule.Any_And_All_In.of.All_In_Span.NeDet_0
import Theorem.Polynomial.RothPolyL1_Sub.le.AddRothSPolyL1
import Theorem.Nat.Injective_I
import Theorem.Fin.RothMvVanishesBelow_Sub
import Theorem.Polynomial.RothPolyL1_C.eq.NatAbs
import Theorem.Fin.RothDegreeBound_RothMvOfCoeff.of.RothCoeff
import Theorem.Fin.RothKronecker.ne.Zero.of.Ne_0.Gt_1
import Theorem.Fin.RothDegreeBoundAdd
import Theorem.Real.Mul.lt.Rpow.of.LtAdd.Le_Rpow.Le_Rpow.Ge_0.Gt_1
import Theorem.Real.FiniteSetOfLtAbsSub_Div1RpowDen.of.NotLiouvilleWith.Gt_0.Irrational
import Theorem.Fin.RothDegreeBoundOver_RothMvHasse.of.RothMvIndex
import Theorem.Int.RothFinsuppL1CoeffMul.le.MulRothSFinsuppL1Coeff
import Theorem.Fin.EqRothLastIndex.of.RothMvIndexAdd_1
import Lemma.Fin.Ne_0AndRothVanishesBelowAndMul_SubDiv1'2.le.RothWeightAndRothWeight.le.Sub_Mul_SubDiv1'2AndRothMvL1.le.PowMul8RothCoordinateBaseSum.of.LeAddNatDegreeRothIntegralPolynomial2MulMul2Square.LtAddNatDegreeRothIntegralPolynomial2MulMul4Square.Lt_Div1'2.Gt_0.Gt_0.All_Gt_0.IsAlgebraic
import Theorem.Fin.EqRothBoxIndex.of.RothBox
import Theorem.Fin.RothMvVanishesBelowNeg
import Theorem.Real.All_LeAndAntitoneAndAll_Le_MulAndAll_LePowAndSum.le.Mul2AndAll_LePowRpow.of.GeMul_2.LeMul_1.Gt_0.Le.Gt_0.All_LtPow.Monotone.All_Ge_2
import Theorem.Fin.RothKronecker.eq.Sum_Monomial
import Theorem.Fin.RothMvL1Mul.le.MulRothSMvL1
import Lemma.MvPolynomial.AbsCoeffRothTranslate.le.MulMulPow4SumRothMvL1Prod_PowMax.of.RothMvIndex
import Theorem.Fin.RothMvL1Det.le.MulFactorialPow.of.All_LeRothMvL1
import Theorem.Polynomial.IsPrimitivePow.of.IsPrimitive
import Theorem.Polynomial.Eval_LastCasesRothMvHasse_RothLastIndex.eq.MulEvalRothMvHasseEvalHasseDeriv.of.RothMvIndex.EqRothLastEquiv_MulCMapC
import Lemma.Fin.CoeffRothAuxCombination.eq.Sum_MulCoeffRothAuxTerm.of.RothCoeff.RothBox
import Theorem.Real.Any_All_Le_Rpow.of.Gt_0
import Theorem.Fin.RothMvL1_Prod.le.Prod_RothMvL1
import Theorem.Polynomial.RothLastEquiv.eq.MulCMap.of.EqRothLastEquiv_Sum_MulCMapC
import Lemma.Real.AbsEval.le.MulMulMulPow8SumRothMvL1Prod_PowMaxRpow.of.All_LeProd_PowAbsSub_RpowMulNegRothMvWeight.Ge_1.Ge_0.RothMvIndex.All_Gt_0
import Theorem.Int.RothFinsuppL1Add.le.AddRothSFinsuppL1
import Theorem.Fin.RothMvL1Neg.eq.RothMvL1
import Theorem.Polynomial.RothPolyRowDerivative_RothPolyDerivativeRow.eq.RothPolyDerivativeRowAdd_1
import Theorem.Fin.RothMvWeight.le.DivRothMvOrder.of.All_Le.Gt_0.RothMvIndex
import Theorem.Fin.RothMvWeight.eq.AddRothMvWeightDiv.of.RothMvIndex
import Lemma.Real.RpowMulSum_AddSub.le.Prod_Pow.of.All_Any_Eq_RothRidoutExponent.LeRothMvWeight.All_Le_RothWeightAndLeRothWeight_Sub.All_LeRpowDenPow.All_LeRpowDenPow.All_Le_PowDen.All_Ge_0.All_Ge_0.Ge_0.Gt_1.All_Gt_0.RothMvIndex.RothCoeff
import Theorem.Polynomial.DegreeRothPowerCoord.lt.NatDegree.of.GtNatDegree_0.Monic
import Theorem.Polynomial.CoeffRothLastEquiv_RothMvHasse_RothLastIndex.eq.RothMvHasse_CoeffHasseDerivRothLastEquiv.of.RothMvIndex
import Theorem.Fin.RothMvL1.eq.Sum_NatAbsCoeff
import Theorem.Fin.RothMvVanishesBelow_MulDiv.of.All_Gt_0.Gt_0
import Theorem.Fin.RothDegreeBound_ProdMulCard.of.All_RothDegreeBound
import Theorem.Fin.RothMvVanishesBelow_Max
import Theorem.Fin.CoeffRothMvHasse.eq.MulProd_ChooseExtAddCoeffAdd.of.RothMvIndex
import Theorem.Polynomial.Any_And_Le_AddNatDegree1AndAll_Eq_CoeffAndAll_LeNatDegreeAndLinearIndependentAndLinearIndependentAndEq_Sum_MulCMap.of.Ne_0
import Lemma.Real.RothDenProduct.le.RpowMul_Add1.of.All_LePowDen_RpowAdd1.Ge_0
import Lemma.Matrix.RothAuxCombination1.eq.Zero.of.EqMulVecRothAuxMatrix_0.RothCoeff.IsAlgebraic
import Theorem.Fin.AddMul_RothMvWeightMul_RothMvWeight_RothRidoutComplement.eq.Sum_AddDivMulDivMul_Sub.of.All_Le.RothMvIndex
import Theorem.Fin.RothDegreeBoundOver
import Theorem.Fin.CoeffRothTranslateM.eq.EvalRothMvHasse
import Theorem.Real.MulPowS.le.RpowMulMulAdd_Mul.of.Le_MulMul.Le_RpowMul.Le_Rpow.Ge_0.Ge
import Theorem.Fin.RothLastSlice0.ne.Zero.of.Ne_0
import Theorem.Fin.RothMvVanishesBelowSMul
import Theorem.Fin.RothMvWeightAdd.eq.AddRothSMvWeight.of.RothMvIndex
import Theorem.Fin.Sum_SquareRothCentered.le.DivCardRothBox4.of.All_Gt_0
import Lemma.Fin.Div_RothDenProduct.le.AbsEval.of.NeEval_AlgebraMapFun_0
import Theorem.Fin.Eq.of.EqRothKroneckerEncode.All_Lt.All_Lt.Gt_1
import Theorem.Real.Any_Lt_Den.of.Infinite.Subset_SetOfLtAbsSub_Div1RpowDen.Gt_0
import Theorem.Fin.RothDegreeBoundOver_Map
import Theorem.Fin.RothKronecker_X.eq.PowXPow
import Theorem.Fin.RothDegreeBound_RothHasseDetMul
import Lemma.Fin.RothRidoutAuxMatrix_LastAddNatDegreeRothIntegralPolynomial1.eq.Eq_RothRidoutBoxComplement1.of.RothBox
import Theorem.Polynomial.RothPolyL1Neg.eq.RothPolyL1
import Theorem.Real.Pow.le.RpowMul.of.LeSquare_Rpow.Le_Mul2.Ge_0.Ge_1
import Lemma.MvPolynomial.FinSuccEquiv.eq.Map
import Theorem.Fin.RothDegreeBoundOver_RothTranslate
import Theorem.Real.Any_LtAbsSub_Div1RpowDenAndLt_Den.of.InfiniteSetOfLtAbsSub_Div1RpowDen.Gt_0
import Theorem.Int.NatAbs.le.RothFinsuppL1
import Theorem.Fin.RothMvVanishesBelow0
import Theorem.Fin.EvalRothTranslateM.eq.Eval_Add
import Lemma.Submodule.RothPolyDerivativeRow_RothKronecker.in.Span_XRothKronHasseJetRows
import Lemma.Fin.NatAbsRothRidoutAuxMatrix.le.PowMul2RothCoordinateBaseSum.of.RothBox
import Theorem.Fin.DivSquare64.le.DivSum_Max_Sub.of.Le_Add_1.Gt_0.GeMul_16.Gt_0.Le_Div_4.Le_1.Gt_0
import Theorem.Polynomial.RothPolyL1.le.MulAddNatDegree1.of.All_LeNatAbsCoeff
import Theorem.Real.Any_Ge_2AndAll_Le2Rpow.of.Gt_0
import Theorem.Fin.RothMvVanishesBelow_Sub.of.RothMvIndex
import Lemma.Polynomial.Eval_MapRothIntPolynomialAlgebraMap.eq.Zero
import Theorem.Real.AbsSub.le.RpowDivNeg.of.LtAbsSub_Div1RpowDen.Le_PowDen.Gt_0.Ge_0.Gt_0
import Theorem.Polynomial.DvdPowSubXC.of.All_EqEvalHasseDeriv_0
import Theorem.Fin.CardRothLowIndex.lt.CardRothBox.of.Lt_MulMul4Square.Gt_0.Gt_0.All_Gt_0
import Theorem.Real.Abs.le.AddAbs1.of.LtAbsSub_Div1RpowDen.Gt_0
import Lemma.Real.All_Eval_AlgebraMapFunRothMvHasse.eq.Zero.of.LeRothMvWeight.Mul_MulMulPow8SumRothMvL1Prod_PowMax.lt.Rpow.All_Any_LeRpowAndDvd_RothClearEval_RothMvHasse.All_LeProd_PowAbsSub_RpowMulNegRothMvWeight.Gt_1.Ge_0.All_Gt_0.RothMvIndex
import Theorem.Fin.RothMvHasse_Sum.eq.Sum_RothMvHasse.of.RothMvIndex
import Theorem.Nat.RothLastIndex.eq.AddRothSLastIndex.of.RothMvIndex
import Theorem.Fin.InvolutiveRothFlip
import Theorem.Fin.CardSupport.le.CardRothBox
import Theorem.Polynomial.Any_And_Det_PowDerivative.ne.Zero.of.LinearIndependent
import Theorem.Fin.RothMvHasse.eq.Zero.of.Lt
import Theorem.Polynomial.Wronskian.ne.Zero.of.NeNatDegree_NatDegree.Ne_0.Ne_0
import Mathlib.RingTheory.Algebraic.Integral


namespace MathlibExtTest.NumberTheory.RothAuxiliary

open MathlibExt.NumberTheory.RothAuxiliary

-- The shared theorem handles a positive numerator-divisibility weight at the prime `2`.
example : Set.Finite {q : ℚ |
    |Real.sqrt 2 - (q : ℝ)| <
        1 / Real.rpow (q.den : ℝ) (9 / 4 : ℝ) ∧
      ∃ a : ℕ,
        ((2 ^ a : ℕ) : ℤ) ∣ q.num ∧
          Real.rpow (q.den : ℝ) (1 / 4 : ℝ) ≤ (2 : ℝ) ^ a} := by
  have hsqrt : IsAlgebraic ℚ (Real.sqrt 2) := by
    apply IsIntegral.isAlgebraic
    refine ⟨Polynomial.X ^ 2 - Polynomial.C (2 : ℚ),
      Polynomial.monic_X_pow_sub_C _ (by norm_num), ?_⟩
    simp [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hcore := finite_of_divisible_approximations
    (Real.sqrt 2) hsqrt
    (1 / 2 : ℝ) (by norm_num) (by norm_num)
    (Finset.univ : Finset (Fin 1)) (fun _ ↦ 2)
    (fun _ ↦ (1 / 4 : ℝ)) (fun _ ↦ 0)
    (by simp) (by simp) (by norm_num)
  refine hcore.subset ?_
  intro q hq
  rcases hq with ⟨happrox, a, hdiv, hlarge⟩
  refine ⟨?_, (fun _ ↦ a), (fun _ ↦ 0), ?_⟩
  · norm_num at happrox ⊢
    exact happrox
  · refine ⟨?_, by simp, ?_⟩
    · simpa using hdiv
    · intro l hl
      refine ⟨?_, by norm_num⟩
      simpa using hlarge

end MathlibExtTest.NumberTheory.RothAuxiliary
