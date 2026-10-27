import Mathlib
import Initialize.Tactic.Attr.Basic
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
import Lemma.Real.All_LeAndAntitoneAndAll_Le_MulAndAll_LePowAndSum.le.Mul2AndAll_LePowRpow.of.GeMul_2.LeMul_1.Gt_0.Le.Gt_0.All_LtPow.Monotone.All_Ge_2
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
import Lemma.Fin.RothMvHasse_Sum.eq.Sum_RothMvHasse.of.RothMvIndex
import Lemma.Nat.RothLastIndex.eq.AddRothSLastIndex.of.RothMvIndex
import Lemma.Fin.InvolutiveRothFlip
import Lemma.Fin.CardSupport.le.CardRothBox
import Lemma.Polynomial.Any_And_Det_PowDerivative.ne.Zero.of.LinearIndependent
import Lemma.Fin.RothMvHasse.eq.Zero.of.Lt
import Lemma.Polynomial.Wronskian.ne.Zero.of.NeNatDegree_NatDegree.Ne_0.Ne_0
import Lemma.MvPolynomial.RothHelpers
import Lemma.MvPolynomial.EvalAlgebraMap.eq.Eval_AlgebraMapFun
import Lemma.Real.AbsEval.le.MulMulMulPow8SumRothMvL1Prod_PowMaxRpow.of.All_LeProd_PowAbsSub_RpowMulNegRothMvWeight.Ge_1.Ge_0.RothMvIndex.All_Gt_0
open MathlibExt.NumberTheory.RothAuxiliary
open MvPolynomial Real
set_option maxHeartbeats 800000


private lemma denProduct_mul_eval₂_h
  {m : ℕ}
  (P : MvPolynomial (Fin m) ℤ)
  (q : Fin m → ℚ)
  (r : Fin m → ℕ)
-- given
  (hP : rothDegreeBound P r) :
-- imply
  (rothDenProduct q r : ℚ) *
      MvPolynomial.eval₂ (algebraMap ℤ ℚ) q P =
    (rothClearEval P q r : ℚ) := by
-- proof
  classical
  unfold rothDenProduct rothClearEval
  rw [MvPolynomial.eval₂_eq']
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hcoord : ∀ h,
      ((q h).den : ℚ) ^ r h * q h ^ d h =
        ((((q h).num ^ d h * ((q h).den : ℤ) ^ (r h - d h)) : ℤ) : ℚ) := by
    intro h
    have hcast : ((((q h).num ^ d h * ((q h).den : ℤ) ^ (r h - d h)) : ℤ) : ℚ) =
        ((q h).num : ℚ) ^ d h * ((q h).den : ℚ) ^ (r h - d h) := by
      push_cast
      rfl
    rw [hcast]
    calc
      _ = ((q h).den : ℚ) ^ r h *
            (((q h).num : ℚ) / (q h).den) ^ d h := by
        rw [(q h).num_div_den]
      _ = ((q h).num : ℚ) ^ d h *
          ((q h).den : ℚ) ^ (r h - d h) := by
        rw [div_pow]
        have hden : ((q h).den : ℚ) ≠ 0 := by
          exact_mod_cast (q h).den_nz
        field_simp
        have hp : ((q h).den : ℚ) ^ r h =
            ((q h).den : ℚ) ^ d h *
              ((q h).den : ℚ) ^ (r h - d h) := by
          rw [← pow_add, Nat.add_sub_of_le (hP d hd h)]
        rw [hp]
        ring
  have hfactor : (∏ h, ((q h).den : ℚ) ^ r h) *
      ((algebraMap ℤ ℚ) (P.coeff d) * ∏ h, q h ^ d h) =
      (P.coeff d : ℚ) *
        ((∏ h, ((q h).den : ℚ) ^ r h) * ∏ h, q h ^ d h) := by
    rw [algebraMap_int_eq, Int.coe_castRingHom]
    dsimp only
    ring
  rw [hfactor]
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro h _
  simpa only [Int.cast_mul, Int.cast_pow, Int.cast_natCast] using hcoord h

private lemma eval₂_rational_lower_bound_h
  {m : ℕ}
  (P : MvPolynomial (Fin m) ℤ)
  (q : Fin m → ℚ)
  (r : Fin m → ℕ)
  (G : ℕ)
-- given
  (hP : rothDegreeBound P r)
  (hne : MvPolynomial.eval₂ (algebraMap ℤ ℝ) (fun h ↦ (q h : ℝ)) P ≠ 0)
  (hG : (G : ℤ) ∣ rothClearEval P q r) :
-- imply
  (G : ℝ) / (rothDenProduct q r : ℝ) ≤
    |MvPolynomial.eval₂ (algebraMap ℤ ℝ) (fun h ↦ (q h : ℝ)) P| := by
-- proof
  let v : ℚ := MvPolynomial.eval₂ (algebraMap ℤ ℚ) q P
  let D := rothDenProduct q r
  let z := rothClearEval P q r
  have hDpos : 0 < D := by
    dsimp [D, rothDenProduct]
    exact Finset.prod_pos fun h _ ↦ pow_pos (q h).pos _
  have hvCast :
    (v : ℝ) =
        MvPolynomial.eval₂ (algebraMap ℤ ℝ) (fun h ↦ (q h : ℝ)) P := by
    simpa [v] using EvalAlgebraMap.eq.Eval_AlgebraMapFun (P := P) (q := q)
  have hv : v ≠ 0 := by
    intro hz
    apply hne
    rw [← hvCast, hz]
    norm_num
  have heqQ : (D : ℚ) * v = (z : ℚ) := denProduct_mul_eval₂_h P q r hP
  have hz : z ≠ 0 := by
    intro hz0
    rw [hz0, Int.cast_zero] at heqQ
    exact hv ((mul_eq_zero.mp heqQ).resolve_left (by exact_mod_cast (ne_of_gt hDpos)))
  have hGnat : G ≤ z.natAbs := by
    simpa [z] using Int.natAbs_le_of_dvd_ne_zero hG hz
  have hGabs : (G : ℝ) ≤ |(z : ℝ)| := by
    have habs : |(z : ℝ)| = (z.natAbs : ℝ) := by
      rw [← Int.cast_abs]
      norm_num
    rw [habs]
    exact_mod_cast hGnat
  have heqR :
    (D : ℝ) *
        MvPolynomial.eval₂ (algebraMap ℤ ℝ) (fun h ↦ (q h : ℝ)) P =
          (z : ℝ) := by
    rw [← hvCast]
    exact_mod_cast heqQ
  have hmul :
    (G : ℝ) ≤
        (D : ℝ) *
          |MvPolynomial.eval₂ (algebraMap ℤ ℝ) (fun h ↦ (q h : ℝ)) P| := calc
      _ ≤ |(z : ℝ)| := hGabs
      _ = |(D : ℝ) *
          MvPolynomial.eval₂ (algebraMap ℤ ℝ) (fun h ↦ (q h : ℝ)) P| :=
        congrArg abs heqR.symm
      _ = (D : ℝ) *
          |MvPolynomial.eval₂ (algebraMap ℤ ℝ) (fun h ↦ (q h : ℝ)) P| := by
        rw [abs_mul, abs_of_pos (by exact_mod_cast hDpos)]
  rwa [div_le_iff₀ (by exact_mod_cast hDpos), mul_comm]

/--
[roth_ridout_hasse_eq_zero_at_rational_of_taylor_bound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ}
  (P : MvPolynomial (Fin m) ℤ)
  (x : Fin m → ℝ)
  (q : Fin m → ℚ)
  (r : Fin m → ℕ)
  (T a Q θ s : ℝ)
-- given
  (hr : ∀ h, 0 < r h)
  (hP : rothDegreeBound P r)
  (hvan : rothMvVanishesBelow
    (MvPolynomial.map (algebraMap ℤ ℝ) P) x r T)
  (ha : 0 ≤ a)
  (hQ : 1 < Q)
  (herr : ∀ l : RothMvIndex m,
    ∏ h, |(q h : ℝ) - x h| ^ l h ≤
      Real.rpow Q (-a * rothMvWeight r l))
  (hdiv : ∀ i : RothMvIndex m, rothMvWeight r i ≤ θ →
    ∃ G : ℕ, Real.rpow Q s ≤ G ∧
      (G : ℤ) ∣ rothClearEval (rothMvHasse i P) q r)
  (hmaster : (rothDenProduct q r : ℝ) *
      (((8 ^ (∑ h, r h) * rothMvL1 P : ℕ) : ℝ) *
        ∏ h, max 1 |x h| ^ r h) <
    Real.rpow Q (s + a * (T - θ))) :
-- imply
  ∀ i : RothMvIndex m, rothMvWeight r i ≤ θ →
    MvPolynomial.eval₂ (algebraMap ℤ ℝ) (fun h ↦ (q h : ℝ))
      (rothMvHasse i P) = 0 := by
-- proof
  intro i hi
  by_contra hne
  let Pi := rothMvHasse i P
  let K : ℝ := ((8 ^ (∑ h, r h) * rothMvL1 P : ℕ) : ℝ) *
    ∏ h, max 1 |x h| ^ r h
  let b := a * (T - rothMvWeight r i)
  have hPiDeg : rothDegreeBound Pi r :=
    rothDegreeBoundOver_hasse_h (show rothDegreeBoundOver P r from hP) i
  obtain ⟨G, hGs, hGdvd⟩ := hdiv i hi
  have hlower :=
    eval₂_rational_lower_bound_h Pi q r G hPiDeg hne hGdvd
  have hupper :=
    AbsEval.le.MulMulMulPow8SumRothMvL1Prod_PowMaxRpow.of.All_LeProd_PowAbsSub_RpowMulNegRothMvWeight.Ge_1.Ge_0.RothMvIndex.All_Gt_0
      P x (fun h ↦ (q h : ℝ)) r i T a Q hr hP hvan ha hQ.le herr
  have hDpos : (0 : ℝ) < rothDenProduct q r := by
    exact_mod_cast (show 0 < rothDenProduct q r by
      unfold rothDenProduct
      exact Finset.prod_pos fun h _ ↦ pow_pos (q h).pos _)
  have hGmul :
    (G : ℝ) ≤
        (rothDenProduct q r : ℝ) *
          |MvPolynomial.eval₂ (algebraMap ℤ ℝ) (fun h ↦ (q h : ℝ)) Pi| := calc
      _ =
          (rothDenProduct q r : ℝ) *
            ((G : ℝ) / rothDenProduct q r) := by field_simp
      _ ≤
          (rothDenProduct q r : ℝ) *
            |MvPolynomial.eval₂ (algebraMap ℤ ℝ) (fun h ↦ (q h : ℝ)) Pi| :=
        mul_le_mul_of_nonneg_left hlower hDpos.le
  have hbase :
    Real.rpow Q s ≤
        (rothDenProduct q r : ℝ) *
          |MvPolynomial.eval₂ (algebraMap ℤ ℝ) (fun h ↦ (q h : ℝ)) Pi| :=
    hGs.trans hGmul
  have hb : s + a * (T - θ) ≤ s + b := by
    dsimp [b]
    nlinarith
  have hQpos : 0 < Q := lt_trans (by norm_num) hQ
  have hKb :
    (rothDenProduct q r : ℝ) * K < Real.rpow Q (s + b) :=
    hmaster.trans_le (Real.rpow_le_rpow_of_exponent_le hQ.le hb)
  have hinv :
    Real.rpow Q (s + b) * Real.rpow Q (-b) = Real.rpow Q s := calc
      _ =
          Real.rpow Q ((s + b) + -b) :=
        (Real.rpow_add hQpos (s + b) (-b)).symm
      _ = Real.rpow Q s := by ring_nf
  have hle :
    (rothDenProduct q r : ℝ) *
          |MvPolynomial.eval₂ (algebraMap ℤ ℝ) (fun h ↦ (q h : ℝ)) Pi| ≤
        (rothDenProduct q r : ℝ) * (K * Real.rpow Q (-b)) := by
    gcongr
    simpa [Pi, K, b, mul_assoc] using hupper
  have hsmall :
    (rothDenProduct q r : ℝ) * (K * Real.rpow Q (-b)) <
        Real.rpow Q s := calc
      _ = ((rothDenProduct q r : ℝ) * K) * Real.rpow Q (-b) := by ring
      _ < Real.rpow Q (s + b) * Real.rpow Q (-b) := by
        gcongr
        exact Real.rpow_pos_of_pos hQpos _
      _ = Real.rpow Q s := hinv
  have := not_lt_of_ge (hbase.trans hle) hsmall
  exact this


-- created on 2026-10-21
