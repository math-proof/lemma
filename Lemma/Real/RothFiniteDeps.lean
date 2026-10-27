import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.NumberTheory.RothAuxiliary.Part7
import Lemma.Int.RothFinsuppL1_Single.eq.NatAbs
import Lemma.Finset.RothFinsuppL1_Sum.le.Sum_RothFinsuppL1
import Lemma.Fin.RothKroneckerEncode.eq.Add_Mul_RothKroneckerEncode
import Lemma.Fin.RothWeight_RothRidoutBoxComplement.eq.Sub_RothWeight.of.All_Gt_0.RothBox
import Lemma.Fin.CoeffCoeffRothLastEquiv.eq.CoeffRothLastIndex.of.RothMvIndex
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
import Lemma.Real.Prod_MulPowRpowDenPowRpowDenSub.le.Pow_RothRidoutExponent.of.All_LeRpowDenPow.All_LeRpowDenPow.RothMvIndex
import Lemma.Polynomial.LinearIndependent_J.of.LinearIndependent
import Lemma.MvPolynomial.CoeffGetFinSuccEquivRothMvHasse_Cons.eq.RothMvHasse_CoeffHasseDerivGetFinSuccEquiv
import Lemma.Submodule.DetUpdateRow.ne.Zero.of.In_Span.NeDet_0
import Lemma.MvPolynomial.CoeffRothTranslate_Eval_C.eq.Sum_MulCoeffRothTranslate_CoeffPow.of.RothMvIndex
import Lemma.Polynomial.Eval.eq.MulPowLeadingCoeffRothIntPolynomialSumRothHasseEval.of.RothCoeff.RothBox.IsAlgebraic
import Lemma.Fin.RothTermDegree.le.Sum.of.RothBox
import Lemma.Polynomial.NatAbsCoeff.le.RothPolyL1
import Lemma.Fin.Nonempty_RothIntegralFactorData.of.RothDeterminantData
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
import Lemma.Fin.RothRidoutComplement.eq.Sub.of.RothMvIndex
import Lemma.Fin.DegreeRothAuxTerm.lt.NatDegreeRothIntegralPolynomial.of.RothBox.IsAlgebraic
import Lemma.Rat.NatDegreeRothIntegralPolynomial.Gt_0.of.IsAlgebraic
import Lemma.Nat.Add_1.le.Pow2.of.Gt_0
import Lemma.Fin.RothMvVanishesBelowAdd
import Lemma.Polynomial.Eval.of.RothMvIndex
import Lemma.Polynomial.DvdPowSubMulCDenXCNum
import Lemma.Fin.CoeffRothLastSlice.eq.CoeffRothLastIndex.of.RothMvIndex
import Lemma.Real.Finite.of.LtSum_Add_Add2.All_Ge_0.All_Ge_0.Le_1.Gt_0.IsAlgebraic
import Lemma.Polynomial.EvalRothPowerCoord.eq.Pow.of.EqEval_0
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
import Lemma.Fin.AddMul_RothMvWeightMul_RothMvWeight_RothRidoutComplement.eq.Sum_AddDivMulDivMul_Sub.of.All_Le.RothMvIndex
import Lemma.Fin.RothDegreeBoundOver
import Lemma.Fin.CoeffRothTranslateM.eq.EvalRothMvHasse
import Lemma.Fin.RothLastSlice0.ne.Zero.of.Ne_0
import Lemma.Fin.RothMvVanishesBelowSMul
import Lemma.Fin.RothMvWeightAdd.eq.AddRothSMvWeight.of.RothMvIndex
import Lemma.Fin.Sum_SquareRothCentered.le.DivCardRothBox4.of.All_Gt_0
import Lemma.Fin.Div_RothDenProduct.le.AbsEval.of.NeEval_AlgebraMapFun_0
import Lemma.Fin.Eq.of.EqRothKroneckerEncode.All_Lt.All_Lt.Gt_1
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
import Lemma.MvPolynomial.EvalAlgebraMap.eq.Eval_AlgebraMapFun
import Lemma.Real.RothCoordinateBase.Gt_0
import Lemma.Real.RothPolyL1_RothScaledPowerCoord.le.PowRothCoordinateBase.of.Le
import Lemma.Real.NormRothRidoutAuxMatrix.le.PowMul_2RothCoordinateBaseSum
import Lemma.Real.Any_Ge_2AndAll_Le2Rpow.of.Gt_0
import Lemma.Real.Any_All_Le_Rpow.of.Gt_0
import Lemma.Real.MulPowS.le.RpowMulMulAdd_Mul.of.Le_MulMul.Le_RpowMul.Le_Rpow.Ge_0.Ge
import Lemma.Real.RpowMul.le.RpowMul.of.LePow_Pow.Ge_0
import Lemma.Real.All_LeAndAntitoneAndAll_Le_MulAndAll_LePowAndSum.le.Mul2AndAll_LePowRpow.of.GeMul_2.LeMul_1.Gt_0.Le.Gt_0.All_LtPow.Monotone.All_Ge_2
import Lemma.Real.RothDenProduct.le.RpowMul_Add1.of.All_LePowDen_RpowAdd1.Ge_0
import Lemma.Real.Pow.le.RpowMul.of.LeSquare_Rpow.Le_Mul2.Ge_0.Ge_1
import Lemma.Real.Mul.lt.Rpow.of.LtAdd.Le_Rpow.Le_Rpow.Ge_0.Gt_1
import Lemma.Real.Prod_PowAbsSub.le.RpowMulNegRothMvWeight.of.All_LtAbsSub_Div1RpowDen.All_Le_PowDen.Gt_0.Ge_0.All_Gt_0
import Lemma.Real.Any_LeRpowMulSum_AddSubAndDvd_RothClearEval_RothMvHasse_RothMvOfCoeff.of.LeRothMvWeight.All_Le_RothWeightAndLeRothWeight_Sub.All_LeRpowDenPow.All_LeRpowDenPow.All_DvdProd_Pow_Den.All_DvdProd_PowNum.All_Le_PowDen.All_Ge_0.All_Ge_0.Ge_0.Gt_1.All_Gt_0.RothMvIndex.RothCoeff
import Lemma.Real.All_Eval_AlgebraMapFunRothMvHasse.eq.Zero.of.LeRothMvWeight.Mul_MulMulPow8SumRothMvL1Prod_PowMax.lt.Rpow.All_Any_LeRpowAndDvd_RothClearEval_RothMvHasse.All_LeProd_PowAbsSub_RpowMulNegRothMvWeight.Gt_1.Ge_0.All_Gt_0.RothMvIndex
import Lemma.Real.Any_Lt_Den.of.Infinite.Subset_SetOfLtAbsSub_Div1RpowDen.Gt_0
import Lemma.Matrix.MulVecRothAuxMatrix.eq.Zero.of.EqMulVecRothRidoutAuxMatrix_0.RothCoeff
import Lemma.Matrix.Mul_SubDiv1'2.le.RothWeightAndRothWeight.le.Sub_Mul_SubDiv1'2.of.Ne_0.RothBox.EqMulVecRothRidoutAuxMatrix_0.All_Gt_0.RothCoeff
import Lemma.Matrix.RothHasseEval_1.eq.Zero.of.EqMulVecRothAuxMatrix_0.RothCoeff.IsAlgebraic
import Lemma.Matrix.RothAuxCombination1.eq.Zero.of.EqMulVecRothAuxMatrix_0.RothCoeff.IsAlgebraic
import Lemma.Matrix.Eq_0.of.EqMulVecRothRidoutAuxMatrix_0.RothCoeff
open MathlibExt.NumberTheory.RothAuxiliary
open scoped BigOperators nonZeroDivisors Polynomial
open Real Matrix
set_option maxHeartbeats 999999


attribute [local instance] Matrix.seminormedAddCommGroup

/-!
Private helper lemmas for finite_of_divisible_approximations, inlined from sympy RothAuxiliary.
-/

lemma rothMvHasse_monomial_h {m : ℕ} {R : Type*} [CommSemiring R]
    (i j : RothMvIndex m) (c : R) :
    rothMvHasse i (MvPolynomial.monomial j c) =
      MvPolynomial.monomial (j - i) ((∏ h, (Nat.choose (j h) (i h) : R)) * c) := by
  simp [rothMvHasse]

lemma rothMvHasse_zero_h {m : ℕ} {R : Type*} [CommSemiring R]
    (i : RothMvIndex m) : rothMvHasse i (0 : MvPolynomial (Fin m) R) = 0 := by
  simp [rothMvHasse]

lemma rothMvHasse_zero_index_h {m : ℕ} {R : Type*} [CommSemiring R]
    (P : MvPolynomial (Fin m) R) : rothMvHasse 0 P = P := by
  classical
  unfold rothMvHasse
  calc
    _ = P.coeff.sum (fun j c ↦ MvPolynomial.monomial j c) := by
      apply Finsupp.sum_congr
      intro j _
      congr 2
      · ext h
        simp
      · simp
    _ = P := by
      rw [Finsupp.sum]
      simpa [MvPolynomial.support] using MvPolynomial.support_sum_monomial_coeff P

lemma rothMvHasse_coeff_h {m : ℕ} {R : Type*} [CommSemiring R]
    (i k : RothMvIndex m) (P : MvPolynomial (Fin m) R) :
    (rothMvHasse i P).coeff k =
      (∏ h, (Nat.choose ((k + i) h) (i h) : R)) * P.coeff (k + i) := by
  classical
  unfold rothMvHasse
  rw [Finsupp.sum, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single (k + i)]
  · have hki : k + i - i = k := by
      ext h
      simp
    simp only [hki, ite_true]
  · intro j hj hne
    split_ifs with heq
    · by_cases hle : i ≤ j
      · exfalso
        apply hne
        ext h
        have heqh := congrArg (fun x : RothMvIndex m ↦ x h) heq
        have hleh := hle h
        simp only [Finsupp.add_apply]
        exact (tsub_eq_iff_eq_add_of_le hleh).mp heqh
      · obtain ⟨h, hh⟩ := not_forall.mp hle
        push Not at hh
        have hz : (Nat.choose (j h) (i h) : R) = 0 := by
          simp [Nat.choose_eq_zero_of_lt hh]
        rw [Finset.prod_eq_zero (Finset.mem_univ h) hz, zero_mul]
    · simp
  · intro hnot
    rw [Finsupp.notMem_support_iff.mp hnot]
    simp

lemma rothMvHasse_eval_zero_h {m : ℕ} {R : Type*} [CommSemiring R]
    (P : MvPolynomial (Fin m) R) (i : RothMvIndex m) :
    MvPolynomial.eval (0 : Fin m → R) (rothMvHasse i P) = P.coeff i := by
  rw [MvPolynomial.eval_zero]
  change (rothMvHasse i P).coeff 0 = P.coeff i
  rw [rothMvHasse_coeff_h]
  simp

lemma roth_choose_comp_h (l i j : ℕ) :
    (l + j).choose j * (l + j + i).choose i =
      (i + j).choose i * (l + (i + j)).choose (i + j) := by
  have h := Nat.choose_mul (n := l + j + i) (k := i + j) (s := i)
    (Nat.le_add_right i j)
  have hsub : l + j + i - i = l + j := by omega
  rw [hsub] at h
  have hk : i + j - i = j := by omega
  rw [hk] at h
  have htotal : l + j + i = l + (i + j) := by omega
  rw [htotal] at h
  rw [htotal]
  simpa only [mul_comm] using h.symm

lemma rothMvHasse_comp_h {m : ℕ} {R : Type*} [CommSemiring R]
    (P : MvPolynomial (Fin m) R) (i j : RothMvIndex m) :
    rothMvHasse j (rothMvHasse i P) =
      (∏ h, (Nat.choose ((i + j) h) (i h) : R)) • rothMvHasse (i + j) P := by
  ext l
  rw [rothMvHasse_coeff_h, rothMvHasse_coeff_h]
  rw [MvPolynomial.coeff_smul, rothMvHasse_coeff_h]
  rw [smul_eq_mul]
  have hprod :
      (∏ h, (Nat.choose ((l + j) h) (j h) : R)) *
          (∏ h, (Nat.choose ((l + j + i) h) (i h) : R)) =
        (∏ h, (Nat.choose ((i + j) h) (i h) : R)) *
          (∏ h, (Nat.choose ((l + (i + j)) h) ((i + j) h) : R)) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro h _
    simp only [Finsupp.add_apply]
    rw [← Nat.cast_mul, ← Nat.cast_mul, roth_choose_comp_h]
  have hindex : l + j + i = l + (i + j) := by
    ext h
    simp only [Finsupp.add_apply]
    omega
  rw [hindex] at hprod
  rw [hindex, ← mul_assoc, ← mul_assoc, hprod]

lemma rothMvHasse_add_h {m : ℕ} {R : Type*} [CommSemiring R]
    (i : RothMvIndex m) (P Q : MvPolynomial (Fin m) R) :
    rothMvHasse i (P + Q) = rothMvHasse i P + rothMvHasse i Q := by
  ext k
  simp only [rothMvHasse_coeff_h, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    mul_add]

lemma rothMvHasse_smul_h {m : ℕ} {R : Type*} [CommSemiring R]
    (i : RothMvIndex m) (c : R) (P : MvPolynomial (Fin m) R) :
    rothMvHasse i (c • P) = c • rothMvHasse i P := by
  ext k
  simp only [rothMvHasse_coeff_h, MvPolynomial.coeff_smul, smul_eq_mul]
  ring

lemma rothMvHasse_map_h {m : ℕ} {R S : Type*} [CommSemiring R]
    [CommSemiring S] (f : R →+* S) (i : RothMvIndex m)
    (P : MvPolynomial (Fin m) R) :
    MvPolynomial.map f (rothMvHasse i P) =
      rothMvHasse i (MvPolynomial.map f P) := by
  ext k
  rw [MvPolynomial.coeff_map, rothMvHasse_coeff_h, rothMvHasse_coeff_h,
    MvPolynomial.coeff_map, map_mul, map_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro h _
  simp

lemma rothMvHasse_finset_sum_h {m : ℕ} {R : Type*} [CommSemiring R]
    {ι : Type*} (s : Finset ι) (i : RothMvIndex m)
    (P : ι → MvPolynomial (Fin m) R) :
    rothMvHasse i (∑ a ∈ s, P a) = ∑ a ∈ s, rothMvHasse i (P a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rothMvHasse_zero_h]
  | @insert a s ha ih => simp [ha, rothMvHasse_add_h, ih]

lemma rothTranslate_C_h {R : Type*} [CommRing R] :
    ∀ {m : ℕ} (x : Fin m → R) (c : R),
      rothTranslate m x (MvPolynomial.C c) = MvPolynomial.C c := by
  intro m
  induction m with
  | zero => simp [rothTranslate]
  | succ n ih =>
      intro x c
      have hC : MvPolynomial.finSuccEquiv R n (MvPolynomial.C c) =
          Polynomial.C (MvPolynomial.C c) := by
        change (MvPolynomial.finSuccEquiv R n) (algebraMap R _ c) =
          Polynomial.C (algebraMap R _ c)
        exact (MvPolynomial.finSuccEquiv R n).commutes c
      apply (MvPolynomial.finSuccEquiv R n).injective
      simp [rothTranslate, hC, ih]

lemma rothTranslate_coeff_cons_h {R : Type*} [CommRing R] {n : ℕ}
    (x : Fin (n + 1) → R) (P : MvPolynomial (Fin (n + 1)) R)
    (a : ℕ) (i : RothMvIndex n) :
    (rothTranslate (n + 1) x P).coeff (i.cons a) =
      (rothTranslate n (fun h ↦ x h.succ)
        ((Polynomial.taylor (MvPolynomial.C (x 0))
          (MvPolynomial.finSuccEquiv R n P)).coeff a)).coeff i := by
  rw [← MvPolynomial.finSuccEquiv_coeff_coeff i (rothTranslate (n + 1) x P) a]
  simp only [rothTranslate, AlgEquiv.symm_toRingEquiv, RingEquiv.symm_mk,
    AlgEquiv.toEquiv_eq_coe, AlgEquiv.symm_toEquiv_eq_symm, RingEquiv.toRingHom_eq_coe,
    AlgHom.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_comp,
    RingHom.coe_coe, RingEquiv.coe_mk, EquivLike.coe_coe, Polynomial.coe_mapRingHom,
    Function.comp_apply, Polynomial.taylorAlgHom_apply, Polynomial.map_taylor,
    AlgEquiv.apply_symm_apply]
  rw [← Polynomial.map_taylor, Polynomial.coeff_map]

lemma rothMvHasse_finSucc_coeff_h {n : ℕ} {R : Type*} [CommSemiring R]
    (P : MvPolynomial (Fin (n + 1)) R) (a k : ℕ) (i : RothMvIndex n) :
    ((MvPolynomial.finSuccEquiv R n) (rothMvHasse (i.cons a) P)).coeff k =
      rothMvHasse i
        ((Polynomial.hasseDeriv a ((MvPolynomial.finSuccEquiv R n) P)).coeff k) := by
  ext l
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]
  rw [show (i.cons a : RothMvIndex (n + 1)) = Finsupp.cons a i from rfl]
  rw [show (l.cons k : RothMvIndex (n + 1)) = Finsupp.cons k l from rfl]
  rw [rothMvHasse_coeff_h, rothMvHasse_coeff_h, Polynomial.hasseDeriv_coeff]
  simp only [Fin.prod_univ_succ, Finsupp.cons_zero, Finsupp.cons_succ,
    Finsupp.add_apply]
  rw [show (↑((k + a).choose a) : MvPolynomial (Fin n) R) =
    MvPolynomial.C ((k + a).choose a : R) by simp]
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.finSuccEquiv_coeff_coeff]
  have hcons : Finsupp.cons k l + Finsupp.cons a i = Finsupp.cons (k + a) (l + i) := by
    ext h
    refine Fin.cases ?_ (fun h ↦ ?_) h <;> simp
  rw [hcons]
  ac_rfl

lemma rothTranslate_eval_coeff_h {R : Type*} [CommRing R] {m : ℕ}
    (x : Fin m → R) (p : Polynomial (MvPolynomial (Fin m) R)) (y : R)
    (i : RothMvIndex m) :
    (rothTranslate m x (Polynomial.eval (MvPolynomial.C y) p)).coeff i =
      ∑ k ∈ p.support, (rothTranslate m x (p.coeff k)).coeff i * y ^ k := by
  rw [Polynomial.eval_eq_sum]
  rw [Polynomial.sum_def, map_sum, MvPolynomial.coeff_sum]
  congr with k
  rw [map_mul, map_pow, rothTranslate_C_h]
  rw [← MvPolynomial.C_pow, mul_comm, MvPolynomial.coeff_C_mul]
  ac_rfl

lemma rothTranslate_coeff_eq_eval_hasse_h {R : Type*} [CommRing R] :
    ∀ {m : ℕ} (x : Fin m → R) (P : MvPolynomial (Fin m) R) (i : RothMvIndex m),
      (rothTranslate m x P).coeff i = MvPolynomial.eval x (rothMvHasse i P) := by
  intro m
  induction m with
  | zero =>
      intro x P i
      have hx : x = 0 := Subsingleton.elim _ _
      have hi : i = 0 := Subsingleton.elim _ _
      subst x
      subst i
      rw [rothMvHasse_zero_index_h]
      change P.coeff 0 = MvPolynomial.eval (0 : Fin 0 → R) P
      rw [MvPolynomial.eval_zero]
      rfl
  | succ n ih =>
      intro x P i
      let a : ℕ := i 0
      let it : RothMvIndex n := i.tail
      let xt : Fin n → R := fun h ↦ x h.succ
      let p : Polynomial (MvPolynomial (Fin n) R) := MvPolynomial.finSuccEquiv R n P
      let A : Polynomial (MvPolynomial (Fin n) R) := Polynomial.hasseDeriv a p
      let B : Polynomial (MvPolynomial (Fin n) R) :=
        MvPolynomial.finSuccEquiv R n (rothMvHasse (it.cons a) P)
      have hi : it.cons a = i := by
        simp [a, it]
      rw [← hi, rothTranslate_coeff_cons_h]
      change
        (rothTranslate n xt
          ((Polynomial.taylor (MvPolynomial.C (x 0)) p).coeff a)).coeff it = _
      rw [Polynomial.taylor_coeff]
      change (rothTranslate n xt (Polynomial.eval (MvPolynomial.C (x 0)) A)).coeff it = _
      rw [rothTranslate_eval_coeff_h]
      have hx : x = Fin.cons (x 0) xt := by
        ext h
        refine Fin.cases ?_ (fun h ↦ ?_) h <;> simp [xt]
      rw [hx, MvPolynomial.eval_eq_eval_mv_eval']
      change (∑ k ∈ A.support, (rothTranslate n xt (A.coeff k)).coeff it * x 0 ^ k) =
        Polynomial.eval (x 0) (Polynomial.map (MvPolynomial.eval xt) B)
      have hBA : B.support ⊆ A.support := by
        intro k hk
        by_contra hkA
        have hAk : A.coeff k = 0 := Polynomial.notMem_support_iff.mp hkA
        have hBk := rothMvHasse_finSucc_coeff_h P a k it
        change B.coeff k = rothMvHasse it (A.coeff k) at hBk
        rw [hAk, rothMvHasse_zero_h] at hBk
        exact (Polynomial.mem_support_iff.mp hk) hBk
      have hmap : (Polynomial.map (MvPolynomial.eval xt) B).support ⊆ A.support :=
        (Polynomial.support_map_subset (MvPolynomial.eval xt) B).trans hBA
      rw [Polynomial.eval_eq_sum]
      rw [Polynomial.sum_eq_of_subset (fun e c ↦ c * x 0 ^ e) (by simp) hmap]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Polynomial.coeff_map]
      have hBk := rothMvHasse_finSucc_coeff_h P a k it
      change B.coeff k = rothMvHasse it (A.coeff k) at hBk
      rw [hBk, ← ih xt (A.coeff k) it]

lemma rothMvWeight_add_h {m : ℕ} (r : Fin m → ℕ) (i j : RothMvIndex m) :
    rothMvWeight r (i + j) = rothMvWeight r i + rothMvWeight r j := by
  simp only [rothMvWeight, Finsupp.add_apply, Nat.cast_add, add_div,
    Finset.sum_add_distrib]

lemma rothMvWeight_nonneg_h {m : ℕ} (r : Fin m → ℕ) (i : RothMvIndex m) :
    0 ≤ rothMvWeight r i := by
  unfold rothMvWeight
  positivity

lemma rothMvWeight_mul_h {m k : ℕ} (r : Fin m → ℕ) (i : RothMvIndex m)
    (hk : 0 < k) (hr : ∀ h, 0 < r h) :
    rothMvWeight (fun h ↦ k * r h) i = rothMvWeight r i / k := by
  unfold rothMvWeight
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro h _
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hrR : (r h : ℝ) ≠ 0 := by exact_mod_cast (hr h).ne'
  push_cast
  field_simp

lemma rothMvVanishesBelow_hasse_h {m : ℕ} {R : Type*} [CommRing R]
    {P : MvPolynomial (Fin m) R} {x : Fin m → R} {r : Fin m → ℕ} {t : ℝ}
    (hP : rothMvVanishesBelow P x r t) (i : RothMvIndex m) :
    rothMvVanishesBelow (rothMvHasse i P) x r (t - rothMvWeight r i) := by
  intro j hj
  rw [rothTranslate_coeff_eq_eval_hasse_h, rothMvHasse_comp_h]
  have hw : rothMvWeight r (i + j) < t := by
    rw [rothMvWeight_add_h]
    linarith
  have hz := hP (i + j) hw
  rw [rothTranslate_coeff_eq_eval_hasse_h] at hz
  simp [hz]

lemma rothMvVanishesBelow_mul_h {m : ℕ} {R : Type*} [CommRing R]
    {P Q : MvPolynomial (Fin m) R} {x : Fin m → R} {r : Fin m → ℕ} {a b : ℝ}
    (hP : rothMvVanishesBelow P x r a) (hQ : rothMvVanishesBelow Q x r b) :
    rothMvVanishesBelow (P * Q) x r (a + b) := by
  classical
  intro i hi
  rw [map_mul, ← MvPolynomial.notMem_support_iff]
  intro himem
  have hadd := MvPolynomial.support_mul
    (rothTranslate m x P) (rothTranslate m x Q) himem
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.mem_add.mp hadd
  have hPu : (rothTranslate m x P).coeff u ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hu
  have hQv : (rothTranslate m x Q).coeff v ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hv
  have hwu : a ≤ rothMvWeight r u := by
    by_contra hnot
    exact hPu (hP u (lt_of_not_ge hnot))
  have hwv : b ≤ rothMvWeight r v := by
    by_contra hnot
    exact hQv (hQ v (lt_of_not_ge hnot))
  rw [← huv, rothMvWeight_add_h] at hi
  linarith

lemma rothMvVanishesBelow_zero_h {m : ℕ} {R : Type*} [CommRing R]
    (x : Fin m → R) (r : Fin m → ℕ) (t : ℝ) :
  rothMvVanishesBelow (0 : MvPolynomial (Fin m) R) x r t := by
  intro i _hi
  simp

lemma rothMvVanishesBelow_nonpos_h {m : ℕ} {R : Type*} [CommRing R]
    (P : MvPolynomial (Fin m) R) (x : Fin m → R) (r : Fin m → ℕ)
    {t : ℝ} (ht : t ≤ 0) : rothMvVanishesBelow P x r t := by
  intro i hi
  exact (not_lt_of_ge (rothMvWeight_nonneg_h r i) (hi.trans_le ht)).elim

lemma rothMvVanishesBelow_add_h {m : ℕ} {R : Type*} [CommRing R]
    {P Q : MvPolynomial (Fin m) R} {x : Fin m → R} {r : Fin m → ℕ} {t : ℝ}
    (hP : rothMvVanishesBelow P x r t) (hQ : rothMvVanishesBelow Q x r t) :
  rothMvVanishesBelow (P + Q) x r t := by
  intro i hi
  rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hP i hi, hQ i hi, add_zero]

lemma rothMvVanishesBelow_neg_h {m : ℕ} {R : Type*} [CommRing R]
    {P : MvPolynomial (Fin m) R} {x : Fin m → R} {r : Fin m → ℕ} {t : ℝ}
    (hP : rothMvVanishesBelow P x r t) :
    rothMvVanishesBelow (-P) x r t := by
  intro i hi
  rw [map_neg, MvPolynomial.coeff_neg, hP i hi, neg_zero]

lemma rothMvVanishesBelow_smul_h {m : ℕ} {R : Type*} [CommRing R]
    {P : MvPolynomial (Fin m) R} {x : Fin m → R} {r : Fin m → ℕ} {t : ℝ}
    (hP : rothMvVanishesBelow P x r t) (c : R) :
    rothMvVanishesBelow (c • P) x r t := by
  rw [MvPolynomial.smul_eq_C_mul]
  intro i hi
  rw [map_mul, rothTranslate_C_h]
  simp [hP i hi]

lemma rothMvVanishesBelow_mono_h {m : ℕ} {R : Type*} [CommRing R]
    {P : MvPolynomial (Fin m) R} {x : Fin m → R} {r : Fin m → ℕ} {a b : ℝ}
    (hP : rothMvVanishesBelow P x r a) (hba : b ≤ a) :
    rothMvVanishesBelow P x r b := by
  intro i hi
  exact hP i (hi.trans_le hba)

lemma rothMvVanishesBelow_max_h {m : ℕ} {R : Type*} [CommRing R]
    {P : MvPolynomial (Fin m) R} {x : Fin m → R} {r : Fin m → ℕ} {a b : ℝ}
    (ha : rothMvVanishesBelow P x r a) (hb : rothMvVanishesBelow P x r b) :
    rothMvVanishesBelow P x r (max a b) := by
  rcases le_total a b with hab | hba
  · simpa [max_eq_right hab] using hb
  · simpa [max_eq_left hba] using ha

lemma rothMvVanishesBelow_mul_weights_h {m k : ℕ} {R : Type*} [CommRing R]
    {P : MvPolynomial (Fin m) R} {x : Fin m → R} {r : Fin m → ℕ} {t : ℝ}
    (hP : rothMvVanishesBelow P x r t) (hk : 0 < k) (hr : ∀ h, 0 < r h) :
    rothMvVanishesBelow P x (fun h ↦ k * r h) (t / k) := by
  intro i hi
  apply hP i
  rw [rothMvWeight_mul_h r i hk hr] at hi
  exact (div_lt_div_iff_of_pos_right (by exact_mod_cast hk)).mp hi

lemma rothMvVanishesBelow_finset_sum_h {m : ℕ} {R : Type*} [CommRing R]
    {J : Type*} (s : Finset J) {P : J → MvPolynomial (Fin m) R}
    {x : Fin m → R} {r : Fin m → ℕ} {t : ℝ}
    (hP : ∀ j ∈ s, rothMvVanishesBelow (P j) x r t) :
    rothMvVanishesBelow (∑ j ∈ s, P j) x r t := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using rothMvVanishesBelow_zero_h x r t
  | @insert j s hjs ih =>
      rw [Finset.sum_insert hjs]
      exact rothMvVanishesBelow_add_h (hP j (Finset.mem_insert_self _ _))
        (ih fun k hk ↦ hP k (Finset.mem_insert_of_mem hk))

lemma rothMvVanishesBelow_finset_prod_h {m : ℕ} {R : Type*} [CommRing R]
    {J : Type*} (s : Finset J) (P : J → MvPolynomial (Fin m) R)
    (a : J → ℝ) {x : Fin m → R} {r : Fin m → ℕ}
    (hP : ∀ j ∈ s, rothMvVanishesBelow (P j) x r (a j)) :
    rothMvVanishesBelow (∏ j ∈ s, P j) x r (∑ j ∈ s, a j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro i hi
      simp only [Finset.prod_empty, map_one]
      have hneg : rothMvWeight r i < 0 := hi
      have hnonneg : 0 ≤ rothMvWeight r i := by
        unfold rothMvWeight
        positivity
      exact (not_lt_of_ge hnonneg hneg).elim
  | @insert j s hjs ih =>
      rw [Finset.prod_insert hjs, Finset.sum_insert hjs]
      exact rothMvVanishesBelow_mul_h (hP j (Finset.mem_insert_self _ _))
        (ih fun k hk ↦ hP k (Finset.mem_insert_of_mem hk))

lemma rothHasseDet_map_h {m k : ℕ} {R S : Type*}
    [CommRing R] [CommRing S] (f : R →+* S)
    (P : MvPolynomial (Fin m) R) (u v : Fin k → RothMvIndex m) :
    MvPolynomial.map f (rothHasseDet P u v) =
      rothHasseDet (MvPolynomial.map f P) u v := by
  classical
  let M : Matrix (Fin k) (Fin k) (MvPolynomial (Fin m) R) :=
    fun s t ↦ rothMvHasse (u s + v t) P
  unfold rothHasseDet
  change MvPolynomial.map f M.det = _
  rw [RingHom.map_det]
  congr 1
  funext s t
  exact rothMvHasse_map_h f (u s + v t) P

lemma rothHasseDet_vanishesBelow_of_rowWeight_le_h
    {m k : ℕ} {R : Type*} [CommRing R]
    {P : MvPolynomial (Fin m) R} {x : Fin m → R} {r : Fin m → ℕ} {T ρ : ℝ}
    (hP : rothMvVanishesBelow P x r T) (u v : Fin k → RothMvIndex m)
    (hu : ∀ s, rothMvWeight r (u s) ≤ ρ) :
    rothMvVanishesBelow (rothHasseDet P u v) x r
      (∑ t, max 0 (T - ρ - rothMvWeight r (v t))) := by
  classical
  unfold rothHasseDet
  let M : Matrix (Fin k) (Fin k) (MvPolynomial (Fin m) R) :=
    fun s t ↦ rothMvHasse (u s + v t) P
  change rothMvVanishesBelow M.det x r _
  rw [Matrix.det_apply M]
  apply rothMvVanishesBelow_finset_sum_h
  intro σ _hσ
  have hentry : ∀ s : Fin k,
      rothMvVanishesBelow (rothMvHasse (u (σ s) + v s) P) x r
        (max 0 (T - ρ - rothMvWeight r (v s))) := by
    intro s
    have hder := rothMvVanishesBelow_hasse_h hP (u (σ s) + v s)
    have hzero := rothMvVanishesBelow_nonpos_h
      (rothMvHasse (u (σ s) + v s) P) x r (le_refl 0)
    apply rothMvVanishesBelow_mono_h (rothMvVanishesBelow_max_h hzero hder)
    rw [rothMvWeight_add_h]
    exact max_le_max le_rfl (by linarith [hu (σ s)])
  have hprod := rothMvVanishesBelow_finset_prod_h Finset.univ
    (fun s : Fin k ↦ rothMvHasse (u (σ s) + v s) P)
    (fun s ↦ max 0 (T - ρ - rothMvWeight r (v s)))
    (fun s _hs ↦ hentry s)
  obtain hsign | hsign := Int.units_eq_one_or (Equiv.Perm.sign σ)
  · simpa [M, hsign] using hprod
  · simpa [M, hsign] using rothMvVanishesBelow_neg_h hprod

lemma roth_exists_row_det_ne_zero_of_mem_span_h {k : ℕ} {K : Type*} [CommRing K]
    (A : Matrix (Fin k) (Fin k) K) (i : Fin k) (S : Set (Fin k → K))
    (hA : A.det ≠ 0) (hi : A i ∈ Submodule.span K S) :
    ∃ v ∈ S, (A.updateRow i v).det ≠ 0 := by
  classical
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  have hall : ∀ v ∈ Submodule.span K S, (A.updateRow i v).det = 0 := by
    intro v hv
    apply Submodule.span_induction (R := K) (s := S)
      (p := fun v _ ↦ (A.updateRow i v).det = 0)
    · intro v hv
      exact h v hv
    · apply Matrix.det_eq_zero_of_row_eq_zero i
      intro j
      simp [Matrix.updateRow_apply]
    · intro u v _hu _hv hu hv
      rw [Matrix.det_updateRow_add, hu, hv, add_zero]
    · intro c v _hv hv
      rw [Matrix.det_updateRow_smul, hv, mul_zero]
    · exact hv
  have := hall (A i) hi
  rw [Matrix.updateRow_eq_self] at this
  exact hA this

lemma roth_exists_nonsingular_rows_of_mem_span_h {k : ℕ} {K : Type*} [CommRing K]
    (A : Matrix (Fin k) (Fin k) K) (S : Fin k → Set (Fin k → K))
    (hA : A.det ≠ 0) (hspan : ∀ i, A i ∈ Submodule.span K (S i)) :
    ∃ B : Matrix (Fin k) (Fin k) K, B.det ≠ 0 ∧ ∀ i, B i ∈ S i := by
  classical
  have aux : ∀ s : Finset (Fin k),
      ∃ B : Matrix (Fin k) (Fin k) K, B.det ≠ 0 ∧
        (∀ i ∈ s, B i ∈ S i) ∧ (∀ i ∉ s, B i = A i) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        exact ⟨A, hA, by simp, by simp⟩
    | @insert i s his ih =>
        obtain ⟨B, hB, hBs, hBout⟩ := ih
        have hBi : B i ∈ Submodule.span K (S i) := by
          rw [hBout i his]
          exact hspan i
        obtain ⟨v, hv, hBv⟩ :=
          roth_exists_row_det_ne_zero_of_mem_span_h B i (S i) hB hBi
        refine ⟨B.updateRow i v, hBv, ?_, ?_⟩
        · intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hjs
          · simpa using hv
          · have hji : j ≠ i := by
              intro hji
              subst j
              exact his hjs
            rw [Matrix.updateRow_ne hji]
            exact hBs j hjs
        · intro j hj
          have hji : j ≠ i := by
            intro hji
            subst j
            exact hj (Finset.mem_insert_self i s)
          rw [Matrix.updateRow_ne hji]
          exact hBout j (fun hjs ↦ hj (Finset.mem_insert_of_mem hjs))
  obtain ⟨B, hB, hrows, _⟩ := aux Finset.univ
  exact ⟨B, hB, fun i ↦ hrows i (Finset.mem_univ i)⟩

lemma roth_wronskian_ne_zero_of_natDegree_ne_h {K : Type*} [Field K] [CharZero K]
    {f g : K[X]} (hf : f ≠ 0) (hg : g ≠ 0) (hdeg : f.natDegree ≠ g.natDegree) :
    Polynomial.wronskian f g ≠ 0 := by
  intro hw
  unfold Polynomial.wronskian at hw
  by_cases hfdeg : f.natDegree = 0
  · have hgdeg : g.natDegree ≠ 0 := by aesop
    have hfd : f.derivative = 0 := Polynomial.derivative_eq_zero.mpr hfdeg
    rw [hfd, zero_mul, sub_zero] at hw
    exact mul_ne_zero hf (Polynomial.derivative_ne_zero.mpr hgdeg) hw
  · by_cases hgdeg : g.natDegree = 0
    · have hgd : g.derivative = 0 := Polynomial.derivative_eq_zero.mpr hgdeg
      rw [hgd, mul_zero, zero_sub] at hw
      exact neg_ne_zero.mpr (mul_ne_zero (Polynomial.derivative_ne_zero.mpr hfdeg) hg) hw
    · have hfd : f.derivative ≠ 0 := Polynomial.derivative_ne_zero.mpr hfdeg
      have hgd : g.derivative ≠ 0 := Polynomial.derivative_ne_zero.mpr hgdeg
      have hdegrees : (f * g.derivative).degree = (f.derivative * g).degree := by
        rw [Polynomial.degree_eq_natDegree (mul_ne_zero hf hgd),
          Polynomial.degree_eq_natDegree (mul_ne_zero hfd hg),
          Polynomial.natDegree_mul hf hgd, Polynomial.natDegree_mul hfd hg,
          Polynomial.natDegree_derivative, Polynomial.natDegree_derivative]
        norm_cast
        omega
      have hlc : (f * g.derivative).leadingCoeff ≠
          (f.derivative * g).leadingCoeff := by
        simp only [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_derivative]
        intro heq
        have hflc : f.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hf
        have hglc : g.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hg
        apply hdeg
        apply Nat.cast_injective (R := K)
        have heq' : f.leadingCoeff * g.leadingCoeff * (g.natDegree : K) =
            f.leadingCoeff * g.leadingCoeff * (f.natDegree : K) := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using heq
        exact (mul_left_cancel₀ (mul_ne_zero hflc hglc)) heq'.symm
      have hlead := Polynomial.leadingCoeff_sub_of_degree_eq hdegrees hlc
      rw [hw, Polynomial.leadingCoeff_zero] at hlead
      exact sub_ne_zero.mpr hlc hlead.symm

lemma roth_wronskian_eq_zero_imp_eq_smul_h {K : Type*} [Field K] [CharZero K]
    {f g : K[X]} (hf : f ≠ 0) (hw : Polynomial.wronskian f g = 0) :
    ∃ c : K, g = c • f := by
  by_cases hg : g = 0
  · exact ⟨0, by simp [hg]⟩
  have hdeg : f.natDegree = g.natDegree := by
    by_contra hne
    exact roth_wronskian_ne_zero_of_natDegree_ne_h hf hg hne hw
  let c := g.leadingCoeff / f.leadingCoeff
  let h := g - c • f
  have hdegree : h.degree < f.degree := by
    have hc : c ≠ 0 := div_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hg)
      (Polynomial.leadingCoeff_ne_zero.mpr hf)
    have hcf : c • f ≠ 0 := smul_ne_zero hc hf
    have hlt : h.degree < g.degree := by
      apply Polynomial.degree_sub_lt_left
      · rw [Polynomial.degree_eq_natDegree hg, Polynomial.degree_eq_natDegree hcf]
        rw [Polynomial.natDegree_smul f hc]
        exact_mod_cast hdeg.symm
      · exact hg
      · dsimp [c]
        rw [Polynomial.leadingCoeff_smul_of_smul_regular f
          (IsSMulRegular.of_ne_zero hc : IsSMulRegular K c)]
        simp only [smul_eq_mul]
        exact (div_mul_cancel₀ g.leadingCoeff (Polynomial.leadingCoeff_ne_zero.mpr hf)).symm
    simpa [Polynomial.degree_eq_natDegree hf, Polynomial.degree_eq_natDegree hg, hdeg] using hlt
  have hwr : Polynomial.wronskian f h = 0 := by
    dsimp [h]
    unfold Polynomial.wronskian
    simp only [Polynomial.derivative_sub, Polynomial.derivative_smul]
    unfold Polynomial.wronskian at hw
    simp only [Polynomial.smul_eq_C_mul]
    calc
      f * (g.derivative - Polynomial.C c * f.derivative) -
          f.derivative * (g - Polynomial.C c * f) =
          f * g.derivative - f.derivative * g := by ring
      _ = 0 := hw
  have hh : h = 0 := by
    by_contra hh
    have hnd : f.natDegree ≠ h.natDegree := by
      intro heq
      have := hdegree
      rw [Polynomial.degree_eq_natDegree hf, Polynomial.degree_eq_natDegree hh, heq] at this
      exact lt_irrefl _ this
    exact roth_wronskian_ne_zero_of_natDegree_ne_h hf hh hnd hwr
  exact ⟨c, sub_eq_zero.mp hh⟩

lemma rothPolyJetRows_mono_h {k : ℕ} {K : Type*} [Field K]
    (f : Fin k → K[X]) {s t : ℕ} (hst : s ≤ t) :
    rothPolyJetRows f s ⊆ rothPolyJetRows f t := by
  rintro v ⟨n, hn, rfl⟩
  exact ⟨n, hn.trans hst, rfl⟩

lemma rothPolyRowDerivative_derivativeRow_h {k : ℕ} {K : Type*} [Field K]
    (f : Fin k → K[X]) (n : ℕ) :
    rothPolyRowDerivative (rothPolyDerivativeRow f n) = rothPolyDerivativeRow f (n + 1) := by
  ext j
  simp only [rothPolyRowDerivative, rothPolyDerivativeRow]
  rw [Function.iterate_succ_apply']

lemma rothPolyRowDerivative_mem_span_h {k : ℕ} {K : Type*} [Field K]
    (f : Fin k → K[X]) {s : ℕ} {v : Fin k → K[X]}
    (hv : v ∈ Submodule.span K[X] (rothPolyJetRows f s)) :
    rothPolyRowDerivative v ∈ Submodule.span K[X] (rothPolyJetRows f (s + 1)) := by
  let T := Submodule.span K[X] (rothPolyJetRows f (s + 1))
  have hold : Submodule.span K[X] (rothPolyJetRows f s) ≤ T :=
    Submodule.span_mono (rothPolyJetRows_mono_h f (Nat.le_succ s))
  apply Submodule.span_induction (R := K[X]) (s := rothPolyJetRows f s)
    (p := fun v _ ↦ rothPolyRowDerivative v ∈ T)
  · rintro _ ⟨n, hn, rfl⟩
    rw [rothPolyRowDerivative_derivativeRow_h]
    exact Submodule.subset_span ⟨n + 1, Nat.add_le_add_right hn 1, rfl⟩
  · have hz : rothPolyRowDerivative (0 : Fin k → K[X]) = 0 := by
      ext j
      simp [rothPolyRowDerivative]
    rw [hz]
    exact T.zero_mem
  · intro u w hu hw hu' hw'
    have hadd : rothPolyRowDerivative (u + w) =
        rothPolyRowDerivative u + rothPolyRowDerivative w := by
      ext j
      simp [rothPolyRowDerivative]
    rw [hadd]
    exact T.add_mem hu' hw'
  · intro c w hw hw'
    have hwT : w ∈ T := hold hw
    have hsum : Polynomial.derivative c • w + c • rothPolyRowDerivative w ∈ T :=
      T.add_mem (T.smul_mem _ hwT) (T.smul_mem _ hw')
    convert hsum using 1
    ext j
    simp [rothPolyRowDerivative, Polynomial.derivative_mul]
  · exact hv

lemma rothPolyWronskianDerivativeRow_zero_h {k : ℕ} {K : Type*} [Field K]
    (f : Fin (k + 1) → K[X]) (n : ℕ) :
    rothPolyWronskianDerivativeRow f n 0 = 0 := by
  change Polynomial.derivative^[n] (Polynomial.wronskian (f 0) (f 0)) = 0
  rw [Polynomial.wronskian_self_eq_zero]
  simp

lemma rothPolyWronskianRow_mem_span_h {k : ℕ} {K : Type*} [Field K]
    (f : Fin (k + 1) → K[X]) :
    rothPolyWronskianRow f ∈ Submodule.span K[X] (rothPolyJetRows f 1) := by
  have h0 : rothPolyDerivativeRow f 0 ∈
      Submodule.span K[X] (rothPolyJetRows f 1) :=
    Submodule.subset_span ⟨0, by omega, rfl⟩
  have h1 : rothPolyDerivativeRow f 1 ∈
      Submodule.span K[X] (rothPolyJetRows f 1) :=
    Submodule.subset_span ⟨1, le_rfl, rfl⟩
  have hmem := (Submodule.span K[X] (rothPolyJetRows f 1)).sub_mem
    ((Submodule.span K[X] (rothPolyJetRows f 1)).smul_mem (f 0) h1)
    ((Submodule.span K[X] (rothPolyJetRows f 1)).smul_mem (f 0).derivative h0)
  convert hmem using 1
  ext j
  simp [rothPolyWronskianRow, rothPolyDerivativeRow, Polynomial.wronskian]

lemma rothPolyWronskianDerivativeRow_mem_span_h {k : ℕ} {K : Type*} [Field K]
    (f : Fin (k + 1) → K[X]) (n : ℕ) :
    rothPolyWronskianDerivativeRow f n ∈
      Submodule.span K[X] (rothPolyJetRows f (n + 1)) := by
  induction n with
  | zero =>
      change rothPolyWronskianRow f ∈ Submodule.span K[X] (rothPolyJetRows f 1)
      exact rothPolyWronskianRow_mem_span_h f
  | succ n ih =>
      have hder := rothPolyRowDerivative_mem_span_h f ih
      convert hder using 1
      · ext j
        simp only [rothPolyRowDerivative, rothPolyWronskianDerivativeRow]
        rw [Function.iterate_succ_apply']

lemma rothPolyWronskian_tail_linearIndependent_h {k : ℕ} {K : Type*}
    [Field K] [CharZero K] (f : Fin (k + 1) → K[X]) (hf : LinearIndependent K f) :
    LinearIndependent K (fun j : Fin k ↦ Polynomial.wronskian (f 0) (f j.succ)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  let h : K[X] := ∑ j, c j • f j.succ
  have hwr : Polynomial.wronskian (f 0) h = 0 := calc
      _ =
          ∑ j, c j • Polynomial.wronskian (f 0) (f j.succ) := by
        simp [h, ← Polynomial.wronskianBilin_apply]
      _ = 0 := hc
  obtain ⟨a, ha⟩ := roth_wronskian_eq_zero_imp_eq_smul_h (hf.ne_zero 0) hwr
  let d : Fin (k + 1) → K := Fin.cons (-a) (fun i ↦ c i)
  have hrel : ∑ i, d i • f i = 0 := by
    rw [Fin.sum_univ_succ]
    simp only [d, Fin.cons_zero, Fin.cons_succ]
    change (-a) • f 0 + h = 0
    rw [ha]
    simp
  have hz := Fintype.linearIndependent_iff.mp hf d hrel j.succ
  simpa [d] using hz

lemma roth_exists_poly_adapted_matrix_h {K : Type*} [Field K] [CharZero K] :
    ∀ {k : ℕ} (f : Fin k → K[X]), LinearIndependent K f →
      ∃ A : Matrix (Fin k) (Fin k) K[X], A.det ≠ 0 ∧
        ∀ s : Fin k, A s ∈ Submodule.span K[X] (rothPolyJetRows f s) := by
  intro k
  induction k with
  | zero =>
      intro f _hf
      refine ⟨0, by simp, ?_⟩
      exact fun s ↦ Fin.elim0 s
  | succ k ih =>
      intro f hf
      let g : Fin k → K[X] :=
        fun j ↦ Polynomial.wronskian (f 0) (f j.succ)
      have hg : LinearIndependent K g := by
        exact rothPolyWronskian_tail_linearIndependent_h f hf
      obtain ⟨A, hA, hArows⟩ := ih g hg
      let B : Matrix (Fin (k + 1)) (Fin (k + 1)) K[X] :=
        Fin.cases f (fun s ↦ Fin.cons 0 (A s))
      have hBdet : B.det = f 0 * A.det := by
        rw [Matrix.det_succ_column_zero]
        rw [Fin.sum_univ_succ]
        simp [B, Matrix.submatrix, hf.ne_zero 0]
        rfl
      have hB : B.det ≠ 0 := by
        rw [hBdet]
        exact mul_ne_zero (hf.ne_zero 0) hA
      refine ⟨B, hB, ?_⟩
      intro s
      refine Fin.cases ?_ (fun t ↦ ?_) s
      · change f ∈ Submodule.span K[X] (rothPolyJetRows f 0)
        apply Submodule.subset_span
        refine ⟨0, le_rfl, ?_⟩
        ext j
        simp [rothPolyDerivativeRow]
      · change Fin.cons 0 (A t) ∈
          Submodule.span K[X] (rothPolyJetRows f t.succ)
        let T := Submodule.span K[X] (rothPolyJetRows f t.succ)
        apply Submodule.span_induction (R := K[X]) (s := rothPolyJetRows g t)
          (p := fun v _ ↦ Fin.cons 0 v ∈ T)
        · rintro _ ⟨n, hn, rfl⟩
          have heq : Fin.cons 0 (rothPolyDerivativeRow g n) =
              rothPolyWronskianDerivativeRow f n := by
            ext j
            refine Fin.cases ?_ (fun u ↦ ?_) j
            · simp [rothPolyWronskianDerivativeRow_zero_h]
            · simp [rothPolyDerivativeRow, rothPolyWronskianDerivativeRow, g]
          rw [heq]
          exact Submodule.span_mono (rothPolyJetRows_mono_h f (Nat.add_le_add_right hn 1))
            (rothPolyWronskianDerivativeRow_mem_span_h f n)
        · have hz : (Fin.cons (0 : K[X]) (0 : Fin k → K[X]) :
              Fin (k + 1) → K[X]) = 0 := by
            ext j
            refine Fin.cases (by simp) (fun w ↦ by simp) j
          rw [hz]
          exact T.zero_mem
        · intro u v _hu _hv hu hv
          have hadd : (Fin.cons (0 : K[X]) (u + v) : Fin (k + 1) → K[X]) =
              Fin.cons 0 u + Fin.cons 0 v := by
            ext j
            refine Fin.cases (by simp) (fun w ↦ by simp) j
          rw [hadd]
          exact T.add_mem hu hv
        · intro c v _hv hv
          have hsmul : (Fin.cons (0 : K[X]) (c • v) : Fin (k + 1) → K[X]) =
              c • Fin.cons 0 v := by
            ext j
            refine Fin.cases (by simp) (fun w ↦ by simp) j
          rw [hsmul]
          exact T.smul_mem c hv
        · exact hArows t

lemma roth_exists_poly_wronskian_orders_h {k : ℕ} {K : Type*}
    [Field K] [CharZero K] (f : Fin k → K[X]) (hf : LinearIndependent K f) :
    ∃ n : Fin k → ℕ, (∀ s, n s ≤ s) ∧
      (Matrix.det fun s j ↦ Polynomial.derivative^[n s] (f j)) ≠ 0 := by
  classical
  obtain ⟨A, hA, hArows⟩ := roth_exists_poly_adapted_matrix_h f hf
  obtain ⟨B, hB, hBrows⟩ :=
    roth_exists_nonsingular_rows_of_mem_span_h A (fun s ↦ rothPolyJetRows f s)
      hA hArows
  choose n hn hrow using hBrows
  refine ⟨n, hn, ?_⟩
  have hBeq : B = fun s j ↦ Polynomial.derivative^[n s] (f j) := by
    ext s j
    rw [hrow s]
    rfl
  rwa [← hBeq]

lemma roth_poly_wronskian_ne_zero_h {k : ℕ} {K : Type*}
    [Field K] [CharZero K] (f : Fin k → K[X]) (hf : LinearIndependent K f) :
    (Matrix.det fun s j ↦ Polynomial.derivative^[s.val] (f j)) ≠ 0 := by
  obtain ⟨n, hn, hdet⟩ := roth_exists_poly_wronskian_orders_h f hf
  have hninj : Function.Injective n := by
    intro s t hst
    by_contra hne
    apply hdet
    apply Matrix.det_zero_of_row_eq hne
    ext j
    rw [hst]
  have hnid : ∀ s : Fin k, n s = s.val := by
    cases k with
    | zero => exact fun s ↦ Fin.elim0 s
    | succ k =>
        have hprefix : ∀ s : Fin (k + 1), ∀ t : Fin (k + 1), t.val ≤ s.val → n t = t.val := by
          intro s
          induction s using Fin.induction with
          | zero =>
              intro t ht
              have htval : t.val = 0 := Nat.eq_zero_of_le_zero (by simpa using ht)
              have ht0 : t = 0 := Fin.eq_of_val_eq htval
              subst t
              exact Nat.eq_zero_of_le_zero (hn 0)
          | succ s ih =>
              intro t ht
              by_cases hts : t = s.succ
              · subst t
                apply Nat.le_antisymm (hn s.succ)
                by_contra hnot
                have hlt : n s.succ < s.succ.val := Nat.lt_of_not_ge hnot
                let u : Fin (k + 1) := ⟨n s.succ, hlt.trans s.succ.isLt⟩
                have hu : u.val ≤ s.castSucc.val := by
                  dsimp [u]
                  simpa using Nat.le_pred_of_lt hlt
                have hnu := ih u hu
                have hcollision : n u = n s.succ := by simpa [u] using hnu
                have hus := hninj hcollision
                have := congrArg Fin.val hus
                simp [u] at this
                omega
              · apply ih t
                have hlt : t.val < s.succ.val := lt_of_le_of_ne ht (by
                  intro heq
                  apply hts
                  exact Fin.eq_of_val_eq heq)
                simpa using Nat.le_pred_of_lt hlt
        exact fun s ↦ hprefix s s le_rfl
  simpa only [hnid] using hdet

lemma roth_poly_hasse_wronskian_ne_zero_h {k : ℕ}
    (f : Fin k → ℚ[X]) (hf : LinearIndependent ℚ f) :
    (Matrix.det fun s j ↦ Polynomial.hasseDeriv s.val (f j)) ≠ 0 := by
  let A : Matrix (Fin k) (Fin k) ℚ[X] :=
    fun s j ↦ Polynomial.derivative^[s.val] (f j)
  let H : Matrix (Fin k) (Fin k) ℚ[X] :=
    fun s j ↦ Polynomial.hasseDeriv s.val (f j)
  have hder : A.det ≠ 0 := roth_poly_wronskian_ne_zero_h f hf
  intro hhasse
  apply hder
  have hhasse' : H.det = 0 := hhasse
  have heq : A.det =
      Polynomial.C (∏ s : Fin k, (s.val.factorial : ℚ)) * H.det := by
    classical
    rw [Matrix.det_apply A, Matrix.det_apply H, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _hσ
    have hprod : ∏ s, A (σ s) s =
        Polynomial.C (∏ s : Fin k, (s.val.factorial : ℚ)) * ∏ s, H (σ s) s := by
      have hfactor : (∏ s : Fin k, ((σ s).val.factorial : ℚ)) =
          ∏ s : Fin k, (s.val.factorial : ℚ) :=
        Equiv.prod_comp σ (fun s : Fin k ↦ (s.val.factorial : ℚ))
      dsimp [A, H]
      rw [← hfactor, map_prod, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro s _hs
      have hfac :=
        congrFun (Polynomial.factorial_smul_hasseDeriv (R := ℚ) (σ s).val) (f s)
      simpa [smul_eq_mul] using hfac.symm
    rw [hprod]
    obtain hsign | hsign := Int.units_eq_one_or (Equiv.Perm.sign σ)
    · simp [hsign]
    · simp [hsign]
  rw [heq, hhasse', mul_zero]

lemma rothKroneckerEncode_succ_h {m D : ℕ} (i : Fin (m + 1) → ℕ) :
    rothKroneckerEncode D i =
      i 0 + D * rothKroneckerEncode D (fun h ↦ i h.succ) := by
  rw [rothKroneckerEncode, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, mul_one, rothKroneckerEncode, Fin.val_succ, pow_succ]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro h _
  simp [mul_left_comm, mul_comm]

lemma rothKroneckerEncode_injective_h : ∀ {m D : ℕ}, 1 < D →
    ∀ {i j : Fin m → ℕ}, (∀ h, i h < D) → (∀ h, j h < D) →
      rothKroneckerEncode D i = rothKroneckerEncode D j → i = j := by
  intro m
  induction m with
  | zero =>
      intro D _hD i j _hi _ _heq
      funext h
      exact Fin.elim0 h
  | succ m ih =>
      intro D hD i j hi hj heq
      rw [rothKroneckerEncode_succ_h, rothKroneckerEncode_succ_h] at heq
      have hzero : i 0 = j 0 := by
        have hmod := congrArg (fun n ↦ n % D) heq
        simpa [Nat.mod_eq_of_lt (hi 0), Nat.mod_eq_of_lt (hj 0)] using hmod
      have htailEq : rothKroneckerEncode D (fun (h : Fin m) ↦ i h.succ) =
          rothKroneckerEncode D (fun (h : Fin m) ↦ j h.succ) := by
        rw [hzero] at heq
        exact Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_of_lt hD) (Nat.add_left_cancel heq)
      have htail : (fun (h : Fin m) ↦ i h.succ) = fun (h : Fin m) ↦ j h.succ :=
        ih hD (fun (h : Fin m) ↦ hi h.succ) (fun (h : Fin m) ↦ hj h.succ) htailEq
      funext h
      refine Fin.cases hzero (fun t ↦ ?_) h
      exact congrFun htail t

lemma rothKronecker_monomial_h {m : ℕ} {K : Type*} [Field K] (D : ℕ)
    (i : Fin m →₀ ℕ) (c : K) :
    rothKronecker D (MvPolynomial.monomial i c) =
      Polynomial.monomial (rothKroneckerEncode D fun h ↦ i h) c := by
  rw [rothKronecker, MvPolynomial.eval₂Hom_monomial]
  rw [Finsupp.prod]
  simp only [← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum]
  rw [← Polynomial.C_mul_X_pow_eq_monomial]
  congr 1
  congr 1
  unfold rothKroneckerEncode
  calc
    _ =
        ∑ a : Fin m, D ^ (a : ℕ) * i a := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro a _ha hnot
      have hai : i a = 0 := by simpa using hnot
      simp [hai]
    _ = ∑ a : Fin m, i a * D ^ (a : ℕ) := by
      apply Finset.sum_congr rfl
      intro a _ha
      exact Nat.mul_comm _ _

lemma rothKronecker_eq_sum_h {m : ℕ} {K : Type*} [Field K] (D : ℕ)
    (P : MvPolynomial (Fin m) K) :
    rothKronecker D P = ∑ i ∈ P.support,
      Polynomial.monomial (rothKroneckerEncode D fun h ↦ i h) (P.coeff i) := by
  conv_lhs => rw [← MvPolynomial.support_sum_monomial_coeff P]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [rothKronecker_monomial_h]

lemma rothKronecker_ne_zero_of_bounded_h {m : ℕ} {K : Type*} [Field K] {D : ℕ}
    (hD : 1 < D) {P : MvPolynomial (Fin m) K} (hP : P ≠ 0)
    (hb : rothKroneckerBounded D P) : rothKronecker D P ≠ 0 := by
  obtain ⟨i, hi⟩ := MvPolynomial.support_nonempty.mpr hP
  have hci : P.coeff i ≠ 0 := MvPolynomial.mem_support_iff.mp hi
  have hcoeff : (rothKronecker D P).coeff (rothKroneckerEncode D fun h ↦ i h) =
      P.coeff i := by
    rw [rothKronecker_eq_sum_h, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j hj hji
      have henc : rothKroneckerEncode D (fun h ↦ j h) ≠
          rothKroneckerEncode D (fun h ↦ i h) := by
        intro heq
        apply hji
        apply Finsupp.ext
        intro h
        exact congrFun (rothKroneckerEncode_injective_h hD (hb j hj) (hb i hi) heq) h
      simp [henc]
    · exact fun hnot ↦ (hnot hi).elim
  intro hz
  have := congrArg (fun Q : K[X] ↦ Q.coeff (rothKroneckerEncode D fun h ↦ i h)) hz
  rw [hcoeff, Polynomial.coeff_zero] at this
  exact hci this

lemma rothKroneckerBounded_finset_sum_h {m : ℕ} {K : Type*} [Field K] {D : ℕ}
    {ι : Type*} (s : Finset ι) (P : ι → MvPolynomial (Fin m) K)
    (hP : ∀ a ∈ s, rothKroneckerBounded D (P a)) :
    rothKroneckerBounded D (∑ a ∈ s, P a) := by
  intro i hi h
  by_contra hnot
  have hz : (∑ a ∈ s, P a).coeff i = 0 := by
    rw [MvPolynomial.coeff_sum]
    apply Finset.sum_eq_zero
    intro a ha
    apply Finsupp.notMem_support_iff.mp
    exact fun hia ↦ hnot (hP a ha i hia h)
  exact (MvPolynomial.mem_support_iff.mp hi) hz

lemma rothKronecker_linearIndependent_h {m k : ℕ} {K : Type*} [Field K]
    {D : ℕ} (hD : 1 < D) (f : Fin k → MvPolynomial (Fin m) K)
    (hf : LinearIndependent K f) (hb : ∀ j, rothKroneckerBounded D (f j)) :
    LinearIndependent K (fun j ↦ rothKronecker D (f j)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  let P := ∑ a, c a • f a
  have hmap : rothKronecker D P = 0 := by
    dsimp [P]
    rw [map_sum]
    simpa [Algebra.smul_def, rothKronecker] using hc
  have hPb : rothKroneckerBounded D P := by
    dsimp [P]
    apply rothKroneckerBounded_finset_sum_h Finset.univ
    intro a _ha i hi h
    by_cases hca : c a = 0
    · simp [hca] at hi
    · have hsupp : (c a • f a).support = (f a).support :=
        MvPolynomial.support_smul_eq hca (f a)
      rw [hsupp] at hi
      exact hb a i hi h
  have hPzero : P = 0 := by
    by_contra hP
    exact rothKronecker_ne_zero_of_bounded_h hD hP hPb hmap
  exact Fintype.linearIndependent_iff.mp hf c hPzero j

lemma rothKronecker_X_h {m : ℕ} {K : Type*} [Field K] (D : ℕ) (h : Fin m) :
    rothKronecker D (MvPolynomial.X h : MvPolynomial (Fin m) K) =
      Polynomial.X ^ D ^ (h : ℕ) := by
  simp [rothKronecker]

lemma rothKronecker_derivative_h {m : ℕ} {K : Type*} [Field K] (D : ℕ)
    (P : MvPolynomial (Fin m) K) :
    (rothKronecker D P).derivative = ∑ h : Fin m,
      Polynomial.C (D ^ (h : ℕ) : K) * Polynomial.X ^ (D ^ (h : ℕ) - 1) *
        rothKronecker D (MvPolynomial.pderiv h P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [rothKronecker]
  | add P Q hP hQ =>
      simp only [map_add, hP, hQ]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro h _
      ring
  | mul_X P n hP =>
      have hsecond : (∑ h : Fin m,
          Polynomial.C (D ^ (h : ℕ) : K) * Polynomial.X ^ (D ^ (h : ℕ) - 1) *
            ((rothKronecker D P) *
              rothKronecker D (MvPolynomial.pderiv h (MvPolynomial.X n)))) =
          Polynomial.C (D ^ (n : ℕ) : K) * Polynomial.X ^ (D ^ (n : ℕ) - 1) *
            rothKronecker D P := by
        rw [Finset.sum_eq_single n]
        · simp [mul_assoc, mul_comm]
        · intro h _ hne
          rw [MvPolynomial.pderiv_X_of_ne hne.symm]
          simp
        · simp
      rw [map_mul, rothKronecker_X_h, Polynomial.derivative_mul, hP,
        Polynomial.derivative_X_pow]
      symm
      calc
        (∑ h : Fin m,
            Polynomial.C (D ^ (h : ℕ) : K) * Polynomial.X ^ (D ^ (h : ℕ) - 1) *
              rothKronecker D (MvPolynomial.pderiv h (P * MvPolynomial.X n))) =
            ∑ h : Fin m,
              (Polynomial.C (D ^ (h : ℕ) : K) * Polynomial.X ^ (D ^ (h : ℕ) - 1) *
                  rothKronecker D (MvPolynomial.pderiv h P) *
                    Polynomial.X ^ D ^ (n : ℕ) +
                Polynomial.C (D ^ (h : ℕ) : K) * Polynomial.X ^ (D ^ (h : ℕ) - 1) *
                  ((rothKronecker D P) *
                    rothKronecker D (MvPolynomial.pderiv h (MvPolynomial.X n)))) := by
          apply Finset.sum_congr rfl
          intro h _
          rw [MvPolynomial.pderiv_mul]
          simp only [map_add, map_mul, rothKronecker_X_h]
          ring
        _ = (∑ h : Fin m,
                Polynomial.C (D ^ (h : ℕ) : K) * Polynomial.X ^ (D ^ (h : ℕ) - 1) *
                  rothKronecker D (MvPolynomial.pderiv h P) *
                    Polynomial.X ^ D ^ (n : ℕ)) +
              ∑ h : Fin m,
                Polynomial.C (D ^ (h : ℕ) : K) * Polynomial.X ^ (D ^ (h : ℕ) - 1) *
                  ((rothKronecker D P) *
                    rothKronecker D (MvPolynomial.pderiv h (MvPolynomial.X n))) :=
          Finset.sum_add_distrib
        _ = (∑ h : Fin m,
                Polynomial.C (D ^ (h : ℕ) : K) * Polynomial.X ^ (D ^ (h : ℕ) - 1) *
                  rothKronecker D (MvPolynomial.pderiv h P)) *
                Polynomial.X ^ D ^ (n : ℕ) +
              Polynomial.C (D ^ (n : ℕ) : K) * Polynomial.X ^ (D ^ (n : ℕ) - 1) *
                rothKronecker D P := by
          rw [← Finset.sum_mul, hsecond]
        _ = _ := by
          push_cast
          ring

lemma rothMvHasse_single_one_h {m : ℕ} (h : Fin m)
    (P : MvPolynomial (Fin m) ℚ) :
    rothMvHasse (Finsupp.single h 1) P = MvPolynomial.pderiv h P := by
  ext i
  rw [rothMvHasse_coeff_h, MvPolynomial.coeff_pderiv]
  have hprod :
      (∏ b : Fin m,
          (Nat.choose ((i + (Finsupp.single h 1 : RothMvIndex m)) b)
            ((Finsupp.single h 1 : RothMvIndex m) b) : ℚ)) =
        (i h + 1 : ℚ) := by
    rw [Finset.prod_eq_single h]
    · simp
    · intro b _hb hbh
      simp [hbh]
    · simp
  rw [hprod]
  ring

lemma roth_pderiv_hasse_h {m : ℕ} (h : Fin m) (i : RothMvIndex m)
    (P : MvPolynomial (Fin m) ℚ) :
    MvPolynomial.pderiv h (rothMvHasse i P) =
      (i h + 1 : ℚ) • rothMvHasse (i + Finsupp.single h 1) P := by
  rw [← rothMvHasse_single_one_h, rothMvHasse_comp_h]
  have hprod :
      (∏ b : Fin m,
          (Nat.choose ((i + (Finsupp.single h 1 : RothMvIndex m)) b) (i b) : ℚ)) =
        (i h + 1 : ℚ) := by
    rw [Finset.prod_eq_single h]
    · simp
    · intro b _hb hbh
      simp [hbh]
    · simp
  rw [hprod]

lemma rothMvOrder_add_h {m : ℕ} (i j : RothMvIndex m) :
    rothMvOrder (i + j) = rothMvOrder i + rothMvOrder j := by
  simp [rothMvOrder, Finset.sum_add_distrib]

lemma rothMvOrder_single_h {m : ℕ} (h : Fin m) (n : ℕ) :
    rothMvOrder (Finsupp.single h n) = n := by
  simp [rothMvOrder]

lemma rothMvOrder_add_single_one_h {m : ℕ} (i : RothMvIndex m) (h : Fin m) :
    rothMvOrder (i + Finsupp.single h 1) = rothMvOrder i + 1 := by
  rw [rothMvOrder_add_h, rothMvOrder_single_h]

lemma rothKronHasseJetRows_mono_h {m k : ℕ} (D : ℕ)
    (f : Fin k → MvPolynomial (Fin m) ℚ) {s t : ℕ} (hst : s ≤ t) :
    rothKronHasseJetRows D f s ⊆ rothKronHasseJetRows D f t := by
  rintro v ⟨i, hi, rfl⟩
  exact ⟨i, hi.trans hst, rfl⟩

lemma rothKronHasseRow_derivative_h {m k : ℕ} (D : ℕ)
    (f : Fin k → MvPolynomial (Fin m) ℚ) (i : RothMvIndex m) :
    rothPolyRowDerivative (rothKronHasseRow D f i) =
      ∑ h : Fin m,
        (Polynomial.C (D ^ (h : ℕ) : ℚ) * Polynomial.X ^ (D ^ (h : ℕ) - 1) *
          Polynomial.C (i h + 1 : ℚ)) •
            rothKronHasseRow D f (i + Finsupp.single h 1) := by
  funext j
  simp only [rothPolyRowDerivative, rothKronHasseRow, Pi.smul_apply,
    Finset.sum_apply]
  rw [rothKronecker_derivative_h]
  apply Finset.sum_congr rfl
  intro h _
  rw [roth_pderiv_hasse_h]
  simp only [Algebra.smul_def, map_mul]
  simp [rothKronecker]
  ring

lemma rothKronHasseRowDerivative_mem_span_h {m k : ℕ} (D : ℕ)
    (f : Fin k → MvPolynomial (Fin m) ℚ) {s : ℕ} {v : Fin k → ℚ[X]}
    (hv : v ∈ Submodule.span ℚ[X] (rothKronHasseJetRows D f s)) :
    rothPolyRowDerivative v ∈
      Submodule.span ℚ[X] (rothKronHasseJetRows D f (s + 1)) := by
  let T := Submodule.span ℚ[X] (rothKronHasseJetRows D f (s + 1))
  have hold : Submodule.span ℚ[X] (rothKronHasseJetRows D f s) ≤ T :=
    Submodule.span_mono (rothKronHasseJetRows_mono_h D f (Nat.le_succ s))
  apply Submodule.span_induction (R := ℚ[X]) (s := rothKronHasseJetRows D f s)
    (p := fun v _ ↦ rothPolyRowDerivative v ∈ T)
  · rintro _ ⟨i, hi, rfl⟩
    rw [rothKronHasseRow_derivative_h]
    apply Submodule.sum_mem
    intro h _hh
    apply T.smul_mem
    apply Submodule.subset_span
    refine ⟨i + Finsupp.single h 1, ?_, rfl⟩
    rw [rothMvOrder_add_single_one_h]
    omega
  · have hz : rothPolyRowDerivative (0 : Fin k → ℚ[X]) = 0 := by
      ext j
      simp [rothPolyRowDerivative]
    rw [hz]
    exact T.zero_mem
  · intro u w _hu _hw hu hw
    have hadd : rothPolyRowDerivative (u + w) =
        rothPolyRowDerivative u + rothPolyRowDerivative w := by
      ext j
      simp [rothPolyRowDerivative]
    rw [hadd]
    exact T.add_mem hu hw
  · intro c w hw hw'
    have hwT : w ∈ T := hold hw
    have hsum : Polynomial.derivative c • w + c • rothPolyRowDerivative w ∈ T :=
      T.add_mem (T.smul_mem _ hwT) (T.smul_mem _ hw')
    convert hsum using 1
    ext j
    simp [rothPolyRowDerivative, Polynomial.derivative_mul]
  · exact hv

lemma rothPolyDerivativeRow_mem_kronHasse_span_h {m k : ℕ} (D : ℕ)
    (f : Fin k → MvPolynomial (Fin m) ℚ) (s : ℕ) :
    rothPolyDerivativeRow (fun j ↦ rothKronecker D (f j)) s ∈
      Submodule.span ℚ[X] (rothKronHasseJetRows D f s) := by
  induction s with
  | zero =>
      apply Submodule.subset_span
      refine ⟨0, by simp [rothMvOrder], ?_⟩
      ext j
      simp [rothPolyDerivativeRow, rothKronHasseRow, rothMvHasse_zero_index_h]
  | succ s ih =>
      have hder := rothKronHasseRowDerivative_mem_span_h D f ih
      rw [rothPolyRowDerivative_derivativeRow_h] at hder
      simpa [Nat.succ_eq_add_one] using hder

lemma roth_exists_generalized_wronskian_of_bounded_h {m k D : ℕ}
    (hD : 1 < D) (f : Fin k → MvPolynomial (Fin m) ℚ)
    (hf : LinearIndependent ℚ f) (hb : ∀ j, rothKroneckerBounded D (f j)) :
    ∃ i : Fin k → RothMvIndex m,
      (∀ s, rothMvOrder (i s) ≤ s) ∧
        (Matrix.det fun s j ↦ rothMvHasse (i s) (f j)) ≠ 0 := by
  classical
  let g : Fin k → ℚ[X] := fun j ↦ rothKronecker D (f j)
  have hg : LinearIndependent ℚ g :=
    rothKronecker_linearIndependent_h hD f hf hb
  let A : Matrix (Fin k) (Fin k) ℚ[X] :=
    fun s j ↦ Polynomial.derivative^[s.val] (g j)
  have hA : A.det ≠ 0 := roth_poly_wronskian_ne_zero_h g hg
  have hArows : ∀ s : Fin k,
      A s ∈ Submodule.span ℚ[X] (rothKronHasseJetRows D f s) := by
    intro s
    exact rothPolyDerivativeRow_mem_kronHasse_span_h D f s
  obtain ⟨B, hB, hBrows⟩ :=
    roth_exists_nonsingular_rows_of_mem_span_h A
      (fun s ↦ rothKronHasseJetRows D f s) hA hArows
  choose i hi hrow using hBrows
  refine ⟨i, hi, ?_⟩
  let C : Matrix (Fin k) (Fin k) (MvPolynomial (Fin m) ℚ) :=
    fun s j ↦ rothMvHasse (i s) (f j)
  have hBC : B = (rothKronecker D).mapMatrix C := by
    ext s j
    rw [hrow s]
    rfl
  have hmapdet : rothKronecker D C.det = B.det := by
    rw [RingHom.map_det, ← hBC]
  intro hC
  apply hB
  rw [← hmapdet, hC, map_zero]

lemma rothFinsuppL1_sum_superset_h {α : Type*} (f : α →₀ ℤ) (s : Finset α)
    (hfs : f.support ⊆ s) :
    rothFinsuppL1 f = ∑ a ∈ s, (f a).natAbs := by
  unfold rothFinsuppL1
  apply Finset.sum_subset hfs
  intro a ha hnot
  rw [Finsupp.notMem_support_iff.mp hnot]
  simp

lemma rothFinsuppL1_add_h {α : Type*} (f g : α →₀ ℤ) :
    rothFinsuppL1 (f + g) ≤ rothFinsuppL1 f + rothFinsuppL1 g := by
  classical
  let s := f.support ∪ g.support
  rw [rothFinsuppL1_sum_superset_h (f + g) s Finsupp.support_add]
  rw [rothFinsuppL1_sum_superset_h f s Finset.subset_union_left]
  rw [rothFinsuppL1_sum_superset_h g s Finset.subset_union_right]
  rw [← Finset.sum_add_distrib]
  gcongr with a ha
  exact Int.natAbs_add_le _ _

lemma rothFinsuppL1_neg_h {α : Type*} (f : α →₀ ℤ) :
    rothFinsuppL1 (-f) = rothFinsuppL1 f := by
  classical
  unfold rothFinsuppL1
  rw [Finsupp.support_neg]
  congr with a
  exact Int.natAbs_neg _

lemma rothFinsuppL1_single_h {α : Type*} (a : α) (c : ℤ) :
    rothFinsuppL1 (Finsupp.single a c) = c.natAbs := by
  classical
  by_cases hc : c = 0
  · simp [hc, rothFinsuppL1]
  · simp [rothFinsuppL1, hc]

lemma rothFinsuppL1_apply_le_h {α : Type*} (f : α →₀ ℤ) (a : α) :
    (f a).natAbs ≤ rothFinsuppL1 f := by
  classical
  by_cases ha : f a = 0
  · simp [ha]
  · exact Finset.single_le_sum (fun b _hb ↦ Nat.zero_le (f b).natAbs)
      (Finsupp.mem_support_iff.mpr ha)

lemma rothMvL1_coeff_le_h {m : ℕ} (P : MvPolynomial (Fin m) ℤ)
    (i : RothMvIndex m) : (P.coeff i).natAbs ≤ rothMvL1 P :=
  rothFinsuppL1_apply_le_h P.coeff i

lemma rothMvL1_eq_sum_h {m : ℕ} (P : MvPolynomial (Fin m) ℤ) :
    rothMvL1 P = ∑ i ∈ P.support, (P.coeff i).natAbs := by
  unfold rothMvL1 rothFinsuppL1
  rw [← MvPolynomial.finsupp_support_eq_support]

lemma rothMvL1_monomial_h {m : ℕ} (i : RothMvIndex m) (c : ℤ) :
    rothMvL1 (MvPolynomial.monomial i c) = c.natAbs := by
  change rothFinsuppL1 (Finsupp.single i c) = c.natAbs
  exact rothFinsuppL1_single_h i c

lemma rothMvL1_neg_h {m : ℕ} (P : MvPolynomial (Fin m) ℤ) :
    rothMvL1 (-P) = rothMvL1 P :=
  rothFinsuppL1_neg_h P.coeff

lemma rothMvL1_finset_sum_h {m : ℕ} {ι : Type*} (s : Finset ι)
    (P : ι → MvPolynomial (Fin m) ℤ) :
    rothMvL1 (∑ a ∈ s, P a) ≤ ∑ a ∈ s, rothMvL1 (P a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rothMvL1, rothFinsuppL1]
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (rothFinsuppL1_add_h _ _).trans (Nat.add_le_add_left ih _)

lemma rothMvL1_mul_h {m : ℕ} (P Q : MvPolynomial (Fin m) ℤ) :
    rothMvL1 (P * Q) ≤ rothMvL1 P * rothMvL1 Q := by
  classical
  rw [MvPolynomial.mul_def, Finsupp.sum]
  calc
    rothMvL1 (∑ a ∈ P.support,
        Q.coeff.sum fun b d ↦ MvPolynomial.monomial (a + b) (P.coeff a * d))
        ≤ ∑ a ∈ P.support,
          rothMvL1 (Q.coeff.sum fun b d ↦
            MvPolynomial.monomial (a + b) (P.coeff a * d)) :=
      rothMvL1_finset_sum_h P.support _
    _ = ∑ a ∈ P.support,
          rothMvL1 (∑ b ∈ Q.support,
            MvPolynomial.monomial (a + b) (P.coeff a * Q.coeff b)) := by
      congr with a
    _ ≤ ∑ a ∈ P.support, ∑ b ∈ Q.support,
          rothMvL1 (MvPolynomial.monomial (a + b) (P.coeff a * Q.coeff b)) := by
      gcongr with a ha
      exact rothMvL1_finset_sum_h Q.support _
    _ = ∑ a ∈ P.support, (P.coeff a).natAbs * rothMvL1 Q := by
      congr with a
      simp_rw [rothMvL1_monomial_h, Int.natAbs_mul]
      unfold rothMvL1 rothFinsuppL1
      rw [← MvPolynomial.finsupp_support_eq_support, ← Finset.mul_sum]
    _ = rothMvL1 P * rothMvL1 Q := by
      unfold rothMvL1 rothFinsuppL1
      rw [← MvPolynomial.finsupp_support_eq_support, Finset.sum_mul]

lemma rothMvL1_one_h {m : ℕ} :
    rothMvL1 (1 : MvPolynomial (Fin m) ℤ) = 1 := by
  rw [show (1 : MvPolynomial (Fin m) ℤ) = MvPolynomial.monomial 0 1 by simp,
    rothMvL1_monomial_h]
  norm_num

lemma rothMvL1_finset_prod_h {m : ℕ} {J : Type*}
    (s : Finset J) (P : J → MvPolynomial (Fin m) ℤ) :
    rothMvL1 (∏ j ∈ s, P j) ≤ ∏ j ∈ s, rothMvL1 (P j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rothMvL1_one_h]
  | @insert j s hjs ih =>
      simp only [Finset.prod_insert hjs]
      exact (rothMvL1_mul_h _ _).trans (Nat.mul_le_mul_left _ ih)

lemma rothMvL1_det_le_h {m k B : ℕ}
    (M : Matrix (Fin k) (Fin k) (MvPolynomial (Fin m) ℤ))
    (hM : ∀ s t, rothMvL1 (M s t) ≤ B) :
    rothMvL1 M.det ≤ k.factorial * B ^ k := by
  classical
  rw [Matrix.det_apply]
  calc
    _ ≤
        ∑ σ ∈ Finset.univ,
          rothMvL1 (Equiv.Perm.sign σ • ∏ i, M (σ i) i) :=
      rothMvL1_finset_sum_h Finset.univ _
    _ = ∑ σ : Equiv.Perm (Fin k), rothMvL1 (∏ i, M (σ i) i) := by
      apply Finset.sum_congr rfl
      intro σ _hσ
      obtain hsign | hsign := Int.units_eq_one_or (Equiv.Perm.sign σ)
      · simp [hsign]
      · simp [hsign, rothMvL1_neg_h]
    _ ≤ ∑ _σ : Equiv.Perm (Fin k), B ^ k := by
      gcongr with σ
      calc
        _ ≤ ∏ i, rothMvL1 (M (σ i) i) :=
          rothMvL1_finset_prod_h Finset.univ _
        _ ≤ ∏ _i : Fin k, B := by
          gcongr with i
          exact hM (σ i) i
        _ = B ^ k := by simp
    _ = k.factorial * B ^ k := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
      rfl

lemma rothDegreeBound_add_h {m : ℕ}
    {P Q : MvPolynomial (Fin m) ℤ} {r : Fin m → ℕ}
    (hP : rothDegreeBound P r) (hQ : rothDegreeBound Q r) :
    rothDegreeBound (P + Q) r := by
  intro i hi h
  rcases Finset.mem_union.mp (MvPolynomial.support_add hi) with hiP | hiQ
  · exact hP i hiP h
  · exact hQ i hiQ h

lemma rothDegreeBound_mul_h {m : ℕ}
    {P Q : MvPolynomial (Fin m) ℤ} {r s : Fin m → ℕ}
    (hP : rothDegreeBound P r) (hQ : rothDegreeBound Q s) :
    rothDegreeBound (P * Q) (fun h ↦ r h + s h) := by
  intro i hi h
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q hi)
  rw [← huv, Finsupp.add_apply]
  exact Nat.add_le_add (hP u hu h) (hQ v hv h)

lemma rothDegreeBound_smul_h {m : ℕ}
    {P : MvPolynomial (Fin m) ℤ} {r : Fin m → ℕ}
    (hP : rothDegreeBound P r) (c : ℤ) : rothDegreeBound (c • P) r := by
  intro i hi h
  exact hP i (MvPolynomial.support_smul hi) h

lemma rothDegreeBound_finset_sum_h {m : ℕ} {J : Type*}
    (s : Finset J) {P : J → MvPolynomial (Fin m) ℤ} {r : Fin m → ℕ}
    (hP : ∀ j ∈ s, rothDegreeBound (P j) r) :
    rothDegreeBound (∑ j ∈ s, P j) r := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rothDegreeBound]
  | @insert j s hjs ih =>
      rw [Finset.sum_insert hjs]
      exact rothDegreeBound_add_h (hP j (Finset.mem_insert_self _ _))
        (ih fun t ht ↦ hP t (Finset.mem_insert_of_mem ht))

lemma rothDegreeBound_finset_prod_h {m : ℕ} {J : Type*}
    (s : Finset J) {P : J → MvPolynomial (Fin m) ℤ} {r : Fin m → ℕ}
    (hP : ∀ j ∈ s, rothDegreeBound (P j) r) :
    rothDegreeBound (∏ j ∈ s, P j) (fun h ↦ s.card * r h) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro i hi h
      simp only [Finset.card_empty, zero_mul]
      rw [Finset.prod_empty, MvPolynomial.support_one] at hi
      rw [Finset.mem_singleton.mp hi]
      simp
  | @insert j s hjs ih =>
      rw [Finset.prod_insert hjs]
      have hmul := rothDegreeBound_mul_h
        (hP j (Finset.mem_insert_self _ _))
        (ih fun t ht ↦ hP t (Finset.mem_insert_of_mem ht))
      simpa [Finset.card_insert_of_notMem hjs, Nat.add_mul, add_comm] using hmul

lemma rothDegreeBound_det_h {m k : ℕ}
    (M : Matrix (Fin k) (Fin k) (MvPolynomial (Fin m) ℤ))
    (r : Fin m → ℕ) (hM : ∀ s t, rothDegreeBound (M s t) r) :
    rothDegreeBound M.det (fun h ↦ k * r h) := by
  classical
  rw [Matrix.det_apply]
  apply rothDegreeBound_finset_sum_h Finset.univ
  intro σ _hσ
  apply rothDegreeBound_smul_h
  simpa using rothDegreeBound_finset_prod_h Finset.univ
    (fun t _ht ↦ hM (σ t) t)

lemma rothDegreeBoundOver_hasse_h {m : ℕ} {R : Type*} [CommSemiring R]
    {P : MvPolynomial (Fin m) R} {r : Fin m → ℕ} (hP : rothDegreeBoundOver P r)
    (i : RothMvIndex m) :
    rothDegreeBoundOver (rothMvHasse i P) r := by
  intro k hk h
  have hcoeff := MvPolynomial.mem_support_iff.mp hk
  rw [rothMvHasse_coeff_h] at hcoeff
  have hPk : P.coeff (k + i) ≠ 0 := by
    intro hz
    exact hcoeff (by rw [hz, mul_zero])
  have hmem : k + i ∈ P.support := MvPolynomial.mem_support_iff.mpr hPk
  exact (Nat.le_add_right (k h) (i h)).trans (hP (k + i) hmem h)

lemma rothHasseDet_degreeBound_h {m k : ℕ}
    {P : MvPolynomial (Fin m) ℤ} {r : Fin m → ℕ}
    (hP : rothDegreeBound P r) (u v : Fin k → RothMvIndex m) :
    rothDegreeBound (rothHasseDet P u v) (fun h ↦ k * r h) := by
  apply rothDegreeBound_det_h
  intro s t
  exact rothDegreeBoundOver_hasse_h hP (u s + v t)

lemma rothDegreeBoundOver_map_h {m : ℕ} {R S : Type*}
    [CommSemiring R] [CommSemiring S] (f : R →+* S)
    {P : MvPolynomial (Fin m) R} {r : Fin m → ℕ} (hP : rothDegreeBoundOver P r) :
    rothDegreeBoundOver (MvPolynomial.map f P) r := by
  intro k hk h
  exact hP k (MvPolynomial.support_map_subset f P hk) h

lemma roth_exists_generalized_wronskian_h {m k : ℕ}
    (f : Fin k → MvPolynomial (Fin m) ℚ) (r : Fin m → ℕ)
    (hf : LinearIndependent ℚ f) (hdeg : ∀ j, rothDegreeBoundOver (f j) r) :
    ∃ i : Fin k → RothMvIndex m,
      (∀ s, rothMvOrder (i s) ≤ s) ∧
        (Matrix.det fun s j ↦ rothMvHasse (i s) (f j)) ≠ 0 := by
  classical
  let D := 2 + ∑ h, r h
  have hD : 1 < D := by
    dsimp [D]
    omega
  have hb : ∀ j, rothKroneckerBounded D (f j) := by
    intro j i hi h
    have hir := hdeg j i hi h
    have hrsum : r h ≤ ∑ t, r t := by
      exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ h)
    dsimp [D]
    omega
  exact roth_exists_generalized_wronskian_of_bounded_h hD f hf hb

lemma roth_equivMapDomain_symm_h {A B M : Type*} [Zero M]
    (e : A ≃ B) (d : B →₀ M) :
    Finsupp.equivMapDomain e (Finsupp.equivMapDomain e.symm d) = d := by
  ext b
  simp [Finsupp.equivMapDomain_apply]

lemma rothLastIndex_castSucc_h {n : ℕ} (i : RothMvIndex n) (a : ℕ)
    (h : Fin n) : rothLastIndex i a h.castSucc = i h := by
  have heq : (Finsupp.equivCongrLeft finSuccEquivLast) (rothLastIndex i a) =
      Finsupp.optionElim a i := by
    simpa [rothLastIndex, Finsupp.equivCongrLeft_apply] using
      roth_equivMapDomain_symm_h finSuccEquivLast (Finsupp.optionElim a i)
  have := congrArg (fun d : Option (Fin n) →₀ ℕ ↦ d (some h)) heq
  simpa [Finsupp.equivCongrLeft_apply, Finsupp.equivMapDomain_eq_mapDomain] using this

lemma rothLastIndex_last_h {n : ℕ} (i : RothMvIndex n) (a : ℕ) :
    rothLastIndex i a (Fin.last n) = a := by
  have heq : (Finsupp.equivCongrLeft finSuccEquivLast) (rothLastIndex i a) =
      Finsupp.optionElim a i := by
    simpa [rothLastIndex, Finsupp.equivCongrLeft_apply] using
      roth_equivMapDomain_symm_h finSuccEquivLast (Finsupp.optionElim a i)
  have := congrArg (fun d : Option (Fin n) →₀ ℕ ↦ d none) heq
  simpa [Finsupp.equivCongrLeft_apply, Finsupp.equivMapDomain_eq_mapDomain] using this

lemma rothLastTail_apply_h {n : ℕ} (d : RothMvIndex (n + 1)) (h : Fin n) :
    rothLastTail d h = d h.castSucc := by
  simp [rothLastTail, Finsupp.equivCongrLeft_apply, Finsupp.equivMapDomain_apply]

lemma rothLastIndex_eta_h {n : ℕ} (d : RothMvIndex (n + 1)) :
    rothLastIndex (rothLastTail d) (d (Fin.last n)) = d := by
  ext h
  refine Fin.lastCases ?_ (fun j ↦ ?_) h
  · rw [rothLastIndex_last_h]
  · rw [rothLastIndex_castSucc_h, rothLastTail_apply_h]

lemma rothLastIndex_left_injective_h {n : ℕ} (a : ℕ) :
    Function.Injective (fun i : RothMvIndex n ↦ rothLastIndex i a) := by
  intro i j hij
  ext h
  have := congrArg (fun d : RothMvIndex (n + 1) ↦ d h.castSucc) hij
  simpa [rothLastIndex_castSucc_h] using this

lemma rothLastIndex_add_h {n : ℕ} (i j : RothMvIndex n) (a b : ℕ) :
    rothLastIndex (i + j) (a + b) = rothLastIndex i a + rothLastIndex j b := by
  ext h
  refine Fin.lastCases ?_ (fun t ↦ ?_) h
  · simp [rothLastIndex_last_h]
  · simp [rothLastIndex_castSucc_h]

lemma rothMvWeight_lastIndex_h {n : ℕ} (r : Fin (n + 1) → ℕ)
    (i : RothMvIndex n) (a : ℕ) :
    rothMvWeight r (rothLastIndex i a) =
      rothMvWeight (fun h ↦ r h.castSucc) i + (a : ℝ) / r (Fin.last n) := by
  unfold rothMvWeight
  rw [Fin.sum_univ_castSucc]
  simp only [rothLastIndex_castSucc_h, rothLastIndex_last_h]

lemma rothLastEquiv_coeff_coeff_h {n : ℕ} {R : Type*} [CommSemiring R]
    (P : MvPolynomial (Fin (n + 1)) R) (a : ℕ) (i : RothMvIndex n) :
    ((rothLastEquiv R n P).coeff a).coeff i = P.coeff (rothLastIndex i a) := by
  let d := rothLastIndex i a
  have hmap : Finsupp.mapDomain finSuccEquivLast d = Finsupp.optionElim a i := by
    rw [← Finsupp.equivMapDomain_eq_mapDomain]
    change (Finsupp.equivCongrLeft finSuccEquivLast) d = _
    simpa [d, rothLastIndex, Finsupp.equivCongrLeft_apply] using
      roth_equivMapDomain_symm_h finSuccEquivLast (Finsupp.optionElim a i)
  unfold rothLastEquiv
  rw [AlgEquiv.trans_apply, MvPolynomial.optionEquivLeft_coeff_coeff]
  rw [← hmap, MvPolynomial.renameEquiv_apply,
    MvPolynomial.coeff_rename_mapDomain finSuccEquivLast finSuccEquivLast.injective]

lemma rothLastEquiv_natDegree_le_h {n : ℕ} {R : Type*} [CommSemiring R]
    {P : MvPolynomial (Fin (n + 1)) R} {r : Fin (n + 1) → ℕ}
    (hP : rothDegreeBoundOver P r) :
    (rothLastEquiv R n P).natDegree ≤ r (Fin.last n) := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro a ha
  by_contra hne
  obtain ⟨i, hi⟩ := MvPolynomial.support_nonempty.mpr hne
  have hcoeff : P.coeff (rothLastIndex i a) ≠ 0 := by
    rw [← rothLastEquiv_coeff_coeff_h]
    exact MvPolynomial.mem_support_iff.mp hi
  have hmem : rothLastIndex i a ∈ P.support := MvPolynomial.mem_support_iff.mpr hcoeff
  have := hP (rothLastIndex i a) hmem (Fin.last n)
  rw [rothLastIndex_last_h] at this
  omega

lemma rothLastEquiv_coeff_degreeBound_h {n : ℕ} {R : Type*}
    [CommSemiring R] {P : MvPolynomial (Fin (n + 1)) R}
    {r : Fin (n + 1) → ℕ} (hP : rothDegreeBoundOver P r) (a : ℕ) :
    rothDegreeBoundOver ((rothLastEquiv R n P).coeff a)
      (fun h ↦ r h.castSucc) := by
  intro i hi h
  have hcoeff : P.coeff (rothLastIndex i a) ≠ 0 := by
    rw [← rothLastEquiv_coeff_coeff_h]
    exact MvPolynomial.mem_support_iff.mp hi
  simpa [rothLastIndex_castSucc_h] using
    hP (rothLastIndex i a) (MvPolynomial.mem_support_iff.mpr hcoeff) h.castSucc

lemma rothLastEquiv_map_h {n : ℕ} {R S : Type*}
    [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (P : MvPolynomial (Fin (n + 1)) R) :
    rothLastEquiv S n (MvPolynomial.map f P) =
      Polynomial.map (MvPolynomial.map f) (rothLastEquiv R n P) := by
  ext a i
  rw [rothLastEquiv_coeff_coeff_h, MvPolynomial.coeff_map, Polynomial.coeff_map,
    MvPolynomial.coeff_map, rothLastEquiv_coeff_coeff_h]

lemma rothMvL1_lastEquiv_coeff_le_h {n : ℕ}
    (P : MvPolynomial (Fin (n + 1)) ℤ) (a : ℕ) :
    rothMvL1 ((rothLastEquiv ℤ n P).coeff a) ≤ rothMvL1 P := by
  classical
  let Q := (rothLastEquiv ℤ n P).coeff a
  let f : RothMvIndex n → RothMvIndex (n + 1) := fun i ↦ rothLastIndex i a
  have hf : Function.Injective f := rothLastIndex_left_injective_h a
  have hsubset : Q.support.image f ⊆ P.support := by
    intro d hd
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hd
    apply MvPolynomial.mem_support_iff.mpr
    rw [← rothLastEquiv_coeff_coeff_h]
    exact MvPolynomial.mem_support_iff.mp hi
  rw [rothMvL1_eq_sum_h, rothMvL1_eq_sum_h]
  calc
    ∑ i ∈ Q.support, (Q.coeff i).natAbs =
        ∑ d ∈ Q.support.image f, (P.coeff d).natAbs := by
      rw [Finset.sum_image]
      · apply Finset.sum_congr rfl
        intro i _hi
        rw [rothLastEquiv_coeff_coeff_h]
      · exact fun _i _hi _j _hj hij ↦ hf hij
    _ ≤ ∑ d ∈ P.support, (P.coeff d).natAbs :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ ↦ Nat.zero_le _)

lemma rothLastEquiv_eval_h {n : ℕ} {R : Type*} [CommSemiring R]
    (x : Fin n → R) (y : R) (P : MvPolynomial (Fin (n + 1)) R) :
    MvPolynomial.eval (Fin.lastCases y x) P =
      Polynomial.eval y
        (Polynomial.map (MvPolynomial.eval x) (rothLastEquiv R n P)) := by
  have h := MvPolynomial.optionEquivLeft_elim_eval R (Fin n) x y
    ((MvPolynomial.renameEquiv R finSuccEquivLast) P)
  rw [MvPolynomial.renameEquiv_apply, MvPolynomial.eval_rename] at h
  change MvPolynomial.eval _ P = _ at h
  have hfun : (fun z : Fin (n + 1) ↦ Fin.lastCases y x z) =
      (fun z : Option (Fin n) ↦ z.elim y x) ∘ finSuccEquivLast := by
    funext z
    refine Fin.lastCases ?_ (fun j ↦ ?_) z <;> simp
  rw [hfun]
  simpa [rothLastEquiv] using h

lemma rothLastSlice_coeff_h {n : ℕ}
    (P : MvPolynomial (Fin (n + 1)) ℤ) (i : RothMvIndex n) (a : ℕ) :
    (rothLastSlice P i).coeff a = P.coeff (rothLastIndex i a) := by
  classical
  rw [rothLastSlice, Polynomial.finsetSum_coeff]
  by_cases ha : a ∈ (rothLastEquiv ℤ n P).support
  · rw [Finset.sum_eq_single a]
    · simp [rothLastEquiv_coeff_coeff_h]
    · intro b hb hba
      simp [Polynomial.coeff_monomial, hba]
    · exact fun hnot ↦ (hnot ha).elim
  · rw [Finset.sum_eq_zero]
    · rw [← rothLastEquiv_coeff_coeff_h]
      simpa using (congrArg (fun Q : MvPolynomial (Fin n) ℤ ↦ Q.coeff i)
        (Polynomial.notMem_support_iff.mp ha)).symm
    · intro b hb
      have hba : b ≠ a := fun hba ↦ ha (hba ▸ hb)
      simp [Polynomial.coeff_monomial, hba]

lemma rothLastSlice_map_eq_C_mul_of_factorization_h {n : ℕ}
    (U : MvPolynomial (Fin (n + 1)) ℤ) (V : MvPolynomial (Fin n) ℤ)
    (W : ℚ[X]) (i : RothMvIndex n)
    (hfactor :
      rothLastEquiv ℚ n (MvPolynomial.map (algebraMap ℤ ℚ) U) =
        Polynomial.C (MvPolynomial.map (algebraMap ℤ ℚ) V) *
          Polynomial.map MvPolynomial.C W) :
    Polynomial.map (algebraMap ℤ ℚ) (rothLastSlice U i) =
      Polynomial.C (V.coeff i : ℚ) * W := by
  ext a
  have hcoeff := congrArg
    (fun Q : Polynomial (MvPolynomial (Fin n) ℚ) ↦ (Q.coeff a).coeff i) hfactor
  rw [Polynomial.coeff_map, rothLastSlice_coeff_h]
  rw [rothLastEquiv_coeff_coeff_h, MvPolynomial.coeff_map] at hcoeff
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_map] at hcoeff
  rw [mul_comm, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map] at hcoeff
  simpa [mul_comm] using hcoeff

lemma rothLastEquiv_hasse_coeff_h {n : ℕ} {R : Type*} [CommSemiring R]
    (P : MvPolynomial (Fin (n + 1)) R) (i : RothMvIndex n) (a b : ℕ) :
    (rothLastEquiv R n (rothMvHasse (rothLastIndex i a) P)).coeff b =
      rothMvHasse i ((Polynomial.hasseDeriv a (rothLastEquiv R n P)).coeff b) := by
  ext j
  rw [rothLastEquiv_coeff_coeff_h, rothMvHasse_coeff_h, rothMvHasse_coeff_h,
    Polynomial.hasseDeriv_coeff, ← MvPolynomial.C_eq_coe_nat,
    MvPolynomial.coeff_C_mul, rothLastEquiv_coeff_coeff_h]
  rw [Fin.prod_univ_castSucc]
  simp only [rothLastIndex_add_h, rothLastIndex_castSucc_h, rothLastIndex_last_h,
    Finsupp.add_apply]
  ring

lemma rothLastEquiv_hasse_of_tensor_decomposition_h {n k : ℕ}
    (Q : Polynomial (MvPolynomial (Fin n) ℚ))
    (phi : Fin k → MvPolynomial (Fin n) ℚ) (psi : Fin k → ℚ[X])
    (hQ : Q = ∑ j, Polynomial.C (phi j) * Polynomial.map MvPolynomial.C (psi j))
    (i : RothMvIndex n) (a : ℕ) :
    rothLastEquiv ℚ n
        (rothMvHasse (rothLastIndex i a) ((rothLastEquiv ℚ n).symm Q)) =
      ∑ j, Polynomial.C (rothMvHasse i (phi j)) *
        Polynomial.map MvPolynomial.C (Polynomial.hasseDeriv a (psi j)) := by
  ext b l
  rw [rothLastEquiv_hasse_coeff_h, AlgEquiv.apply_symm_apply,
    Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.hasseDeriv_coeff]
  rw [hQ, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_map]
  rw [← MvPolynomial.C_eq_coe_nat, ← MvPolynomial.smul_eq_C_mul,
    rothMvHasse_smul_h, rothMvHasse_finset_sum_h, MvPolynomial.coeff_smul,
    MvPolynomial.coeff_sum]
  rw [Finset.smul_sum, MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [show phi j * MvPolynomial.C ((psi j).coeff (b + a)) =
      (psi j).coeff (b + a) • phi j by
        rw [MvPolynomial.smul_eq_C_mul]
        ring,
    rothMvHasse_smul_h, MvPolynomial.coeff_smul]
  simp only [smul_eq_mul]
  rw [mul_comm (rothMvHasse i (phi j)), MvPolynomial.coeff_C_mul,
    Polynomial.hasseDeriv_coeff]
  ring

lemma roth_exists_tensor_decomposition_h {n : ℕ}
    (Q : Polynomial (MvPolynomial (Fin n) ℚ)) (hQ : Q ≠ 0) :
    ∃ (k : ℕ) (phi : Fin k → MvPolynomial (Fin n) ℚ) (psi : Fin k → ℚ[X]),
      0 < k ∧ k ≤ Q.natDegree + 1 ∧
        (∀ j, ∃ a ∈ Q.support, phi j = Q.coeff a) ∧
        (∀ j, (psi j).natDegree ≤ Q.natDegree) ∧
        LinearIndependent ℚ phi ∧ LinearIndependent ℚ psi ∧
        Q = ∑ j, Polynomial.C (phi j) * Polynomial.map MvPolynomial.C (psi j) := by
  classical
  let S : Set (MvPolynomial (Fin n) ℚ) :=
    Set.range fun a : Q.support ↦ Q.coeff a
  let _ : Module.Finite ℚ (Submodule.span ℚ S) :=
    Module.Finite.span_of_finite ℚ (Set.finite_range _)
  let k := Module.finrank ℚ (Submodule.span ℚ S)
  have hspanNontrivial : Nontrivial (Submodule.span ℚ S) := by
    obtain ⟨b, hb⟩ := Polynomial.support_nonempty.mpr hQ
    have hbne : Q.coeff b ≠ 0 := Polynomial.mem_support_iff.mp hb
    have hbmem : Q.coeff b ∈ Submodule.span ℚ S :=
      Submodule.subset_span ⟨⟨b, hb⟩, rfl⟩
    rw [nontrivial_iff]
    refine ⟨⟨Q.coeff b, hbmem⟩, 0, ?_⟩
    intro heq
    apply hbne
    exact congrArg Subtype.val heq
  have hkPos : 0 < k := Module.finrank_pos_iff.mpr hspanNontrivial
  obtain ⟨phi, hphiS, hphiSpan, hphi⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℚ S
  have hcoeffSpan : ∀ a : ℕ, Q.coeff a ∈ Submodule.span ℚ (Set.range phi) := by
    intro a
    rw [hphiSpan]
    by_cases ha : a ∈ Q.support
    · exact Submodule.subset_span ⟨⟨a, ha⟩, rfl⟩
    · rw [Polynomial.notMem_support_iff.mp ha]
      exact Submodule.zero_mem _
  have hcoordExists : ∀ a : ℕ, ∃ c : Fin k → ℚ,
      ∑ j, c j • phi j = Q.coeff a := by
    intro a
    exact (Submodule.mem_span_range_iff_exists_fun ℚ).mp (hcoeffSpan a)
  choose c hc using hcoordExists
  let psi : Fin k → ℚ[X] := fun j ↦
    ∑ a ∈ Q.support, Polynomial.monomial a (c a j)
  have hcZero {a : ℕ} (ha : a ∉ Q.support) : ∀ j, c a j = 0 := by
    have hsum : ∑ j, c a j • phi j = 0 := by
      rw [hc a, Polynomial.notMem_support_iff.mp ha]
    exact Fintype.linearIndependent_iff.mp hphi (c a) hsum
  have hpsiCoeff : ∀ (j : Fin k) (a : ℕ), (psi j).coeff a = c a j := by
    intro j a
    dsimp [psi]
    rw [Polynomial.finsetSum_coeff]
    by_cases ha : a ∈ Q.support
    · rw [Finset.sum_eq_single a]
      · simp
      · intro b hb hba
        simp [Polynomial.coeff_monomial, hba]
      · exact fun hnot ↦ (hnot ha).elim
    · rw [Finset.sum_eq_zero]
      · exact (hcZero ha j).symm
      · intro b hb
        have hba : b ≠ a := fun hba ↦ ha (hba ▸ hb)
        simp [Polynomial.coeff_monomial, hba]
  choose a ha using hphiS
  have haCoeff : ∀ j, phi j = Q.coeff (a j) := fun j ↦ (ha j).symm
  have haInjective : Function.Injective a := by
    intro i j hij
    apply hphi.injective
    rw [haCoeff i, haCoeff j, hij]
  have hkSupport : k ≤ Q.support.card := by
    simpa using Fintype.card_le_of_injective a haInjective
  have hsupportDegree : Q.support.card ≤ Q.natDegree + 1 := by
    simpa using Finset.card_le_card Polynomial.supp_subset_range_natDegree_succ
  have hkDegree : k ≤ Q.natDegree + 1 := hkSupport.trans hsupportDegree
  have hcSelected : ∀ (j t : Fin k), c (a j) t = if t = j then 1 else 0 := by
    intro j
    let e : Fin k → ℚ := fun t ↦ if t = j then 1 else 0
    have heSum : ∑ t, e t • phi t = phi j := by
      simp [e]
    have hdiff : ∑ t, (c (a j) t - e t) • phi t = 0 := by
      simp only [sub_smul]
      rw [Finset.sum_sub_distrib]
      rw [hc (a j), ← haCoeff j, heSum, sub_self]
    have hz := Fintype.linearIndependent_iff.mp hphi
      (fun t ↦ c (a j) t - e t) hdiff
    intro t
    exact sub_eq_zero.mp (hz t)
  have hpsi : LinearIndependent ℚ psi := by
    rw [Fintype.linearIndependent_iff]
    intro d hd j
    have hcoeff := congrArg (fun P : ℚ[X] ↦ P.coeff (a j)) hd
    have hcoeff' : ∑ t, d t * (psi t).coeff (a j) = 0 := by
      simpa using hcoeff
    have hcoeff'' : ∑ t, d t * c (a j) t = 0 := calc
        _ = ∑ t, d t * (psi t).coeff (a j) := by
          apply Finset.sum_congr rfl
          intro t _ht
          rw [hpsiCoeff]
        _ = 0 := hcoeff'
    simpa [hcSelected j] using hcoeff''
  have hpsiDegree : ∀ j, (psi j).natDegree ≤ Q.natDegree := by
    intro j
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro b hb
    rw [hpsiCoeff]
    apply hcZero
    intro hmem
    exact (not_le_of_gt hb) (Polynomial.le_natDegree_of_mem_supp b hmem)
  have hdecomp : Q =
      ∑ j, Polynomial.C (phi j) * Polynomial.map MvPolynomial.C (psi j) := by
    apply Polynomial.ext
    intro b
    rw [Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul, Polynomial.coeff_map, hpsiCoeff]
    simpa [Algebra.smul_def, mul_comm] using (hc b).symm
  exact ⟨k, phi, psi, hkPos, hkDegree,
    fun j ↦ ⟨a j, (a j).property, haCoeff j⟩, hpsiDegree, hphi, hpsi, hdecomp⟩

lemma rothHasseDet_lastEquiv_factorization_h {n k : ℕ}
    (P : MvPolynomial (Fin (n + 1)) ℚ)
    (phi : Fin k → MvPolynomial (Fin n) ℚ) (psi : Fin k → ℚ[X])
    (hP : rothLastEquiv ℚ n P =
      ∑ j, Polynomial.C (phi j) * Polynomial.map MvPolynomial.C (psi j))
    (i : Fin k → RothMvIndex n) :
    rothLastEquiv ℚ n
        (rothHasseDet P
          (fun s ↦ rothLastIndex (i s) 0)
          (fun t ↦ rothLastIndex 0 t.val)) =
      Polynomial.C (Matrix.det fun s j ↦ rothMvHasse (i s) (phi j)) *
        Polynomial.map MvPolynomial.C
          (Matrix.det fun t j ↦ Polynomial.hasseDeriv t.val (psi j)) := by
  classical
  let V : Matrix (Fin k) (Fin k) (MvPolynomial (Fin n) ℚ) :=
    fun s j ↦ rothMvHasse (i s) (phi j)
  let H : Matrix (Fin k) (Fin k) ℚ[X] :=
    fun t j ↦ Polynomial.hasseDeriv t.val (psi j)
  let B : Matrix (Fin k) (Fin k) (MvPolynomial (Fin (n + 1)) ℚ) :=
    fun s t ↦ rothMvHasse
      (rothLastIndex (i s) 0 + rothLastIndex 0 t.val) P
  let A : Matrix (Fin k) (Fin k) (Polynomial (MvPolynomial (Fin n) ℚ)) :=
    fun s t ↦ rothLastEquiv ℚ n
      (rothMvHasse (rothLastIndex (i s) t.val) P)
  let VC : Matrix (Fin k) (Fin k) (Polynomial (MvPolynomial (Fin n) ℚ)) :=
    fun s j ↦ Polynomial.C (V s j)
  let HC : Matrix (Fin k) (Fin k) (Polynomial (MvPolynomial (Fin n) ℚ)) :=
    fun j t ↦ Polynomial.map MvPolynomial.C (H t j)
  have hA : A = VC * HC := by
    funext s t
    rw [Matrix.mul_apply]
    dsimp [A, VC, HC, V, H]
    simpa using rothLastEquiv_hasse_of_tensor_decomposition_h
      (rothLastEquiv ℚ n P) phi psi hP (i s) t.val
  have hleft : rothLastEquiv ℚ n
        (rothHasseDet P
          (fun s ↦ rothLastIndex (i s) 0)
          (fun t ↦ rothLastIndex 0 t.val)) = A.det := by
    unfold rothHasseDet
    change rothLastEquiv ℚ n B.det = A.det
    calc
      rothLastEquiv ℚ n B.det =
          ((rothLastEquiv ℚ n).toRingHom.mapMatrix B).det :=
        RingHom.map_det (rothLastEquiv ℚ n).toRingHom B
      _ = A.det := by
        congr 1
        funext s t
        change rothLastEquiv ℚ n
            (rothMvHasse (rothLastIndex (i s) 0 + rothLastIndex 0 t.val) P) =
          rothLastEquiv ℚ n (rothMvHasse (rothLastIndex (i s) t.val) P)
        rw [← rothLastIndex_add_h]
        simp
  rw [hleft, hA, Matrix.det_mul]
  have hVC : VC.det = Polynomial.C V.det := by
    have hmatrix : VC = V.map Polynomial.C := by
      funext s j
      rfl
    rw [hmatrix]
    exact (RingHom.map_det
      (Polynomial.C : MvPolynomial (Fin n) ℚ →+* Polynomial (MvPolynomial (Fin n) ℚ)) V).symm
  have hHC : HC.det = Polynomial.map MvPolynomial.C H.det := by
    let f : ℚ[X] →+* Polynomial (MvPolynomial (Fin n) ℚ) :=
      Polynomial.mapRingHom MvPolynomial.C
    have hmatrix : HC = f.mapMatrix H.transpose := by
      ext j t
      rfl
    have hmapMatrix : f.mapMatrix H.transpose = H.transpose.map f := by
      rfl
    calc
      HC.det = (f.mapMatrix H.transpose).det := congrArg Matrix.det hmatrix
      _ = (H.transpose.map f).det := congrArg Matrix.det hmapMatrix
      _ = f H.transpose.det := (RingHom.map_det f H.transpose).symm
      _ = f H.det := by rw [Matrix.det_transpose]
      _ = Polynomial.map MvPolynomial.C H.det := rfl
  rw [hVC, hHC]

lemma rothMvHasse_eval_last_of_factorization_h {n : ℕ}
    (P : MvPolynomial (Fin (n + 1)) ℚ) (V : MvPolynomial (Fin n) ℚ)
    (W : ℚ[X])
    (hfactor : rothLastEquiv ℚ n P =
      Polynomial.C V * Polynomial.map MvPolynomial.C W)
    (x : Fin n → ℚ) (y : ℚ) (i : RothMvIndex n) (a : ℕ) :
    MvPolynomial.eval (Fin.lastCases y x)
        (rothMvHasse (rothLastIndex i a) P) =
      MvPolynomial.eval x (rothMvHasse i V) *
        (Polynomial.hasseDeriv a W).eval y := by
  let phi : Fin 1 → MvPolynomial (Fin n) ℚ := fun _ ↦ V
  let psi : Fin 1 → ℚ[X] := fun _ ↦ W
  have hdecomp : rothLastEquiv ℚ n P =
      ∑ j, Polynomial.C (phi j) * Polynomial.map MvPolynomial.C (psi j) := by
    rw [hfactor]
    simp [phi, psi]
  have hhasse := rothLastEquiv_hasse_of_tensor_decomposition_h
    (rothLastEquiv ℚ n P) phi psi hdecomp i a
  have hhasse' :
      rothLastEquiv ℚ n (rothMvHasse (rothLastIndex i a) P) =
        Polynomial.C (rothMvHasse i V) *
          Polynomial.map MvPolynomial.C (Polynomial.hasseDeriv a W) := by
    simpa [phi, psi] using hhasse
  have hcomp : (MvPolynomial.eval x).comp MvPolynomial.C = RingHom.id ℚ := by
    ext z
    simp
  rw [rothLastEquiv_eval_h, hhasse', Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_map, hcomp, Polynomial.map_id, Polynomial.eval_mul,
    Polynomial.eval_C]

lemma rothLastSlice_hasse_eval_h {n : ℕ}
    (P : MvPolynomial (Fin (n + 1)) ℤ) (i : RothMvIndex n)
    (a : ℕ) (y : ℚ) :
    MvPolynomial.eval (Fin.lastCases y (fun _ ↦ 0))
        (rothMvHasse (rothLastIndex i a)
          (MvPolynomial.map (algebraMap ℤ ℚ) P)) =
      (Polynomial.hasseDeriv a
        (Polynomial.map (algebraMap ℤ ℚ) (rothLastSlice P i))).eval y := by
  rw [rothLastEquiv_eval_h]
  congr 1
  apply Polynomial.ext
  intro b
  rw [Polynomial.coeff_map, rothLastEquiv_hasse_coeff_h]
  change MvPolynomial.eval (0 : Fin n → ℚ) _ = _
  rw [rothMvHasse_eval_zero_h]
  simp only [Polynomial.hasseDeriv_coeff, Polynomial.coeff_map]
  rw [rothLastSlice_coeff_h]
  rw [← MvPolynomial.C_eq_coe_nat, ← MvPolynomial.smul_eq_C_mul,
    MvPolynomial.coeff_smul]
  rw [rothLastEquiv_coeff_coeff_h, MvPolynomial.coeff_map]
  simp [smul_eq_mul]

lemma rothMvL1_hasse_le_h {m : ℕ} (P : MvPolynomial (Fin m) ℤ)
    (i : RothMvIndex m) (r : Fin m → ℕ) (hdeg : rothDegreeBound P r) :
    rothMvL1 (rothMvHasse i P) ≤ 2 ^ (∑ h, r h) * rothMvL1 P := by
  classical
  unfold rothMvHasse
  rw [Finsupp.sum]
  calc
    rothMvL1 (∑ j ∈ P.support,
        MvPolynomial.monomial (j - i)
          ((∏ h, (Nat.choose (j h) (i h) : ℤ)) * P.coeff j))
        ≤ ∑ j ∈ P.support, rothMvL1
          (MvPolynomial.monomial (j - i)
            ((∏ h, (Nat.choose (j h) (i h) : ℤ)) * P.coeff j)) :=
      rothMvL1_finset_sum_h P.support _
    _ = ∑ j ∈ P.support, (∏ h, Nat.choose (j h) (i h)) * (P.coeff j).natAbs := by
      congr with j
      rw [rothMvL1_monomial_h, Int.natAbs_mul, ← Nat.cast_prod, Int.natAbs_natCast]
    _ ≤ ∑ j ∈ P.support, 2 ^ (∑ h, r h) * (P.coeff j).natAbs := by
      gcongr with j hj
      calc
        _ ≤ ∏ h, 2 ^ j h := by
          gcongr with h
          exact Nat.choose_le_two_pow (j h) (i h)
        _ ≤ ∏ h, 2 ^ r h := by
          gcongr with h
          exact hdeg j hj h
        _ = 2 ^ (∑ h, r h) := Finset.prod_pow_eq_pow_sum Finset.univ r 2
    _ = 2 ^ (∑ h, r h) * rothMvL1 P := by
      unfold rothMvL1 rothFinsuppL1
      rw [← MvPolynomial.finsupp_support_eq_support, Finset.mul_sum]

lemma rothHasseDet_l1_le_h {m k : ℕ}
    (P : MvPolynomial (Fin m) ℤ) (r : Fin m → ℕ)
    (hP : rothDegreeBound P r) (u v : Fin k → RothMvIndex m) :
    rothMvL1 (rothHasseDet P u v) ≤
      k.factorial * (2 ^ (∑ h, r h) * rothMvL1 P) ^ k := by
  apply rothMvL1_det_le_h
  intro s t
  exact rothMvL1_hasse_le_h P (u s + v t) r hP

lemma roth_exists_determinant_data_h {n : ℕ}
    (P : MvPolynomial (Fin (n + 1)) ℤ) (r : Fin (n + 1) → ℕ)
    (hPne : P ≠ 0) (hPdeg : rothDegreeBound P r) :
    Nonempty (RothDeterminantData P r) := by
  classical
  let castQ : ℤ →+* ℚ := algebraMap ℤ ℚ
  let PQ := MvPolynomial.map castQ P
  let Q := rothLastEquiv ℚ n PQ
  have hPQne : PQ ≠ 0 := by
    simpa [PQ] using (MvPolynomial.map_injective castQ Int.cast_injective).ne hPne
  have hQne : Q ≠ 0 := (rothLastEquiv ℚ n).injective.ne hPQne
  obtain ⟨k, phi, psi, hk, hkQ, hphi, hpsiDeg, hphiLI, hpsiLI, hdecomp⟩ :=
    roth_exists_tensor_decomposition_h Q hQne
  have hPQdeg : rothDegreeBoundOver PQ r :=
    rothDegreeBoundOver_map_h castQ hPdeg
  have hQdeg : Q.natDegree ≤ r (Fin.last n) :=
    rothLastEquiv_natDegree_le_h hPQdeg
  have hkR : k ≤ r (Fin.last n) + 1 := hkQ.trans (Nat.add_le_add_right hQdeg 1)
  choose a haQ hphiCoeff using hphi
  let phiZ : Fin k → MvPolynomial (Fin n) ℤ :=
    fun j ↦ (rothLastEquiv ℤ n P).coeff (a j)
  have hphiMap : ∀ j, MvPolynomial.map castQ (phiZ j) = phi j := by
    intro j
    have hmap := congrArg (fun F : Polynomial (MvPolynomial (Fin n) ℚ) ↦
      F.coeff (a j)) (rothLastEquiv_map_h castQ P)
    rw [Polynomial.coeff_map] at hmap
    exact hmap.symm.trans (hphiCoeff j).symm
  have hphiZdeg : ∀ j, rothDegreeBound (phiZ j) (fun h ↦ r h.castSucc) := by
    intro j
    exact rothLastEquiv_coeff_degreeBound_h hPdeg (a j)
  have hphiDeg : ∀ j, rothDegreeBoundOver (phi j) (fun h ↦ r h.castSucc) := by
    intro j
    rw [← hphiMap j]
    exact rothDegreeBoundOver_map_h castQ (hphiZdeg j)
  obtain ⟨row, hrowOrder, hrowDet⟩ :=
    roth_exists_generalized_wronskian_h phi (fun h ↦ r h.castSucc) hphiLI hphiDeg
  let V : MvPolynomial (Fin n) ℤ :=
    Matrix.det fun s j ↦ rothMvHasse (row s) (phiZ j)
  let W : ℚ[X] := Matrix.det fun t j ↦ Polynomial.hasseDeriv t.val (psi j)
  let U : MvPolynomial (Fin (n + 1)) ℤ := rothHasseDet P
    (fun s ↦ rothLastIndex (row s) 0)
    (fun t ↦ rothLastIndex 0 t.val)
  have hVmap : MvPolynomial.map castQ V =
      Matrix.det fun s j ↦ rothMvHasse (row s) (phi j) := by
    let A : Matrix (Fin k) (Fin k) (MvPolynomial (Fin n) ℤ) :=
      fun s j ↦ rothMvHasse (row s) (phiZ j)
    change MvPolynomial.map castQ A.det = _
    rw [RingHom.map_det]
    congr 1
    funext s j
    change MvPolynomial.map castQ (rothMvHasse (row s) (phiZ j)) = _
    rw [rothMvHasse_map_h, hphiMap]
  have hVne : V ≠ 0 := by
    intro hzero
    apply hrowDet
    rw [← hVmap, hzero, map_zero]
  have hWne : W ≠ 0 := roth_poly_hasse_wronskian_ne_zero_h psi hpsiLI
  have hfactor : rothLastEquiv ℚ n (MvPolynomial.map castQ U) =
      Polynomial.C (MvPolynomial.map castQ V) * Polynomial.map MvPolynomial.C W := by
    rw [show MvPolynomial.map castQ U = rothHasseDet PQ
        (fun s ↦ rothLastIndex (row s) 0)
        (fun t ↦ rothLastIndex 0 t.val) by
      dsimp [U, PQ]
      exact rothHasseDet_map_h castQ P _ _]
    rw [hVmap]
    exact rothHasseDet_lastEquiv_factorization_h PQ phi psi hdecomp row
  have hVdegree : rothDegreeBound V (fun h ↦ k * r h.castSucc) := by
    dsimp [V]
    apply rothDegreeBound_det_h
    intro s j
    exact rothDegreeBoundOver_hasse_h (hphiZdeg j) (row s)
  have hUdegree : rothDegreeBound U (fun h ↦ k * r h) := by
    dsimp [U]
    exact rothHasseDet_degreeBound_h hPdeg _ _
  have hVl1 : rothMvL1 V ≤
      k.factorial * (2 ^ (∑ h : Fin n, r h.castSucc) * rothMvL1 P) ^ k := by
    dsimp [V]
    apply rothMvL1_det_le_h
    intro s j
    calc
      rothMvL1 (rothMvHasse (row s) (phiZ j)) ≤
          2 ^ (∑ h : Fin n, r h.castSucc) * rothMvL1 (phiZ j) :=
        rothMvL1_hasse_le_h (phiZ j) (row s) _ (hphiZdeg j)
      _ ≤ 2 ^ (∑ h : Fin n, r h.castSucc) * rothMvL1 P := by
        gcongr
        exact rothMvL1_lastEquiv_coeff_le_h P (a j)
  have hUl1 : rothMvL1 U ≤
      k.factorial * (2 ^ (∑ h, r h) * rothMvL1 P) ^ k := by
    dsimp [U]
    exact rothHasseDet_l1_le_h P r hPdeg _ _
  exact ⟨{
    k := k
    k_pos := hk
    k_le := hkR
    row := row
    row_order := hrowOrder
    V := V
    W := W
    U := U
    V_ne := hVne
    W_ne := hWne
    U_def := rfl
    factorization := hfactor
    V_degree := hVdegree
    U_degree := hUdegree
    V_l1 := hVl1
    U_l1 := hUl1
  }⟩

lemma rothPolyL1_coeff_le_h (P : ℤ[X]) (n : ℕ) :
    (P.coeff n).natAbs ≤ rothPolyL1 P := by
  exact rothFinsuppL1_apply_le_h P.toFinsupp.coeff n

lemma rothPolyL1_eq_sum_h (P : ℤ[X]) :
    rothPolyL1 P = ∑ n ∈ P.support, (P.coeff n).natAbs := by
  unfold rothPolyL1 rothFinsuppL1
  rw [Polynomial.support_toFinsupp]
  simp only [Polynomial.toFinsupp_apply]

lemma rothPolyL1_le_natDegree_succ_mul_h (P : ℤ[X]) (H : ℕ)
    (hcoeff : ∀ n, (P.coeff n).natAbs ≤ H) :
    rothPolyL1 P ≤ (P.natDegree + 1) * H := by
  rw [rothPolyL1_eq_sum_h]
  calc
    _ ≤ ∑ _n ∈ P.support, H := by
      gcongr with n
      exact hcoeff n
    _ = P.support.card * H := by simp
    _ ≤ (P.natDegree + 1) * H := by
      gcongr
      simpa using Finset.card_le_card Polynomial.supp_subset_range_natDegree_succ

lemma rothLastSlice_natDegree_le_h {n : ℕ}
    {P : MvPolynomial (Fin (n + 1)) ℤ} {r : Fin (n + 1) → ℕ}
    (hP : rothDegreeBound P r) (i : RothMvIndex n) :
    (rothLastSlice P i).natDegree ≤ r (Fin.last n) := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro a ha
  rw [rothLastSlice_coeff_h]
  by_contra hne
  have hmem : rothLastIndex i a ∈ P.support := MvPolynomial.mem_support_iff.mpr hne
  have hle := hP (rothLastIndex i a) hmem (Fin.last n)
  rw [rothLastIndex_last_h] at hle
  omega

lemma rothPolyL1_lastSlice_le_h {n : ℕ}
    {P : MvPolynomial (Fin (n + 1)) ℤ} {r : Fin (n + 1) → ℕ}
    (hP : rothDegreeBound P r) (i : RothMvIndex n) :
    rothPolyL1 (rothLastSlice P i) ≤
      (r (Fin.last n) + 1) * rothMvL1 P := by
  calc
    rothPolyL1 (rothLastSlice P i) ≤
        ((rothLastSlice P i).natDegree + 1) * rothMvL1 P :=
      rothPolyL1_le_natDegree_succ_mul_h _ _ fun a ↦ by
        rw [rothLastSlice_coeff_h]
        exact rothMvL1_coeff_le_h P (rothLastIndex i a)
    _ ≤ (r (Fin.last n) + 1) * rothMvL1 P := by
      gcongr
      exact rothLastSlice_natDegree_le_h hP i

lemma roth_exists_integral_factor_data_h {n : ℕ}
    {P : MvPolynomial (Fin (n + 1)) ℤ} {r : Fin (n + 1) → ℕ}
    (d : RothDeterminantData P r) :
    Nonempty (RothIntegralFactorData d) := by
  classical
  obtain ⟨i, hi⟩ := MvPolynomial.support_nonempty.mpr d.V_ne
  have hcoeff : d.V.coeff i ≠ 0 := MvPolynomial.mem_support_iff.mp hi
  let WZ := rothLastSlice d.U i
  have hmapW : Polynomial.map (algebraMap ℤ ℚ) WZ =
      Polynomial.C (d.V.coeff i : ℚ) * d.W := by
    exact rothLastSlice_map_eq_C_mul_of_factorization_h d.U d.V d.W i d.factorization
  have hcoeffQ : (d.V.coeff i : ℚ) ≠ 0 := by exact_mod_cast hcoeff
  have hWZne : WZ ≠ 0 := by
    intro hzero
    have hright : Polynomial.C (d.V.coeff i : ℚ) * d.W = 0 := by
      rw [← hmapW, hzero, Polynomial.map_zero]
    exact (mul_ne_zero (Polynomial.C_ne_zero.mpr hcoeffQ) d.W_ne) hright
  have hWZdegree : WZ.natDegree ≤ d.k * r (Fin.last n) := by
    exact rothLastSlice_natDegree_le_h d.U_degree i
  have hWZl1 : rothPolyL1 WZ ≤
      (d.k * r (Fin.last n) + 1) *
        (d.k.factorial * (2 ^ (∑ h, r h) * rothMvL1 P) ^ d.k) := by
    exact (rothPolyL1_lastSlice_le_h d.U_degree i).trans
      (Nat.mul_le_mul_left _ d.U_l1)
  have hscaled :
      rothLastEquiv ℚ n
          ((d.V.coeff i : ℚ) • MvPolynomial.map (algebraMap ℤ ℚ) d.U) =
        Polynomial.C (MvPolynomial.map (algebraMap ℤ ℚ) d.V) *
          Polynomial.map MvPolynomial.C
            (Polynomial.map (algebraMap ℤ ℚ) WZ) := by
    rw [map_smul, d.factorization, hmapW, Polynomial.map_mul,
      Polynomial.map_C]
    simp only [Algebra.smul_def]
    rw [show algebraMap ℚ (Polynomial (MvPolynomial (Fin n) ℚ))
      (d.V.coeff i : ℚ) = Polynomial.C (MvPolynomial.C (d.V.coeff i : ℚ)) by simp]
    ring
  exact ⟨{
    coeffIndex := i
    coeff_ne := hcoeff
    WZ := WZ
    WZ_ne := hWZne
    WZ_degree := hWZdegree
    WZ_l1 := hWZl1
    scaled_factorization := hscaled
  }⟩

lemma rothBoxIndex_apply_h {m : ℕ} {r : Fin m → ℕ} (j : RothBox r) (h : Fin m) :
    rothBoxIndex j h = j h := by
  simp [rothBoxIndex]

lemma rothBoxIndex_injective_h {m : ℕ} {r : Fin m → ℕ} :
    Function.Injective (rothBoxIndex : RothBox r → RothMvIndex m) := by
  intro i j hij
  funext h
  apply Fin.ext
  simpa only [rothBoxIndex_apply_h] using congrArg (fun k : RothMvIndex m ↦ k h) hij

lemma rothMvOfCoeff_coeff_h {m : ℕ} {r : Fin m → ℕ} (c : RothCoeff r)
    (j : RothBox r) :
    (rothMvOfCoeff c).coeff (rothBoxIndex j) = c j := by
  classical
  simp only [rothMvOfCoeff, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    simp only [ite_eq_right_iff]
    intro hidx
    exact (hkj (rothBoxIndex_injective_h hidx)).elim
  · simp

lemma rothMvOfCoeff_ne_zero_h {m : ℕ} {r : Fin m → ℕ} {c : RothCoeff r}
    (hc : c ≠ 0) : rothMvOfCoeff c ≠ 0 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hc
  intro hzero
  have := congrArg (fun P : MvPolynomial (Fin m) ℤ ↦ P.coeff (rothBoxIndex j)) hzero
  rw [rothMvOfCoeff_coeff_h, AddMonoidAlgebra.coeff_zero] at this
  exact hj this

lemma rothMvOfCoeff_degreeBound_h {m : ℕ} {r : Fin m → ℕ} (c : RothCoeff r) :
    rothDegreeBound (rothMvOfCoeff c) r := by
  classical
  intro i hi h
  by_contra hnot
  have hgt : r h < i h := Nat.lt_of_not_ge hnot
  have hcoeff : (rothMvOfCoeff c).coeff i ≠ 0 := MvPolynomial.mem_support_iff.mp hi
  apply hcoeff
  simp only [rothMvOfCoeff, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  apply Finset.sum_eq_zero
  intro j _
  have hne : rothBoxIndex j ≠ i := by
    intro heq
    have := congrArg (fun k : RothMvIndex m ↦ k h) heq
    simp only [rothBoxIndex_apply_h] at this
    have hjle : (j h : ℕ) ≤ r h := Nat.le_of_lt_succ (j h).isLt
    omega
  simp [hne]

lemma rothMvL1_ofCoeff_le_h {m : ℕ} {r : Fin m → ℕ} (c : RothCoeff r) :
    rothMvL1 (rothMvOfCoeff c) ≤ ∑ j, (c j).natAbs := by
  classical
  unfold rothMvOfCoeff
  calc
    _ ≤
        ∑ j ∈ Finset.univ,
          rothMvL1 (MvPolynomial.monomial (rothBoxIndex j) (c j)) :=
      rothMvL1_finset_sum_h Finset.univ _
    _ = ∑ j, (c j).natAbs := by simp [rothMvL1_monomial_h]

lemma rothFlip_apply_same_h {m : ℕ} (r : Fin m → ℕ) (h : Fin m)
    (j : RothBox r) :
    ((rothFlip r h j) h : ℕ) = r h - j h := by
  simp [rothFlip]

lemma rothFlip_apply_ne_h {m : ℕ} (r : Fin m → ℕ) {h k : Fin m}
    (hhk : k ≠ h) (j : RothBox r) :
    rothFlip r h j k = j k := by
  simp [rothFlip, hhk]

lemma rothCentered_flip_same_h {m : ℕ} {r : Fin m → ℕ}
    (hr : ∀ h, 0 < r h) (h : Fin m) (j : RothBox r) :
    rothCentered r (rothFlip r h j) h = -rothCentered r j h := by
  unfold rothCentered
  rw [rothFlip_apply_same_h]
  have hjle : (j h : ℕ) ≤ r h := Nat.le_of_lt_succ (j h).isLt
  rw [Nat.cast_sub hjle]
  have hrR : (0 : ℝ) < r h := by exact_mod_cast hr h
  field_simp
  ring

lemma rothCentered_flip_ne_h {m : ℕ} {r : Fin m → ℕ}
    {h k : Fin m} (hhk : k ≠ h) (j : RothBox r) :
    rothCentered r (rothFlip r h j) k = rothCentered r j k := by
  simp only [rothCentered, rothFlip_apply_ne_h r hhk]

lemma rothCentered_sq_le_h {m : ℕ} {r : Fin m → ℕ}
    (hr : ∀ h, 0 < r h) (j : RothBox r) (h : Fin m) :
    rothCentered r j h ^ 2 ≤ (1 : ℝ) / 4 := by
  have hjle : (j h : ℕ) ≤ r h := Nat.le_of_lt_succ (j h).isLt
  have hrR : (0 : ℝ) < r h := by exact_mod_cast hr h
  have hx0 : (0 : ℝ) ≤ (j h : ℝ) / r h := by positivity
  have hx1 : (j h : ℝ) / r h ≤ 1 := by
    exact (div_le_one hrR).2 (by exact_mod_cast hjle)
  have hleft : 0 ≤ rothCentered r j h + 1 / 2 := by
    unfold rothCentered
    linarith
  have hright : 0 ≤ 1 / 2 - rothCentered r j h := by
    unfold rothCentered
    linarith
  have hprod := mul_nonneg hleft hright
  nlinarith

lemma rothCentered_cross_sum_h {m : ℕ} {r : Fin m → ℕ}
    (hr : ∀ h, 0 < r h) {h k : Fin m} (hhk : h ≠ k) :
    ∑ j : RothBox r, rothCentered r j h * rothCentered r j k = 0 := by
  have hreindex := Equiv.sum_comp (rothFlipEquiv r h)
    (fun j : RothBox r ↦ rothCentered r j h * rothCentered r j k)
  have hkh : k ≠ h := Ne.symm hhk
  have hneg :
      (∑ j : RothBox r,
          rothCentered r (rothFlip r h j) h * rothCentered r (rothFlip r h j) k) =
        -(∑ j : RothBox r, rothCentered r j h * rothCentered r j k) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [rothCentered_flip_same_h hr, rothCentered_flip_ne_h hkh]
    ring
  change
    (∑ j : RothBox r,
        rothCentered r (rothFlip r h j) h * rothCentered r (rothFlip r h j) k) =
      ∑ j : RothBox r, rothCentered r j h * rothCentered r j k at hreindex
  rw [hneg] at hreindex
  linarith

lemma rothCentered_sq_sum_le_h {m : ℕ} {r : Fin m → ℕ}
    (hr : ∀ h, 0 < r h) (h : Fin m) :
    ∑ j : RothBox r, rothCentered r j h ^ 2 ≤
      (Fintype.card (RothBox r) : ℝ) / 4 := calc
    _ ≤
        ∑ _j : RothBox r, (1 : ℝ) / 4 := by
      gcongr with j
      exact rothCentered_sq_le_h hr j h
    _ = (Fintype.card (RothBox r) : ℝ) / 4 := by
      simp [div_eq_mul_inv]

lemma rothCentered_second_moment_le_h {m : ℕ} {r : Fin m → ℕ}
    (hr : ∀ h, 0 < r h) :
    ∑ j : RothBox r, rothCenteredSum r j ^ 2 ≤
      (m : ℝ) * Fintype.card (RothBox r) / 4 := by
  have hexpand :
      (∑ j : RothBox r, rothCenteredSum r j ^ 2) =
        ∑ h : Fin m, ∑ k : Fin m, ∑ j : RothBox r,
          rothCentered r j h * rothCentered r j k := calc
      _ =
          ∑ j : RothBox r, ∑ h : Fin m, ∑ k : Fin m,
            rothCentered r j h * rothCentered r j k := by
        apply Finset.sum_congr rfl
        intro j _
        unfold rothCenteredSum
        rw [pow_two, Finset.sum_mul_sum]
      _ = ∑ h : Fin m, ∑ j : RothBox r, ∑ k : Fin m,
            rothCentered r j h * rothCentered r j k := Finset.sum_comm
      _ = ∑ h : Fin m, ∑ k : Fin m, ∑ j : RothBox r,
            rothCentered r j h * rothCentered r j k := by
        apply Finset.sum_congr rfl
        intro h _
        exact Finset.sum_comm
  rw [hexpand]
  calc
    (∑ h : Fin m, ∑ k : Fin m, ∑ j : RothBox r,
        rothCentered r j h * rothCentered r j k) ≤
        ∑ h : Fin m, ∑ k : Fin m,
          if h = k then (Fintype.card (RothBox r) : ℝ) / 4 else 0 := by
      gcongr with h k
      by_cases hhk : h = k
      · subst k
        simpa [pow_two] using rothCentered_sq_sum_le_h hr h
      · simp only [hhk, ↓reduceIte]
        rw [rothCentered_cross_sum_h hr hhk]
    _ = (m : ℝ) * Fintype.card (RothBox r) / 4 := by
      simp
      ring

lemma rothWeight_eq_centeredSum_add_h {m : ℕ} (r : Fin m → ℕ)
    (j : RothBox r) :
    rothWeight r (fun h ↦ j h) = rothCenteredSum r j + (m : ℝ) / 2 := by
  unfold rothWeight rothCenteredSum rothCentered
  rw [Finset.sum_sub_distrib]
  simp
  ring

lemma roth_low_indices_card_bound_h {m : ℕ} {r : Fin m → ℕ}
    (hr : ∀ h, 0 < r h) (hm : 0 < m) {γ : ℝ} (hγ : 0 < γ) :
    (4 : ℝ) * m * γ ^ 2 * (rothLowIndices r γ).card ≤
      Fintype.card (RothBox r) := by
  let L := rothLowIndices r γ
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hpoint : ∀ j ∈ L,
      ((m : ℝ) * γ) ^ 2 ≤ rothCenteredSum r j ^ 2 := by
    intro j hj
    have hjlow := (Finset.mem_filter.mp hj).2
    rw [rothWeight_eq_centeredSum_add_h] at hjlow
    have hs : rothCenteredSum r j < -((m : ℝ) * γ) := by linarith
    have hmg : 0 < (m : ℝ) * γ := mul_pos hmR hγ
    nlinarith
  have hlow :
      (L.card : ℝ) * ((m : ℝ) * γ) ^ 2 ≤
        ∑ j ∈ L, rothCenteredSum r j ^ 2 := calc
      _ =
          ∑ _j ∈ L, ((m : ℝ) * γ) ^ 2 := by simp
      _ ≤ ∑ j ∈ L, rothCenteredSum r j ^ 2 := by
        exact Finset.sum_le_sum fun j hj ↦ hpoint j hj
  have hsubset :
      (∑ j ∈ L, rothCenteredSum r j ^ 2) ≤
        ∑ j : RothBox r, rothCenteredSum r j ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.filter_subset _ _
    · intro j _ _hjL
      positivity
  have hmain :
      (L.card : ℝ) * ((m : ℝ) * γ) ^ 2 ≤
        (m : ℝ) * Fintype.card (RothBox r) / 4 :=
    hlow.trans (hsubset.trans (rothCentered_second_moment_le_h hr))
  have hmul :
      (m : ℝ) * ((4 : ℝ) * m * γ ^ 2 * L.card) ≤
        (m : ℝ) * Fintype.card (RothBox r) := calc
      _ =
          4 * ((L.card : ℝ) * ((m : ℝ) * γ) ^ 2) := by ring
      _ ≤ 4 * ((m : ℝ) * Fintype.card (RothBox r) / 4) := by
        gcongr
      _ = (m : ℝ) * Fintype.card (RothBox r) := by ring
  exact (mul_le_mul_iff_of_pos_left hmR).mp hmul

lemma roth_low_equation_card_lt_h {m d : ℕ} {r : Fin m → ℕ}
    (hr : ∀ h, 0 < r h) (hm : 0 < m) {γ : ℝ} (hγ : 0 < γ)
    (hparam : (d : ℝ) < 4 * m * γ ^ 2) :
    Fintype.card (RothLowIndex r γ × Fin d) < Fintype.card (RothBox r) := by
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe]
  by_cases hL : (rothLowIndices r γ).card = 0
  · simp only [hL, zero_mul]
    exact Fintype.card_pos_iff.mpr
      ⟨fun h ↦ ⟨0, Nat.succ_pos (r h)⟩⟩
  · have hLpos : (0 : ℝ) < (rothLowIndices r γ).card := by
      exact_mod_cast Nat.pos_of_ne_zero hL
    have hstrict :
        (d : ℝ) * (rothLowIndices r γ).card <
          (4 * m * γ ^ 2) * (rothLowIndices r γ).card :=
      mul_lt_mul_of_pos_right hparam hLpos
    have hbound := roth_low_indices_card_bound_h hr hm hγ
    have hreal :
        ((d * (rothLowIndices r γ).card : ℕ) : ℝ) <
          Fintype.card (RothBox r) := by
      norm_num only [Nat.cast_mul]
      exact hstrict.trans_le hbound
    have hnat : d * (rothLowIndices r γ).card < Fintype.card (RothBox r) := by
      exact_mod_cast hreal
    simpa [mul_comm] using hnat

lemma rothZeroBox_mem_low_h {m : ℕ} (r : Fin m → ℕ) (hm : 0 < m)
    {γ : ℝ} (hγ : γ < 1 / 2) :
    rothZeroBox r ∈ rothLowIndices r γ := by
  simp only [rothLowIndices, Finset.mem_filter, Finset.mem_univ, true_and]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hprod : (0 : ℝ) < m * (1 / 2 - γ) := mul_pos hmR (sub_pos.mpr hγ)
  simpa [rothWeight, rothZeroBox] using hprod

lemma roth_low_equation_card_pos_h {m d : ℕ} {r : Fin m → ℕ}
    (hm : 0 < m) (hd : 0 < d) {γ : ℝ} (hγ : γ < 1 / 2) :
    0 < Fintype.card (RothLowIndex r γ × Fin d) := by
  exact Fintype.card_pos_iff.mpr
    ⟨(⟨rothZeroBox r, rothZeroBox_mem_low_h r hm hγ⟩, ⟨0, hd⟩)⟩

lemma roth_low_equation_twice_card_le_h {m d : ℕ} {r : Fin m → ℕ}
    (hr : ∀ h, 0 < r h) (hm : 0 < m) {γ : ℝ} (hγ : 0 < γ)
    (hparam : (d : ℝ) ≤ 2 * m * γ ^ 2) :
    2 * Fintype.card (RothLowIndex r γ × Fin d) ≤ Fintype.card (RothBox r) := by
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe]
  have hbound := roth_low_indices_card_bound_h hr hm hγ
  have hreal :
      ((2 * ((rothLowIndices r γ).card * d) : ℕ) : ℝ) ≤
        Fintype.card (RothBox r) := by
    norm_num only [Nat.cast_mul, Nat.cast_ofNat]
    calc
      (2 : ℝ) * ((rothLowIndices r γ).card * d) =
          (2 * d) * (rothLowIndices r γ).card := by ring
      _ ≤ (4 * m * γ ^ 2) * (rothLowIndices r γ).card := by
        have hcoef : (2 : ℝ) * d ≤ 4 * m * γ ^ 2 := by linarith
        exact mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ ≤ Fintype.card (RothBox r) := hbound
  exact_mod_cast hreal

lemma roth_box_card_h {m : ℕ} (r : Fin m → ℕ) :
    Fintype.card (RothBox r) = ∏ h, (r h + 1) := by
  simp [RothBox, Fintype.card_pi]

lemma rothMvHasse_eval_ofCoeff_index_h {m : ℕ} {R : Type*} [CommRing R]
    {r : Fin m → ℕ} (c : RothCoeff r) (i : RothMvIndex m) (x : Fin m → R) :
    MvPolynomial.eval₂ (algebraMap ℤ R) x (rothMvHasse i (rothMvOfCoeff c)) =
      rothHasseEval c (fun h ↦ i h) x := by
  classical
  rw [rothMvOfCoeff, rothMvHasse_finset_sum_h Finset.univ]
  rw [MvPolynomial.eval₂_sum]
  unfold rothHasseEval
  apply Finset.sum_congr rfl
  intro j _
  rw [rothMvHasse_monomial_h, MvPolynomial.eval₂_monomial]
  rw [Finsupp.prod_fintype]
  · change
      (algebraMap ℤ R) ((∏ h, (Nat.choose (j h) (i h) : ℤ)) * c j) *
          ∏ h, x h ^ ((j h : ℕ) - i h) = _
    rw [map_mul, map_prod]
    rw [algebraMap_int_eq, Int.coe_castRingHom]
    dsimp only
    simp only [Int.cast_natCast]
    rw [Finset.prod_mul_distrib]
    ac_rfl
  · intro h
    simp

lemma rothVanishesBelow_to_mv_h {m : ℕ} {r : Fin m → ℕ}
    {c : RothCoeff r} {x : Fin m → ℝ} {T : ℝ}
    (hvan : rothVanishesBelow c x T) :
    rothMvVanishesBelow
      (MvPolynomial.map (algebraMap ℤ ℝ) (rothMvOfCoeff c)) x r T := by
  intro i hi
  rw [rothTranslate_coeff_eq_eval_hasse_h, ← rothMvHasse_map_h,
    ← MvPolynomial.eval₂_eq_eval_map, rothMvHasse_eval_ofCoeff_index_h]
  exact hvan (fun h ↦ i h) (by simpa [rothWeight, rothMvWeight] using hi)

lemma roth_den_pow_le_natAbs_leadingCoeff_of_pow_dvd_h
    (P : ℤ[X]) (q : ℚ) (k : ℕ) (hP : P ≠ 0)
    (hdiv : (Polynomial.C (q.den : ℤ) * Polynomial.X - Polynomial.C q.num) ^ k ∣ P) :
    q.den ^ k ≤ P.leadingCoeff.natAbs := by
  let L : ℤ[X] := Polynomial.C (q.den : ℤ) * Polynomial.X - Polynomial.C q.num
  have hL : L.leadingCoeff = (q.den : ℤ) := by
    dsimp [L]
    rw [Polynomial.leadingCoeff_sub_of_degree_lt]
    · exact Polynomial.leadingCoeff_C_mul_X _
    · rw [Polynomial.degree_C_mul_X (by exact_mod_cast q.pos.ne')]
      exact lt_of_le_of_lt Polynomial.degree_C_le (by norm_num)
  have hdvdZ : ((q.den ^ k : ℕ) : ℤ) ∣ P.leadingCoeff := by
    obtain ⟨Q, hQ⟩ := hdiv
    rw [hQ, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_pow, hL]
    norm_cast
    exact dvd_mul_right _ _
  refine Nat.le_of_dvd
    (Int.natAbs_pos.mpr (Polynomial.leadingCoeff_ne_zero.mpr hP)) ?_
  simpa using (Int.natAbs_dvd_natAbs.mpr hdvdZ)

lemma roth_rat_linear_isPrimitive_h (q : ℚ) :
    (Polynomial.C (q.den : ℤ) * Polynomial.X - Polynomial.C q.num).IsPrimitive := by
  rw [Polynomial.isPrimitive_iff_isUnit_of_C_dvd]
  intro a ha
  have hall := (Polynomial.C_dvd_iff_dvd_coeff a _).mp ha
  have hanum : a ∣ q.num := by
    have h := hall 0
    simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C] at h
    norm_num at h
    exact h
  have haden : a ∣ (q.den : ℤ) := by
    have h := hall 1
    simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C] at h
    norm_num at h
    exact h
  have hanum' : a.natAbs ∣ q.num.natAbs := Int.natAbs_dvd_natAbs.mpr hanum
  have haden' : a.natAbs ∣ q.den := by
    simpa using (Int.natAbs_dvd_natAbs.mpr haden)
  apply Int.isUnit_iff_natAbs_eq.mpr
  exact Nat.dvd_one.mp
    ((Nat.dvd_gcd hanum' haden').trans (by rw [q.reduced.gcd_eq_one]))

lemma roth_isPrimitive_pow_h (P : ℤ[X]) (hP : P.IsPrimitive) (k : ℕ) :
    (P ^ k).IsPrimitive := by
  induction k with
  | zero =>
      rw [pow_zero]
      exact Polynomial.isPrimitive_one
  | succ k ih =>
      rw [pow_succ]
      exact ih.mul hP

lemma roth_rat_linear_pow_dvd_of_map_dvd_h (P : ℤ[X]) (q : ℚ) (k : ℕ)
    (hdiv : (Polynomial.X - Polynomial.C q) ^ k ∣
      P.map (Int.castRingHom ℚ)) :
    (Polynomial.C (q.den : ℤ) * Polynomial.X - Polynomial.C q.num) ^ k ∣ P := by
  let L : ℤ[X] := Polynomial.C (q.den : ℤ) * Polynomial.X - Polynomial.C q.num
  let A : ℚ[X] := Polynomial.X - Polynomial.C q
  have hmapL : L.map (Int.castRingHom ℚ) = Polynomial.C (q.den : ℚ) * A := by
    dsimp [L, A]
    rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
      Polynomial.map_C, mul_sub, ← Polynomial.C_mul, Rat.den_mul_eq_num]
    rfl
  have hunit : IsUnit (Polynomial.C (q.den : ℚ)) :=
    Polynomial.isUnit_C.mpr
      (show IsUnit (q.den : ℚ) from (by exact_mod_cast q.pos.ne' : (q.den : ℚ) ≠ 0).isUnit)
  have hassoc : Associated ((L ^ k).map (Int.castRingHom ℚ)) (A ^ k) := by
    rw [Polynomial.map_pow, hmapL, mul_pow]
    exact associated_unit_mul_left _ _ (hunit.pow k)
  apply (Polynomial.IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast
    (L ^ k) P (roth_isPrimitive_pow_h L (roth_rat_linear_isPrimitive_h q) k)).mpr
  rwa [Associated.dvd_iff_dvd_left hassoc]

lemma roth_X_sub_C_pow_dvd_of_hasse_eval_eq_zero_h (P : ℚ[X]) (q : ℚ) (k : ℕ)
    (hzero : ∀ n < k, (Polynomial.hasseDeriv n P).eval q = 0) :
    (Polynomial.X - Polynomial.C q) ^ k ∣ P := by
  rw [Polynomial.X_sub_C_pow_dvd_iff, ← Polynomial.taylor_apply,
    Polynomial.X_pow_dvd_iff]
  intro n hn
  rw [Polynomial.taylor_coeff]
  exact hzero n hn

lemma roth_univariate_index_le_h (P : ℤ[X]) (q : ℚ) (k r : ℕ) (δ : ℝ)
    (hP : P ≠ 0) (hq : 2 ≤ q.den) (hr : 0 < r)
    (hdiv : (Polynomial.C (q.den : ℤ) * Polynomial.X - Polynomial.C q.num) ^ k ∣ P)
    (hheight : (P.leadingCoeff.natAbs : ℝ) ≤
      Real.rpow (q.den : ℝ) (δ * r)) :
    (k : ℝ) / r ≤ δ := by
  have hpowNat := roth_den_pow_le_natAbs_leadingCoeff_of_pow_dvd_h P q k hP hdiv
  have hpow : Real.rpow (q.den : ℝ) k ≤ Real.rpow (q.den : ℝ) (δ * r) := calc
      _ = ((q.den ^ k : ℕ) : ℝ) := by
        rw [Real.rpow_eq_pow, Real.rpow_natCast]
        norm_cast
      _ ≤ (P.leadingCoeff.natAbs : ℝ) := by exact_mod_cast hpowNat
      _ ≤ Real.rpow (q.den : ℝ) (δ * r) := hheight
  have hk : (k : ℝ) ≤ δ * r :=
    (Real.strictMono_rpow_of_base_gt_one (by exact_mod_cast hq)).le_iff_le.mp hpow
  exact (div_le_iff₀ (by exact_mod_cast hr : (0 : ℝ) < r)).2 (by simpa [mul_comm] using hk)

lemma roth_triangular_sum_lower_h {θ δ : ℝ} {r k : ℕ}
    (hθ : 0 < θ) (hθone : θ ≤ 1) (hδ : δ ≤ θ / 4)
    (hr : 0 < r) (hrlarge : 16 ≤ θ * r)
    (hk : 0 < k) (hkr : k ≤ r + 1) :
    θ ^ 2 / 64 ≤
      (∑ t : Fin k, max 0 (θ - δ - (t : ℝ) / r)) / k := by
  let N : ℕ := ⌊θ * r / 8⌋₊
  have hxnonneg : 0 ≤ θ * (r : ℝ) / 8 := by positivity
  have hxlarge : 2 ≤ θ * (r : ℝ) / 8 := by linarith
  have hNle : (N : ℝ) ≤ θ * r / 8 := by
    exact Nat.floor_le hxnonneg
  have hxlt : θ * r / 8 < (N : ℝ) + 1 := Nat.lt_floor_add_one _
  have hNlower : θ * (r : ℝ) / 16 ≤ N := by linarith
  have hNpos : 0 < N := by
    have : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hNlower
    exact_mod_cast this
  have hterm : ∀ t : Fin k, t.val < N →
      θ / 2 ≤ max 0 (θ - δ - (t : ℝ) / r) := by
    intro t ht
    have htN : (t.val : ℝ) < N := by exact_mod_cast ht
    have htx : (t.val : ℝ) < θ * r / 8 := htN.trans_le hNle
    have htdiv : (t.val : ℝ) / r < θ / 8 := by
      apply (div_lt_iff₀ (by exact_mod_cast hr : (0 : ℝ) < r)).2
      nlinarith
    exact (by linarith : θ / 2 ≤ θ - δ - (t : ℝ) / r).trans
      (le_max_right _ _)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  apply (le_div_iff₀ hkR).2
  by_cases hkN : k ≤ N
  · have hsum : (k : ℝ) * (θ / 2) ≤
        ∑ t : Fin k, max 0 (θ - δ - (t : ℝ) / r) := calc
        _ = ∑ _t : Fin k, θ / 2 := by simp
        _ ≤ ∑ t : Fin k, max 0 (θ - δ - (t : ℝ) / r) := by
          gcongr with t
          exact hterm t (lt_of_lt_of_le t.isLt hkN)
    calc
      _ ≤ (k : ℝ) * (θ / 2) := by
        have : θ ^ 2 / 64 ≤ θ / 2 := by nlinarith [sq_nonneg θ]
        nlinarith
      _ ≤ _ := hsum
  · have hNk : N ≤ k := (Nat.le_of_lt (lt_of_not_ge hkN))
    let S : Finset (Fin k) := Finset.univ.filter fun t ↦ t.val < N
    have hcardS : S.card = N := by
      rw [← Fintype.card_coe]
      let e : S ≃ Fin N :=
        { toFun := fun t ↦ ⟨t.val.val, by
              have := t.property
              change t.val ∈ Finset.univ.filter (fun u : Fin k ↦ u.val < N) at this
              exact (Finset.mem_filter.mp this).2⟩
          invFun := fun t ↦ ⟨⟨t.val, t.isLt.trans_le hNk⟩, by
              simp [S]⟩
          left_inv := by intro t; ext; rfl
          right_inv := by intro t; ext; rfl }
      exact (Fintype.card_congr e).trans (Fintype.card_fin N)
    have hsumS : (N : ℝ) * (θ / 2) ≤
        ∑ t ∈ S, max 0 (θ - δ - (t : ℝ) / r) := calc
        _ = ∑ _t ∈ S, θ / 2 := by simp [hcardS]
        _ ≤ ∑ t ∈ S, max 0 (θ - δ - (t : ℝ) / r) := by
          gcongr with t ht
          exact hterm t (by simpa [S] using ht)
    have hsumAll : (N : ℝ) * (θ / 2) ≤
        ∑ t : Fin k, max 0 (θ - δ - (t : ℝ) / r) := by
      exact hsumS.trans (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun _ _ _ ↦ le_max_left _ _))
    have hkrR : (k : ℝ) ≤ 2 * r := by
      exact_mod_cast (hkr.trans (by omega : r + 1 ≤ 2 * r))
    calc
      _ ≤ θ ^ 2 * r / 32 := by
        nlinarith [sq_nonneg θ]
      _ ≤ (N : ℝ) * (θ / 2) := by
        nlinarith
      _ ≤ _ := hsumAll

lemma rothIntPolynomial_ne_zero_h {α : ℝ} (hα : IsAlgebraic ℚ α) :
    rothIntPolynomial α ≠ 0 := by
  obtain ⟨b, hb, hspec⟩ :=
    IsLocalization.integerNormalization_spec ℤ⁰ (minpoly ℚ α)
  intro hf
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hbQ : algebraMap ℤ ℚ b ≠ 0 := Int.cast_ne_zero.mpr hb0
  have hsmul : b • minpoly ℚ α ≠ 0 := by
    rw [Algebra.smul_def]
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr hbQ) (minpoly.ne_zero hα.isIntegral)

  apply hsmul
  change IsLocalization.integerNormalization ℤ⁰ (minpoly ℚ α) = 0 at hf
  rw [← hspec, hf, Polynomial.map_zero]

lemma rothIntPolynomial_isRoot_h (α : ℝ) :
    Polynomial.eval α ((rothIntPolynomial α).map (algebraMap ℤ ℝ)) = 0 := by
  obtain ⟨b, _hb, hspec⟩ :=
    IsLocalization.integerNormalization_spec ℤ⁰ (minpoly ℚ α)
  change Polynomial.eval α
    ((IsLocalization.integerNormalization ℤ⁰ (minpoly ℚ α)).map
      (algebraMap ℤ ℝ)) = 0
  have hmap : algebraMap ℤ ℝ = (algebraMap ℚ ℝ).comp (algebraMap ℤ ℚ) := by
    ext
    simp
  have hmapsmul :
      Polynomial.map (algebraMap ℚ ℝ) (b • minpoly ℚ α) =
        b • Polynomial.map (algebraMap ℚ ℝ) (minpoly ℚ α) :=
    map_zsmul (Polynomial.mapRingHom (algebraMap ℚ ℝ)) b (minpoly ℚ α)
  have hroot : Polynomial.eval₂ (algebraMap ℚ ℝ) α (minpoly ℚ α) = 0 := by
    rw [← Polynomial.aeval_def]
    exact minpoly.aeval ℚ α

  rw [hmap, ← Polynomial.map_map, hspec, hmapsmul, Polynomial.eval_smul]
  simp [Polynomial.eval_map, hroot]

lemma rothIntPolynomial_natDegree_pos_h {α : ℝ} (hα : IsAlgebraic ℚ α) :
    0 < (rothIntPolynomial α).natDegree := by
  let f := rothIntPolynomial α
  have hf : f ≠ 0 := rothIntPolynomial_ne_zero_h hα
  by_contra hnot
  have hd : f.natDegree = 0 := Nat.eq_zero_of_not_pos hnot
  have hfC : f = Polynomial.C (f.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hd
  have hr := rothIntPolynomial_isRoot_h α
  change Polynomial.eval α (f.map (algebraMap ℤ ℝ)) = 0 at hr
  rw [hfC, Polynomial.map_C, Polynomial.eval_C] at hr
  have hc : f.coeff 0 = 0 := Int.cast_eq_zero.mp hr
  apply hf
  rw [hfC, hc, Polynomial.C_0]

lemma rothIntegralPolynomial_natDegree_pos_h {α : ℝ} (hα : IsAlgebraic ℚ α) :
    0 < (rothIntegralPolynomial α).natDegree := by
  simpa [rothIntegralPolynomial] using rothIntPolynomial_natDegree_pos_h hα

lemma roth_succ_le_two_pow_h {n : ℕ} (hn : 0 < n) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hn0 : n = 0
      · subst n
        norm_num
      · calc
          _ ≤ 2 * (n + 1) := by omega
          _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 (ih (Nat.pos_of_ne_zero hn0))
          _ = 2 ^ (n + 1) := by rw [pow_succ]; ring

lemma roth_box_card_le_two_pow_sum_h {m : ℕ} {r : Fin m → ℕ}
    (hr : ∀ h, 0 < r h) :
    Fintype.card (RothBox r) ≤ 2 ^ (∑ h, r h) := by
  rw [roth_box_card_h]
  calc
    _ ≤ ∏ h, 2 ^ r h := by
      gcongr with h
      exact roth_succ_le_two_pow_h (hr h)
    _ = 2 ^ (∑ h, r h) := Finset.prod_pow_eq_pow_sum Finset.univ r 2

lemma roth_ridout_exists_auxiliary_coeff_h
    (α : ℝ) (hα : IsAlgebraic ℚ α) {m : ℕ} {r : Fin m → ℕ}
    (hr : ∀ h, 0 < r h) (hm : 0 < m) {γ : ℝ} (hγ0 : 0 < γ) (hγhalf : γ < 1 / 2)
    (hparamStrict : (((rothIntegralPolynomial α).natDegree + 2 : ℕ) : ℝ) <
      4 * m * γ ^ 2)
    (hparamHalf : (((rothIntegralPolynomial α).natDegree + 2 : ℕ) : ℝ) ≤
      2 * m * γ ^ 2) :
    ∃ c : RothCoeff r, c ≠ 0 ∧
      rothVanishesBelow c (fun _h ↦ α) ((m : ℝ) * (1 / 2 - γ)) ∧
      (∀ j, c j ≠ 0 →
        (m : ℝ) * (1 / 2 - γ) ≤ rothWeight r (fun h ↦ j h) ∧
          rothWeight r (fun h ↦ j h) ≤
            (m : ℝ) - (m : ℝ) * (1 / 2 - γ)) ∧
      rothMvL1 (rothMvOfCoeff c) ≤
        (8 * rothCoordinateBase α) ^ (∑ h, r h) := by
  let d := (rothIntegralPolynomial α).natDegree + 2
  let A := rothRidoutAuxMatrix α r γ
  let M := Fintype.card (RothLowIndex r γ × Fin d)
  let N := Fintype.card (RothBox r)
  let S := ∑ h, r h
  let H := (2 * rothCoordinateBase α) ^ S
  have hd : 0 < d := by dsimp [d]; omega
  have hcard : M < N := by
    exact roth_low_equation_card_lt_h hr hm hγ0 hparamStrict
  have hMpos : 0 < M := roth_low_equation_card_pos_h hm hd hγhalf
  have htwice : 2 * M ≤ N := by
    exact roth_low_equation_twice_card_le_h hr hm hγ0 hparamHalf
  obtain ⟨c, hc, hker, hcnorm⟩ :=
    Int.Matrix.exists_ne_zero_int_vec_norm_le A hcard hMpos
  have hcardR : (M : ℝ) < N := by exact_mod_cast hcard
  have htwiceR : (2 : ℝ) * M ≤ N := by exact_mod_cast htwice
  have hden : 0 < (N : ℝ) - M := sub_pos.mpr hcardR
  have hexp : (M : ℝ) / ((N : ℝ) - M) ≤ 1 := by
    apply (div_le_one hden).2
    linarith
  have hNpos : 0 < N := lt_of_le_of_lt (Nat.zero_le _) hcard
  have hbase : (1 : ℝ) ≤ (N : ℝ) * max 1 ‖A‖ := by
    exact one_le_mul_of_one_le_of_one_le (by exact_mod_cast hNpos)
      (le_max_left _ _)
  have hrpow :
      ((N : ℝ) * max 1 ‖A‖) ^ ((M : ℝ) / ((N : ℝ) - M)) ≤
        (N : ℝ) * max 1 ‖A‖ := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hbase hexp
  have hHnat : 1 ≤ H := by
    apply one_le_pow₀
    have hB := RothCoordinateBase.Gt_0 α
    omega
  have hH : (1 : ℝ) ≤ H := by exact_mod_cast hHnat
  have hAnorm : ‖A‖ ≤ (H : ℝ) := by
    exact NormRothRidoutAuxMatrix.le.PowMul_2RothCoordinateBaseSum α r γ
  have hmax : max 1 ‖A‖ ≤ (H : ℝ) := max_le hH hAnorm
  have hcnormSimple : ‖c‖ ≤ (N : ℝ) * H := calc
      _ ≤ ((N : ℝ) * max 1 ‖A‖) ^ ((M : ℝ) / ((N : ℝ) - M)) := hcnorm
      _ ≤ (N : ℝ) * max 1 ‖A‖ := hrpow
      _ ≤ (N : ℝ) * H := by gcongr
  have hsumNorm := Pi.sum_norm_apply_le_norm c
  have hsum : ((∑ j, (c j).natAbs : ℕ) : ℝ) ≤ (N : ℝ) * ‖c‖ := calc
      _ = ∑ j, ((c j).natAbs : ℝ) := by
        norm_cast
      _ = ∑ j, ‖c j‖ := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Int.norm_eq_abs, ← Int.cast_abs, ← Int.natCast_natAbs]
        norm_num
      _ ≤ (N : ℝ) * ‖c‖ := by
        simpa [N, nsmul_eq_mul] using hsumNorm
  have hN : N ≤ 2 ^ S := roth_box_card_le_two_pow_sum_h hr
  have hl1Nat := rothMvL1_ofCoeff_le_h c
  have hl1 : (rothMvL1 (rothMvOfCoeff c) : ℝ) ≤
      (((8 * rothCoordinateBase α) ^ S : ℕ) : ℝ) := calc
      _ ≤ ((∑ j, (c j).natAbs : ℕ) : ℝ) := by
        exact_mod_cast hl1Nat
      _ ≤ (N : ℝ) * ‖c‖ := hsum
      _ ≤ (N : ℝ) * ((N : ℝ) * H) := by gcongr
      _ ≤ ((2 ^ S : ℕ) : ℝ) * (((2 ^ S : ℕ) : ℝ) * H) := by gcongr
      _ = (((8 * rothCoordinateBase α) ^ S : ℕ) : ℝ) := by
        norm_cast
        dsimp [H]
        rw [← mul_pow, ← mul_pow]
        congr 1
        ring
  have hkerOld := MulVecRothAuxMatrix.eq.Zero.of.EqMulVecRothRidoutAuxMatrix_0.RothCoeff hker
  refine ⟨c, hc, ?_, ?_, by exact_mod_cast hl1⟩
  · intro i hi
    by_cases hir : ∀ h, i h ≤ r h
    · let ib : RothBox r := fun h ↦ ⟨i h, Nat.lt_succ_iff.mpr (hir h)⟩
      have hibLow : ib ∈ rothLowIndices r γ := by
        simp only [rothLowIndices, Finset.mem_filter, Finset.mem_univ, true_and]
        simpa [ib] using hi
      exact RothHasseEval_1.eq.Zero.of.EqMulVecRothAuxMatrix_0.RothCoeff.IsAlgebraic (i := ⟨ib, hibLow⟩) hα hkerOld
    · push Not at hir
      obtain ⟨h, hh⟩ := hir
      unfold rothHasseEval
      apply Finset.sum_eq_zero
      intro j _
      have hjlt : (j h : ℕ) < i h :=
        lt_of_le_of_lt (Nat.le_of_lt_succ (j h).isLt) hh
      have hz : (Nat.choose (j h) (i h) : ℝ) = 0 := by
        simp [Nat.choose_eq_zero_of_lt hjlt]
      rw [Finset.prod_eq_zero (Finset.mem_univ h)]
      · ring
      · rw [hz]
        simp
  · intro j hj
    exact Mul_SubDiv1'2.le.RothWeightAndRothWeight.le.Sub_Mul_SubDiv1'2.of.Ne_0.RothBox.EqMulVecRothRidoutAuxMatrix_0.All_Gt_0.RothCoeff hr hker hj

lemma roth_factorial_le_two_pow_sq_h {k : ℕ} (hk : 0 < k) :
    k.factorial ≤ 2 ^ (k * k) := by
  have hktwo : k ≤ 2 ^ k :=
    (Nat.le_add_right k 1).trans (roth_succ_le_two_pow_h hk)
  calc
    _ ≤ k ^ k := Nat.factorial_le_pow k
    _ ≤ (2 ^ k) ^ k := by gcongr
    _ = 2 ^ (k * k) := by rw [pow_mul]

lemma roth_determinant_V_l1_coarse_h {n : ℕ}
    {P : MvPolynomial (Fin (n + 1)) ℤ} {r : Fin (n + 1) → ℕ}
    (d : RothDeterminantData P r) :
    rothMvL1 d.V ≤
      2 ^ (d.k * d.k + d.k * (∑ h : Fin n, r h.castSucc)) *
        rothMvL1 P ^ d.k := calc
    _ ≤
        d.k.factorial *
          (2 ^ (∑ h : Fin n, r h.castSucc) * rothMvL1 P) ^ d.k := d.V_l1
    _ ≤ 2 ^ (d.k * d.k) *
          (2 ^ (∑ h : Fin n, r h.castSucc) * rothMvL1 P) ^ d.k := by
      gcongr
      exact roth_factorial_le_two_pow_sq_h d.k_pos
    _ = 2 ^ (d.k * d.k + d.k * (∑ h : Fin n, r h.castSucc)) *
          rothMvL1 P ^ d.k := by
      rw [mul_pow, ← pow_mul]
      rw [show 2 ^ (d.k * d.k) *
          (2 ^ ((∑ h : Fin n, r h.castSucc) * d.k) * rothMvL1 P ^ d.k) =
          (2 ^ (d.k * d.k) *
            2 ^ ((∑ h : Fin n, r h.castSucc) * d.k)) * rothMvL1 P ^ d.k by ring,
        ← pow_add]
      congr 2
      ring

lemma roth_determinant_W_l1_coarse_h {n : ℕ}
    {P : MvPolynomial (Fin (n + 1)) ℤ} {r : Fin (n + 1) → ℕ}
    (d : RothDeterminantData P r) (e : RothIntegralFactorData d)
    (hrlast : 0 < r (Fin.last n)) :
    rothPolyL1 e.WZ ≤
      2 ^ (d.k * r (Fin.last n) + d.k * d.k + d.k * (∑ h, r h)) *
        rothMvL1 P ^ d.k := by
  have hkr : 0 < d.k * r (Fin.last n) := Nat.mul_pos d.k_pos hrlast
  calc
    _ ≤
        (d.k * r (Fin.last n) + 1) *
          (d.k.factorial * (2 ^ (∑ h, r h) * rothMvL1 P) ^ d.k) := e.WZ_l1
    _ ≤ 2 ^ (d.k * r (Fin.last n)) *
          (2 ^ (d.k * d.k) *
            (2 ^ (∑ h, r h) * rothMvL1 P) ^ d.k) := by
      gcongr
      · exact roth_succ_le_two_pow_h hkr
      · exact roth_factorial_le_two_pow_sq_h d.k_pos
    _ = 2 ^ (d.k * r (Fin.last n) + d.k * d.k + d.k * (∑ h, r h)) *
          rothMvL1 P ^ d.k := by
      rw [mul_pow, ← pow_mul]
      rw [show 2 ^ (d.k * r (Fin.last n)) *
          (2 ^ (d.k * d.k) * (2 ^ ((∑ h, r h) * d.k) * rothMvL1 P ^ d.k)) =
          (2 ^ (d.k * r (Fin.last n)) * 2 ^ (d.k * d.k) *
            2 ^ ((∑ h, r h) * d.k)) * rothMvL1 P ^ d.k by ring,
        ← pow_add, ← pow_add]
      congr 2
      ring

lemma roth_univariate_small_hasse_h (θ : ℝ) (hθ : 0 < θ)
    (P : ℤ[X]) (q : ℚ) (r : ℕ) (hr : 0 < r) (hq : 2 ≤ q.den)
    (hPne : P ≠ 0) (hheight : (rothPolyL1 P : ℝ) ≤
      Real.rpow q.den ((θ / 4) * r)) :
    ∃ a : ℕ, (a : ℝ) / r < θ ∧
      (Polynomial.hasseDeriv a (Polynomial.map (algebraMap ℤ ℚ) P)).eval q ≠ 0 := by
  let k : ℕ := ⌈θ * r⌉₊
  by_contra hnot
  push Not at hnot
  have hzero : ∀ a < k,
      (Polynomial.hasseDeriv a (Polynomial.map (algebraMap ℤ ℚ) P)).eval q = 0 := by
    intro a ha
    apply hnot a
    have haθ : (a : ℝ) < θ * r := Nat.lt_ceil.mp ha
    exact (div_lt_iff₀ (by exact_mod_cast hr : (0 : ℝ) < r)).2 (by
      simpa [mul_comm] using haθ)
  have hdivQ := roth_X_sub_C_pow_dvd_of_hasse_eval_eq_zero_h
    (Polynomial.map (algebraMap ℤ ℚ) P) q k hzero
  have hdiv := roth_rat_linear_pow_dvd_of_map_dvd_h P q k hdivQ
  have hlead : (P.leadingCoeff.natAbs : ℝ) ≤
      Real.rpow q.den ((θ / 4) * r) := by
    have hnat : P.leadingCoeff.natAbs ≤ rothPolyL1 P := by
      simpa using rothPolyL1_coeff_le_h P P.natDegree
    have hreal : (P.leadingCoeff.natAbs : ℝ) ≤ rothPolyL1 P := by
      exact_mod_cast hnat
    exact hreal.trans hheight
  have hindex := roth_univariate_index_le_h P q k r (θ / 4)
    hPne hq hr hdiv hlead
  have hceil : θ ≤ (k : ℝ) / r := by
    apply (le_div_iff₀ (by exact_mod_cast hr : (0 : ℝ) < r)).2
    simpa [k, mul_comm] using (Nat.le_ceil (θ * (r : ℝ)))
  linarith

lemma rothMvWeight_le_order_div_h {m b : ℕ}
    (r : Fin m → ℕ) (i : RothMvIndex m) (hb : 0 < b)
    (hbr : ∀ h, b ≤ r h) :
    rothMvWeight r i ≤ (rothMvOrder i : ℝ) / b := by
  unfold rothMvWeight rothMvOrder
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro h _
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hrR : (b : ℝ) ≤ r h := by exact_mod_cast hbr h
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hbR hrR

lemma rothLastSlice_zero_ne_h
    (P : MvPolynomial (Fin 1) ℤ) (hP : P ≠ 0) :
    rothLastSlice P (0 : RothMvIndex 0) ≠ 0 := by
  intro hzero
  apply hP
  ext d
  have htail : rothLastTail d = (0 : RothMvIndex 0) := Subsingleton.elim _ _
  rw [← rothLastIndex_eta_h d, htail, ← rothLastSlice_coeff_h, hzero]
  simp

lemma roth_exists_nonzero_hasse_of_not_vanishesBelow_h
    {m : ℕ} {P : MvPolynomial (Fin m) ℚ} {x : Fin m → ℚ}
    {r : Fin m → ℕ} {T : ℝ}
    (h : ¬rothMvVanishesBelow P x r T) :
    ∃ i : RothMvIndex m, rothMvWeight r i < T ∧
      MvPolynomial.eval x (rothMvHasse i P) ≠ 0 := by
  rw [rothMvVanishesBelow] at h
  push Not at h
  obtain ⟨i, hi, hne⟩ := h
  refine ⟨i, hi, ?_⟩
  simpa [rothTranslate_coeff_eq_eval_hasse_h] using hne

lemma roth_lemma_base_h (θ : ℝ) (hθ : 0 < θ) (hθone : θ ≤ 1) :
    ∃ (δ : ℝ) (Q R : ℕ), 0 < δ ∧ δ ≤ 1 ∧ 2 ≤ Q ∧ 1 ≤ R ∧
      ∀ A : RothLemmaInput 0 δ Q R,
        ¬rothMvVanishesBelow
          (MvPolynomial.map (algebraMap ℤ ℚ) A.P) A.q A.r θ := by
  let δ := θ / 8
  obtain ⟨Q, hQtwo, hQ⟩ := Any_Ge_2AndAll_Le2Rpow.of.Gt_0 (by
    dsimp [δ]
    positivity : 0 < δ)
  refine ⟨δ, Q, 1, by dsimp [δ]; positivity, by dsimp [δ]; linarith,
    hQtwo, le_rfl, fun A hvan ↦ ?_⟩
  have hr : 0 < A.r 0 := lt_of_lt_of_le Nat.zero_lt_one (A.r_large 0)
  have hq : 2 ≤ (A.q 0).den := hQtwo.trans A.den_large
  let Pu := rothLastSlice A.P (0 : RothMvIndex 0)
  have hPu : Pu ≠ 0 := rothLastSlice_zero_ne_h A.P A.P_ne
  have hPul1Nat : rothPolyL1 Pu ≤ 2 ^ A.r 0 * rothMvL1 A.P := by
    calc
      rothPolyL1 Pu ≤ (A.r (Fin.last 0) + 1) * rothMvL1 A.P :=
        rothPolyL1_lastSlice_le_h A.P_degree 0
      _ ≤ 2 ^ A.r 0 * rothMvL1 A.P := by
        gcongr
        simpa using roth_succ_le_two_pow_h hr
  have hPul1 : (rothPolyL1 Pu : ℝ) ≤
      Real.rpow (A.q 0).den ((θ / 4) * A.r 0) := by
    have habsorb := MulPowS.le.RpowMulMulAdd_Mul.of.Le_MulMul.Le_RpowMul.Le_Rpow.Ge_0.Ge (A.q 0).den (rothMvL1 A.P)
      (A.r 0) 1 (A.r 0) 1 δ δ hq (by positivity) (hQ _ A.den_large)
      A.height (by simp)
    have hnat : (rothPolyL1 Pu : ℝ) ≤
        ((2 ^ A.r 0 * rothMvL1 A.P ^ 1 : ℕ) : ℝ) := by
      exact_mod_cast (hPul1Nat.trans_eq (by simp))
    refine hnat.trans ?_
    have hexp : (δ + δ * (1 : ℕ)) * (1 : ℕ) * A.r 0 =
        (θ / 4) * A.r 0 := by
      dsimp [δ]
      push_cast
      ring
    rwa [hexp] at habsorb
  obtain ⟨a, haweight, hane⟩ :=
    roth_univariate_small_hasse_h θ hθ Pu (A.q 0) (A.r 0) hr hq hPu hPul1
  let i := rothLastIndex (0 : RothMvIndex 0) a
  have hiweight : rothMvWeight A.r i < θ := by
    rw [rothMvWeight_lastIndex_h]
    simpa [i, rothMvWeight] using haweight
  have hz := hvan i hiweight
  rw [rothTranslate_coeff_eq_eval_hasse_h] at hz
  have hqfun : A.q = Fin.lastCases (A.q (Fin.last 0)) (fun _ ↦ 0) := by
    funext h
    have hh : h = Fin.last 0 := Fin.ext (by simp)
    subst h
    exact (Fin.lastCases_last (motive := fun _ : Fin 1 ↦ ℚ)
      (last := A.q (Fin.last 0))
      (cast := fun _ : Fin 0 ↦ (0 : ℚ))).symm
  apply hane
  dsimp [Pu]
  have hqzero : A.q 0 = A.q (Fin.last 0) := by
    exact congrArg A.q (Fin.ext (by simp))
  rw [hqzero]
  calc
    ((Polynomial.hasseDeriv a
        (Polynomial.map (algebraMap ℤ ℚ)
          (rothLastSlice A.P (0 : RothMvIndex 0)))).eval (A.q (Fin.last 0))) =
        MvPolynomial.eval (Fin.lastCases (A.q (Fin.last 0)) (fun _ ↦ 0))
          (rothMvHasse (rothLastIndex (0 : RothMvIndex 0) a)
            (MvPolynomial.map (algebraMap ℤ ℚ) A.P)) :=
      (rothLastSlice_hasse_eval_h A.P (0 : RothMvIndex 0) a
        (A.q (Fin.last 0))).symm
    _ = 0 := by
      rw [← hqfun]
      simpa [i] using hz

lemma roth_lemma_h :
    ∀ (n : ℕ) (θ : ℝ), 0 < θ → θ ≤ 1 →
      ∃ (δ : ℝ) (Q R : ℕ), 0 < δ ∧ δ ≤ 1 ∧ 2 ≤ Q ∧ 1 ≤ R ∧
        ∀ A : RothLemmaInput n δ Q R,
          ¬rothMvVanishesBelow
            (MvPolynomial.map (algebraMap ℤ ℚ) A.P) A.q A.r θ := by
  intro n
  induction n with
  | zero =>
      intro θ hθ hθone
      exact roth_lemma_base_h θ hθ hθone
  | succ n ih =>
      intro θ hθ hθone
      let τ := θ ^ 2 / 256
      have hτ : 0 < τ := by dsimp [τ]; positivity
      have hτone : τ ≤ 1 := by
        dsimp [τ]
        nlinarith [sq_nonneg (θ - 1), sq_nonneg θ]
      obtain ⟨δI, QI, RI, hδI, hδIone, hQItwo, hRIone, hIH⟩ :=
        ih τ hτ hτone
      let δu := τ / 4
      let δc := min δI δu
      let A0 : ℕ := n + 6
      let lam := δc / (4 * (A0 : ℝ))
      have hδu : 0 < δu := by dsimp [δu]; positivity
      have hδc : 0 < δc := lt_min hδI hδu
      have hA0 : 0 < A0 := by dsimp [A0]; omega
      have hlam : 0 < lam := by dsimp [lam]; positivity
      obtain ⟨QA, hQAtwo, hQA⟩ := Any_Ge_2AndAll_Le2Rpow.of.Gt_0 hlam
      let δ := min (θ / 4) (δc / 4)
      let Q := max QI QA
      let R := max RI (max 1 ⌈16 / θ⌉₊)
      have hδ : 0 < δ := lt_min (by positivity) (by positivity)
      have hδtheta : δ ≤ θ / 4 := min_le_left _ _
      have hδc_le : δ ≤ δc / 4 := min_le_right _ _
      have hδI_le : δ ≤ δI :=
        hδc_le.trans (by
          have := min_le_left δI δu
          linarith)
      have hδu_le : δ ≤ δu :=
        hδc_le.trans (by
          have := min_le_right δI δu
          linarith)
      have hmargin : δ + lam * A0 ≤ δc / 2 := by
        have hA0R : (0 : ℝ) < A0 := by exact_mod_cast hA0
        have hlamA : lam * A0 = δc / 4 := by
          dsimp [lam]
          field_simp
        rw [hlamA]
        linarith
      have hmarginI : δ + lam * A0 ≤ δI :=
        hmargin.trans (by
          have := min_le_left δI δu
          linarith)
      have hmarginU : δ + lam * A0 ≤ δu :=
        hmargin.trans (by
          have := min_le_right δI δu
          linarith)
      refine ⟨δ, Q, R, hδ, hδtheta.trans (by linarith),
        hQItwo.trans (le_max_left _ _), le_max_of_le_right (le_max_left _ _),
        fun X hvan ↦ ?_⟩
      have hQXI : QI ≤ (X.q 0).den :=
        (le_max_left QI QA).trans X.den_large
      have hQXA : QA ≤ (X.q 0).den :=
        (le_max_right QI QA).trans X.den_large
      have hq0 : 2 ≤ (X.q 0).den := hQItwo.trans hQXI
      have hrpos : ∀ h, 0 < X.r h := fun h ↦
        lt_of_lt_of_le Nat.zero_lt_one ((le_max_of_le_right (le_max_left _ _)).trans
          (X.r_large h))
      obtain ⟨d⟩ := roth_exists_determinant_data_h X.P X.r X.P_ne X.P_degree
      obtain ⟨e⟩ := roth_exists_integral_factor_data_h d
      let r0 := X.r 0
      let rlast := X.r (Fin.last (n + 1))
      have hrlast : 0 < rlast := hrpos _
      have hrlast0 : rlast ≤ r0 := X.r_antitone (Fin.zero_le _)
      have hk0 : d.k ≤ 2 * r0 := calc
          _ ≤ rlast + 1 := d.k_le
          _ ≤ r0 + 1 := Nat.add_le_add_right hrlast0 1
          _ ≤ 2 * r0 := by omega
      have hsumFirst : (∑ h : Fin (n + 1), X.r h.castSucc) ≤ (n + 1) * r0 := calc
          _ ≤ ∑ _h : Fin (n + 1), r0 := by
            gcongr with h
            exact X.r_antitone (Fin.zero_le _)
          _ = (n + 1) * r0 := by simp
      have hsumAll : (∑ h, X.r h) ≤ (n + 2) * r0 := calc
          _ ≤ ∑ _h : Fin (n + 2), r0 := by
            gcongr with h
            exact X.r_antitone (Fin.zero_le _)
          _ = (n + 2) * r0 := by simp
      let CV := d.k * d.k + d.k * (∑ h : Fin (n + 1), X.r h.castSucc)
      let CW := d.k * rlast + d.k * d.k + d.k * (∑ h, X.r h)
      have hCV : CV ≤ A0 * d.k * r0 := calc
          _ ≤ d.k * (2 * r0) + d.k * ((n + 1) * r0) := by
            dsimp [CV]
            exact Nat.add_le_add (Nat.mul_le_mul_left d.k hk0)
              (Nat.mul_le_mul_left d.k hsumFirst)
          _ = (n + 3) * d.k * r0 := by ring
          _ ≤ A0 * d.k * r0 := by
            gcongr
            dsimp [A0]
            omega
      have hCW : CW ≤ A0 * d.k * r0 := calc
          _ ≤ d.k * r0 + d.k * (2 * r0) + d.k * ((n + 2) * r0) := by
            dsimp [CW]
            exact Nat.add_le_add
              (Nat.add_le_add (Nat.mul_le_mul_left d.k hrlast0)
                (Nat.mul_le_mul_left d.k hk0))
              (Nat.mul_le_mul_left d.k hsumAll)
          _ = (n + 5) * d.k * r0 := by ring
          _ ≤ A0 * d.k * r0 := by
            gcongr
            dsimp [A0]
            omega
      have hVheight : (rothMvL1 d.V : ℝ) ≤
          Real.rpow (X.q 0).den (δI * (d.k * r0)) := by
        have hcoarseNat := roth_determinant_V_l1_coarse_h d
        have hcoarse : (rothMvL1 d.V : ℝ) ≤
            ((2 ^ CV * rothMvL1 X.P ^ d.k : ℕ) : ℝ) := by
          exact_mod_cast hcoarseNat
        have habsorb := MulPowS.le.RpowMulMulAdd_Mul.of.Le_MulMul.Le_RpowMul.Le_Rpow.Ge_0.Ge (X.q 0).den (rothMvL1 X.P)
          CV d.k r0 A0 δ lam hq0 hlam.le (hQA _ hQXA) X.height hCV
        refine hcoarse.trans (habsorb.trans ?_)
        apply Real.rpow_le_rpow_of_exponent_le (by
          exact_mod_cast (show 1 ≤ (X.q 0).den by omega) : (1 : ℝ) ≤ (X.q 0).den)
        have hk0R : (0 : ℝ) ≤ d.k * r0 := by positivity
        nlinarith [mul_le_mul_of_nonneg_right hmarginI hk0R]
      let rV : Fin (n + 1) → ℕ := fun h ↦ d.k * X.r h.castSucc
      let qV : Fin (n + 1) → ℚ := fun h ↦ X.q h.castSucc
      let B : RothLemmaInput n δI QI RI := {
        P := d.V
        r := rV
        q := qV
        P_ne := d.V_ne
        P_degree := d.V_degree
        r_large := fun h ↦ by
          have hrh : RI ≤ X.r h.castSucc :=
            (le_max_left RI (max 1 ⌈16 / θ⌉₊)).trans (X.r_large h.castSucc)
          dsimp [rV]
          nlinarith [d.k_pos]
        den_large := by simpa [qV] using hQXI
        den_monotone := fun i j hij ↦
          X.den_monotone (Fin.castSucc_le_castSucc_iff.mpr hij)
        r_antitone := fun i j hij ↦ by
          dsimp [rV]
          exact Nat.mul_le_mul_left d.k
            (X.r_antitone (Fin.castSucc_le_castSucc_iff.mpr hij))
        separated := fun i ↦ by
          have hp := X.separated i.castSucc
          dsimp [rV]
          push_cast
          have hkR : (0 : ℝ) ≤ d.k := by positivity
          have hki : (0 : ℝ) ≤ d.k * X.r i.castSucc.castSucc := by positivity
          calc
            _ =
                (d.k : ℝ) * X.r i.castSucc.succ := by rw [Fin.succ_castSucc]
            _ ≤ (d.k : ℝ) * (δ * X.r i.castSucc.castSucc) :=
              mul_le_mul_of_nonneg_left hp hkR
            _ = δ * ((d.k : ℝ) * X.r i.castSucc.castSucc) := by ring
            _ ≤ δI * ((d.k : ℝ) * X.r i.castSucc.castSucc) :=
              mul_le_mul_of_nonneg_right hδI_le hki
        den_power := fun h ↦ by
          have hp := X.den_power h.castSucc
          dsimp [qV, rV]
          calc
            _ =
                ((X.q 0).den ^ X.r 0) ^ d.k := by rw [mul_comm, pow_mul]
            _ ≤ ((X.q h.castSucc).den ^ X.r h.castSucc) ^ d.k := by gcongr
            _ = (X.q h.castSucc).den ^ (d.k * X.r h.castSucc) := by
              rw [mul_comm, pow_mul]
        height := by simpa [rV, qV, r0, mul_assoc] using hVheight
      }
      have hVnot := hIH B
      obtain ⟨iV, hiVweight, hiVne⟩ :=
        roth_exists_nonzero_hasse_of_not_vanishesBelow_h hVnot
      have hWheight0 : (rothPolyL1 e.WZ : ℝ) ≤
          Real.rpow (X.q 0).den (δu * (d.k * r0)) := by
        have hcoarseNat := roth_determinant_W_l1_coarse_h d e hrlast
        have hcoarse : (rothPolyL1 e.WZ : ℝ) ≤
            ((2 ^ CW * rothMvL1 X.P ^ d.k : ℕ) : ℝ) := by
          exact_mod_cast hcoarseNat
        have habsorb := MulPowS.le.RpowMulMulAdd_Mul.of.Le_MulMul.Le_RpowMul.Le_Rpow.Ge_0.Ge (X.q 0).den (rothMvL1 X.P)
          CW d.k r0 A0 δ lam hq0 hlam.le (hQA _ hQXA) X.height hCW
        refine hcoarse.trans (habsorb.trans ?_)
        apply Real.rpow_le_rpow_of_exponent_le (by
          exact_mod_cast (show 1 ≤ (X.q 0).den by omega) : (1 : ℝ) ≤ (X.q 0).den)
        have hk0R : (0 : ℝ) ≤ d.k * r0 := by positivity
        nlinarith [mul_le_mul_of_nonneg_right hmarginU hk0R]
      have hWheight : (rothPolyL1 e.WZ : ℝ) ≤
          Real.rpow (X.q (Fin.last (n + 1))).den
            ((τ / 4) * (d.k * rlast)) := by
        refine hWheight0.trans ?_
        have hp := X.den_power (Fin.last (n + 1))
        have ht := RpowMul.le.RpowMul.of.LePow_Pow.Ge_0 (X.q 0).den
          (X.q (Fin.last (n + 1))).den r0 rlast (δu * d.k)
          (by positivity) hp
        simpa [δu, Nat.cast_mul, mul_assoc] using ht
      have hqlast : 2 ≤ (X.q (Fin.last (n + 1))).den :=
        hq0.trans (X.den_monotone (Fin.zero_le _))
      obtain ⟨aW, haWweight, haWne⟩ := roth_univariate_small_hasse_h τ hτ e.WZ
        (X.q (Fin.last (n + 1))) (d.k * rlast) (Nat.mul_pos d.k_pos hrlast)
        hqlast e.WZ_ne (by simpa [Nat.cast_mul] using hWheight)
      let rprev := X.r (Fin.last n).castSucc
      have hrprev : 0 < rprev := hrpos _
      have hprefixMin : ∀ h : Fin (n + 1), rprev ≤ X.r h.castSucc := by
        intro h
        exact X.r_antitone (Fin.castSucc_le_castSucc_iff.mpr (Fin.le_last h))
      have hrowWeight : ∀ s, rothMvWeight (fun h ↦ X.r h.castSucc) (d.row s) ≤ δ := by
        intro s
        calc
          _ ≤
              (rothMvOrder (d.row s) : ℝ) / rprev :=
            rothMvWeight_le_order_div_h _ _ hrprev hprefixMin
          _ ≤ (s : ℝ) / rprev := by
            gcongr
            exact_mod_cast d.row_order s
          _ ≤ (rlast : ℝ) / rprev := by
            gcongr
            have hkLast : d.k ≤ rlast + 1 := by simpa [rlast] using d.k_le
            have hsNat : s.val ≤ rlast := by omega
            exact_mod_cast hsNat
          _ ≤ δ := by
            apply (div_le_iff₀ (by exact_mod_cast hrprev : (0 : ℝ) < rprev)).2
            simpa [rprev, rlast] using
              X.separated (Fin.last n)
      let u : Fin d.k → RothMvIndex (n + 2) :=
        fun s ↦ rothLastIndex (d.row s) 0
      let v : Fin d.k → RothMvIndex (n + 2) :=
        fun t ↦ rothLastIndex 0 t.val
      let L : ℝ := ∑ t : Fin d.k, max 0 (θ - δ - (t : ℝ) / rlast)
      have hrowWeightFull : ∀ s, rothMvWeight X.r (u s) ≤ δ := by
        intro s
        rw [rothMvWeight_lastIndex_h]
        simpa [u, rothMvWeight] using hrowWeight s
      have hdetVan := rothHasseDet_vanishesBelow_of_rowWeight_le_h
        hvan u v hrowWeightFull
      have hvweight : ∀ t : Fin d.k,
          rothMvWeight X.r (v t) = (t : ℝ) / rlast := by
        intro t
        rw [rothMvWeight_lastIndex_h]
        simp [rlast, rothMvWeight]
      simp_rw [hvweight] at hdetVan
      have hmapU : MvPolynomial.map (algebraMap ℤ ℚ) d.U =
          rothHasseDet (MvPolynomial.map (algebraMap ℤ ℚ) X.P) u v := by
        rw [d.U_def, rothHasseDet_map_h]
      rw [← hmapU] at hdetVan
      change rothMvVanishesBelow
        (MvPolynomial.map (algebraMap ℤ ℚ) d.U) X.q X.r L at hdetVan
      have hscaledVan0 := rothMvVanishesBelow_smul_h hdetVan
        (d.V.coeff e.coeffIndex : ℚ)
      have hscaledVan := rothMvVanishesBelow_mul_weights_h hscaledVan0 d.k_pos hrpos
      have hrlarge : 16 ≤ θ * rlast := by
        have hceil : 16 / θ ≤ (⌈16 / θ⌉₊ : ℝ) := Nat.le_ceil _
        have hRlast : ⌈16 / θ⌉₊ ≤ rlast :=
          (le_max_of_le_right (le_max_right 1 ⌈16 / θ⌉₊)).trans
            (X.r_large (Fin.last (n + 1)))
        have hcast : (⌈16 / θ⌉₊ : ℝ) ≤ rlast := by exact_mod_cast hRlast
        have := hceil.trans hcast
        calc
          _ = θ * (16 / θ) := by field_simp
          _ ≤ θ * rlast := mul_le_mul_of_nonneg_left this hθ.le
      have htri : θ ^ 2 / 64 ≤ L / d.k := by
        exact roth_triangular_sum_lower_h hθ hθone hδtheta hrlast hrlarge
          d.k_pos d.k_le
      have hsmall : 2 * τ < L / d.k := by
        have : 2 * τ < θ ^ 2 / 64 := by
          dsimp [τ]
          nlinarith [sq_pos_of_pos hθ]
        exact this.trans_le htri
      let qV' : Fin (n + 1) → ℚ := fun h ↦ X.q h.castSucc
      have hqeta : X.q = Fin.lastCases (X.q (Fin.last (n + 1))) qV' := by
        funext h
        refine Fin.lastCases ?_ (fun j ↦ ?_) h
        · exact (Fin.lastCases_last (motive := fun _ : Fin (n + 2) ↦ ℚ)
            (last := X.q (Fin.last (n + 1))) (cast := qV')).symm
        · exact (Fin.lastCases_castSucc (motive := fun _ : Fin (n + 2) ↦ ℚ)
            (last := X.q (Fin.last (n + 1))) (cast := qV') j).symm
      have hfullne :
          MvPolynomial.eval X.q
            (rothMvHasse (rothLastIndex iV aW)
              ((d.V.coeff e.coeffIndex : ℚ) •
                MvPolynomial.map (algebraMap ℤ ℚ) d.U)) ≠ 0 := by
        rw [hqeta]
        rw [rothMvHasse_eval_last_of_factorization_h _ _ _ e.scaled_factorization]
        exact mul_ne_zero hiVne haWne

      have hiweight : rothMvWeight (fun h ↦ d.k * X.r h)
          (rothLastIndex iV aW) < L / d.k := by
        rw [rothMvWeight_lastIndex_h]
        change rothMvWeight rV iV < τ at hiVweight
        have haWweight' : (aW : ℝ) / ((d.k : ℝ) * rlast) < τ := by
          simpa [Nat.cast_mul] using haWweight
        have hadd : rothMvWeight rV iV +
            (aW : ℝ) / (d.k * rlast) < 2 * τ := by
          nlinarith
        simpa [rV, rlast, Nat.cast_mul] using hadd.trans hsmall
      have hz := hscaledVan (rothLastIndex iV aW) hiweight
      rw [rothTranslate_coeff_eq_eval_hasse_h] at hz
      exact hfullne hz

lemma roth_ridout_exists_approximation_chain_h {α p : ℝ} (hp : 0 < p)
    (A : Set ℚ)
    (hA : A ⊆ {q : ℚ | |α - (q : ℝ)| < 1 / Real.rpow (q.den : ℝ) p})
    (hinf : A.Infinite) (m N K : ℕ) :
    ∃ q : Fin (m + 1) → ℚ,
      (∀ h, q h ∈ A) ∧
      N < (q 0).den ∧
      ∀ h : Fin m, (q h.castSucc).den ^ K < (q h.succ).den := by
  induction m with
  | zero =>
      obtain ⟨a, ha, hN⟩ := Any_Lt_Den.of.Infinite.Subset_SetOfLtAbsSub_Div1RpowDen.Gt_0 A N hp hA hinf
      let q : Fin 1 → ℚ := fun _ ↦ a
      exact ⟨q, fun _ ↦ ha, by simpa [q] using hN, fun h ↦ Fin.elim0 h⟩
  | succ m ih =>
      obtain ⟨q, hq, hqN, hchain⟩ := ih
      obtain ⟨a, ha, hlast⟩ := Any_Lt_Den.of.Infinite.Subset_SetOfLtAbsSub_Div1RpowDen.Gt_0 A
        ((q (Fin.last m)).den ^ K) hp hA hinf
      let q' : Fin (m + 2) → ℚ := Fin.lastCases a q
      refine ⟨q', ?_, ?_, ?_⟩
      · intro h
        refine Fin.lastCases ?_ (fun j ↦ ?_) h
        · simpa [q'] using ha
        · simpa [q'] using hq j
      · change N < (q' (0 : Fin (m + 2))).den
        simpa only [show (0 : Fin (m + 2)) = (0 : Fin (m + 1)).castSucc by rfl,
          q', Fin.lastCases_castSucc] using hqN
      · intro h
        refine Fin.lastCases ?_ (fun j ↦ ?_) h
        · simpa [q'] using hlast
        · simpa only [q', Fin.lastCases_castSucc, Fin.succ_castSucc] using hchain j

lemma roth_rational_vanishing_of_real_hasse_zero_h {m : ℕ}
    (P : MvPolynomial (Fin m) ℤ) (q : Fin m → ℚ) (r : Fin m → ℕ) (θ : ℝ)
    (hzero : ∀ i : RothMvIndex m, rothMvWeight r i ≤ θ →
      MvPolynomial.eval₂ (algebraMap ℤ ℝ) (fun h ↦ (q h : ℝ))
        (rothMvHasse i P) = 0) :
    rothMvVanishesBelow (MvPolynomial.map (algebraMap ℤ ℚ) P) q r θ := by
  intro i hi
  rw [rothTranslate_coeff_eq_eval_hasse_h, ← rothMvHasse_map_h,
    ← MvPolynomial.eval₂_eq_eval_map]
  have hcast :=
    MvPolynomial.EvalAlgebraMap.eq.Eval_AlgebraMapFun (P := rothMvHasse i P) (q := q)
  have hR := hzero i hi.le
  have : ((MvPolynomial.eval₂ (algebraMap ℤ ℚ) q (rothMvHasse i P) : ℚ) : ℝ) = 0 := by
    rw [hcast, hR]
  exact_mod_cast this
