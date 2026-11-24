module
public import Mathlib
public import Theorem.Algebra.AdicCompletion.PolynomialCompletion.Part8
public import Theorem.Algebra.AdicCompletion.RingFunctoriality.Part7
public import Theorem.Algebra.AdicCompletion.Semilocal.Part6
public import Theorem.Algebra.AdicCompletion.TensorRing.Part4
public import Theorem.Algebra.AdicCompletion.GaloisAction.Part6
public import Def.Algebra.AdicCompletion.Localization
open IsLocalRing
open scoped AdicCompletion.GaloisAction


public section

namespace BDescN6

end BDescN6

/-- Algebra structure on adic completions along a lying-over prime. -/
noncomputable instance instAlgebraAdicCompletion {O : Type*} [CommRing O] [IsLocalRing O]
    {C : Type*} [CommRing C] [Algebra O C] {𝔫 : Ideal C} [𝔫.LiesOver (maximalIdeal O)] :
    Algebra (AdicCompletion (maximalIdeal O) O) (AdicCompletion 𝔫 C) :=
  AdicCompletion.instAlgebraOfLiesOver (maximalIdeal O) 𝔫

noncomputable instance instIsScalarTowerAdicCompletion {O : Type*} [CommRing O] [IsLocalRing O]
    {C : Type*} [CommRing C] [Algebra O C] {𝔫 : Ideal C} [𝔫.LiesOver (maximalIdeal O)] :
    IsScalarTower O (AdicCompletion (maximalIdeal O) O) (AdicCompletion 𝔫 C) :=
  AdicCompletion.instIsScalarTowerOfLiesOver (maximalIdeal O) 𝔫
