/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingAgreementGramVarianceCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib


namespace StatMech.FrontierA

open scoped BigOperators

noncomputable section

def gramVarianceCounterDiagonal (i : Fin 3) : Real :=
  if i.val = 0 then 1 / 4 else if i.val = 1 then 29 / 4 else 5 / 4


def gramVarianceCounterKernel (i j : Fin 3) : Real :=
  (if i.val = j.val then gramVarianceCounterDiagonal i else 0) + 1 / 4

def gramVarianceCounterMass (i : Fin 3) : Real :=
  ∑ j, gramVarianceCounterKernel j i

def gramVarianceCounterReflect (i : Fin 3) : Fin 3 :=
  ⟨2 - i.val, by omega⟩

def gramVarianceCounterValue (i : Fin 3) : Real :=
  if i.val = 0 then -2 else if i.val = 1 then 0 else 2

def gramVarianceCounterPlusWeight (i : Fin 3) : Real :=
  gramVarianceCounterMass i *
    (if i.val = 0 then 2 / 3 else if i.val = 1 then 1 else 3 / 2)

def gramVarianceCounterMinusWeight (i : Fin 3) : Real :=
  gramVarianceCounterMass i *
    (if i.val = 0 then 3 / 2 else if i.val = 1 then 1 else 2 / 3)

def finiteWeightedVariance {E : Type*} [Fintype E]
    (w X : E -> Real) : Real :=
  (∑ i, w i * X i ^ 2) / (∑ i, w i) -
    ((∑ i, w i * X i) / (∑ i, w i)) ^ 2

end
end StatMech.FrontierA
