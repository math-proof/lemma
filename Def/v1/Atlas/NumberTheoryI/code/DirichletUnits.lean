/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletUnits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.NumberField.Units.Regulator
import Mathlib.NumberTheory.FunctionField
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody
import Mathlib.NumberTheory.NumberField.ProductFormula
open scoped NumberField Classical Polynomial nonZeroDivisors NNReal
open NumberField NumberField.Units NumberField.InfinitePlace
open NumberField.Units.dirichletUnitTheorem Module
open NumberField.mixedEmbedding


noncomputable section

variable (K : Type*) [Field K] [NumberField K]

def logEmbedding_def : Additive ((𝓞 K)ˣ) →+ logSpace K :=
  NumberField.Units.logEmbedding K

def def_15_3_size (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    (f : InfinitePlace K → ℝ) : ℝ :=
  (∏ w : InfinitePlace K, f w ^ mult w) / (FractionalIdeal.absNorm I : ℝ)

def def_15_3_L (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    (f : InfinitePlace K → ℝ) : Set K :=
  {x : K | x ∈ (I : Submodule (𝓞 K) K) ∧ ∀ w : InfinitePlace K, w x ≤ f w}

omit [NumberField K] in
def def_15_3_I_c_hom :
    FractionalIdeal (nonZeroDivisors (𝓞 K)) K × (InfinitePlace K → ℝ) →*
      FractionalIdeal (nonZeroDivisors (𝓞 K)) K :=
  MonoidHom.fst _ _

def arakelovL (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    (f : InfinitePlace K → ℝ) : Set K :=
  {x : K | x ∈ (I : Submodule (𝓞 K) K) ∧ ∀ w : InfinitePlace K, w x ≤ f w}

def prop_15_11_basisUnitLattice : Basis (Fin (rank K)) ℤ (unitLattice K) :=
  basisUnitLattice K

def placesAboveInfty (Fq F : Type*) [Field Fq] [Field F]
    [Algebra (RatFunc Fq) F] :
    Set (Valuation F (WithZero (Multiplicative ℤ))) :=
  {v | (v.comap (algebraMap (RatFunc Fq) F)).IsEquiv
         (FunctionField.inftyValuation Fq)}

def FunctionField.unitRank (Fq F : Type*) [Field Fq] [Field F]
    [Algebra (RatFunc Fq) F] : ℕ :=
  Nat.card (placesAboveInfty Fq F) - 1

def FunctionField.torsionUnits (Fq F : Type*) [Field Fq] [Field F]
    [Algebra Fq[X] F] : Subgroup (FunctionField.ringOfIntegers Fq F)ˣ :=
  CommGroup.torsion (FunctionField.ringOfIntegers Fq F)ˣ

def def_15_16_regulator : ℝ := regulator K

def def_15_16_regOfFamily (u : Fin (rank K) → (𝓞 K)ˣ) : ℝ := regOfFamily u

def arakelovDivisor_size (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    (f : InfinitePlace K → ℝ) : ℝ :=
  def_15_3_size K I f

def arakelovDivisor_L (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    (f : InfinitePlace K → ℝ) : Set K :=
  def_15_3_L K I f

omit [NumberField K] in
def arakelovDivisor_projection_hom :
    FractionalIdeal (nonZeroDivisors (𝓞 K)) K × (InfinitePlace K → ℝ) →*
      FractionalIdeal (nonZeroDivisors (𝓞 K)) K :=
  def_15_3_I_c_hom K

def basisOfUnitLattice : Basis (Fin (rank K)) ℤ (unitLattice K) :=
  prop_15_11_basisUnitLattice K

def regulatorValue : ℝ := def_15_16_regulator K

def regulatorOfFamily (u : Fin (rank K) → (𝓞 K)ˣ) : ℝ :=
  def_15_16_regOfFamily K u

end
