/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/KostantTheorem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.LieGroups.code.HarishChandraIsomorphism.Part2
import Lemma.Int.Any_All_Eq.of.LeKer_Ker.Surjective
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.InvariantBasisNumber
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Lie.CartanSubalgebra
import Mathlib.Algebra.Lie.Weights.Basic
import Mathlib.Algebra.Lie.Abelian
import Mathlib.RingTheory.SimpleModule.Basic


noncomputable section

variable (R : Type*) [CommRing R]

variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

variable {R 𝔤}

def qInteger (d : ℕ) : PowerSeries ℤ :=
  ∑ i ∈ Finset.range d, PowerSeries.X ^ i

variable {P' : Type*} [DecidableEq P'] [AddCommGroup P']

def groupRingExp (α : P') : AddMonoidAlgebra ℤ P' := Finsupp.single α 1

def groupRingOneMinusExp (α : P') : AddMonoidAlgebra ℤ P' :=
  Finsupp.single (0 : P') 1 - Finsupp.single α 1

def numeratorProd (S : Finset P') : AddMonoidAlgebra ℤ P' :=
  S.prod (fun α => groupRingOneMinusExp α)

def groupRingCT (f : AddMonoidAlgebra ℤ P') : ℤ := f 0

def singleFactorCoeff (α : P') (n : ℕ) : AddMonoidAlgebra ℤ P' :=
  Finsupp.single (n • α) (1 : ℤ) - Finsupp.single ((n + 1) • α) 1

def singleFactorPS (α : P') : PowerSeries (AddMonoidAlgebra ℤ P') :=
  PowerSeries.mk (singleFactorCoeff α)

def fullProductPS (S : Finset P') : PowerSeries (AddMonoidAlgebra ℤ P') :=
  S.prod (fun α => singleFactorPS α)

def geomFactorCoeff (α : P') (n : ℕ) : AddMonoidAlgebra ℤ P' :=
  Finsupp.single (n • α) (1 : ℤ)

def geomFactorPS (α : P') : PowerSeries (AddMonoidAlgebra ℤ P') :=
  PowerSeries.mk (geomFactorCoeff α)

def geomProductPS (S : Finset P') : PowerSeries (AddMonoidAlgebra ℤ P') :=
  S.prod (fun α => geomFactorPS α)

def powerSeriesCT (f : PowerSeries (AddMonoidAlgebra ℤ P')) : PowerSeries ℤ :=
  PowerSeries.mk (fun n => groupRingCT (PowerSeries.coeff n f))

def concreteCT_fullRoots (roots : Finset P') : PowerSeries ℤ :=
  powerSeriesCT (fullProductPS roots)

def concreteCT_posRoots (roots posRoots : Finset P') : PowerSeries ℤ :=
  let C := (PowerSeries.C : AddMonoidAlgebra ℤ P' →+* PowerSeries (AddMonoidAlgebra ℤ P'))
  powerSeriesCT (C (numeratorProd posRoots) * geomProductPS roots)

def concreteCT_fullRoots_char (roots : Finset P') (chi : AddMonoidAlgebra ℤ P') :
    PowerSeries ℤ :=
  let C := (PowerSeries.C : AddMonoidAlgebra ℤ P' →+* PowerSeries (AddMonoidAlgebra ℤ P'))
  powerSeriesCT (fullProductPS roots * C chi)

def concreteCT_posRoots_lambda (roots posRoots : Finset P') (wt : P') :
    PowerSeries ℤ :=
  let C := (PowerSeries.C : AddMonoidAlgebra ℤ P' →+* PowerSeries (AddMonoidAlgebra ℤ P'))
  powerSeriesCT (C (groupRingExp wt * numeratorProd posRoots) * geomProductPS roots)

def qIntegerProd (r : ℕ) (degrees : Fin r → ℕ) : PowerSeries ℤ :=
  ∏ i : Fin r, qInteger (degrees i)

def gradedHilbertSeries (dimFun : ℕ → ℕ) : PowerSeries ℤ :=
  PowerSeries.mk (fun n => (dimFun n : ℤ))

end
