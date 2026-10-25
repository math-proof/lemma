/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STT.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ProductMeasure.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Universality.STT.Part3
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

def triAB (ω : LocalConfig) : Bool := ω.2.2 || (ω.1 && ω.2.1)

def triAC (ω : LocalConfig) : Bool := ω.2.1 || (ω.1 && ω.2.2)

def triBC (ω : LocalConfig) : Bool := ω.1 || (ω.2.1 && ω.2.2)


def starAB (ω : LocalConfig) : Bool := ω.1 && ω.2.1

def starAC (ω : LocalConfig) : Bool := ω.1 && ω.2.2

def starBC (ω : LocalConfig) : Bool := ω.2.1 && ω.2.2


def triPatABC (ω : LocalConfig) : Bool := triAB ω && triBC ω && triAC ω

def starPatABC (ω : LocalConfig) : Bool := starAB ω && starBC ω && starAC ω

def triPatSep (ω : LocalConfig) : Bool := !triAB ω && !triBC ω && !triAC ω

def starPatSep (ω : LocalConfig) : Bool := !starAB ω && !starBC ω && !starAC ω

def triPatAB (ω : LocalConfig) : Bool := triAB ω && !triAC ω && !triBC ω

def starPatAB (ω : LocalConfig) : Bool := starAB ω && !starAC ω && !starBC ω

def triPatAC (ω : LocalConfig) : Bool := triAC ω && !triAB ω && !triBC ω

def starPatAC (ω : LocalConfig) : Bool := starAC ω && !starAB ω && !starBC ω

def triPatBC (ω : LocalConfig) : Bool := triBC ω && !triAB ω && !triAC ω

def starPatBC (ω : LocalConfig) : Bool := starBC ω && !starAB ω && !starAC ω


def triProb (p0 p1 p2 : ℝ) (pat : LocalConfig → Bool) : ℝ :=
  ∑ ω : LocalConfig, if pat ω then localWeight p0 p1 p2 ω else 0


def starProb (q0 q1 q2 : ℝ) (pat : LocalConfig → Bool) : ℝ :=
  ∑ ω : LocalConfig, if pat ω then localWeight q0 q1 q2 ω else 0


end Universality
end StatMech
