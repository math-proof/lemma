/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/KestenAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Universality.Defs.Part7
import Theorem.StatisticalMechanics.Code.Universality.BXPTransfer.Part2
import Theorem.StatisticalMechanics.Code.Universality.RSWStrip.Part3
import Theorem.StatisticalMechanics.Code.Universality.KestenHalf
import Theorem.StatisticalMechanics.Code.Universality.KestenAssembly
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

open StatMech.Lattice StatMech.TwoDim


structure KaSelfDualBoxSeed (μ : Measure (ConfigSpace (Sym2 (Site 2)))) where
  
  c : ℝ
  
  c_pos : 0 < c
  

  wide : ∀ n : ℕ, c ≤ μ.real (StatMech.RSW.Box.horizontalCrossingEvent 0 (2 * (n : ℤ)) 0 (n : ℤ))
  

  tall : ∀ n : ℕ, c ≤ μ.real (StatMech.RSW.Box.verticalCrossingEvent 0 (n : ℤ) 0 (2 * (n : ℤ)))


structure KaCrossingTranslationInvariant
    (μ : Measure (ConfigSpace (Sym2 (Site 2)))) : Prop where
  
  horiz : ∀ (τ : Site 2) (a b : ℤ),
    μ.real (translatedHorizontalCrossingEvent τ a b)
      = μ.real (TwoDim.horizontalCrossingEvent a b)
  
  vert : ∀ (τ : Site 2) (a b : ℤ),
    μ.real (translatedVerticalCrossingEvent τ a b)
      = μ.real (TwoDim.verticalCrossingEvent a b)


end Universality
end StatMech
