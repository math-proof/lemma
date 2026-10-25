/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SymbolDet.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib


namespace StatMech.Onsager

noncomputable def ons_KWsymbolMat (x ω z₁ z₂ : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![ 1 - x*z₁,              -x*(-Complex.I*ω)*z₂,   0,                      -x*ω*z₂⁻¹ ;
      -x*ω*z₁,               1 - x*z₂,               -x*(-Complex.I*ω)*z₁⁻¹, 0 ;
      0,                     -x*ω*z₂,                1 - x*z₁⁻¹,             -x*(-Complex.I*ω)*z₂⁻¹ ;
      -x*(-Complex.I*ω)*z₁,  0,                      -x*ω*z₁⁻¹,              1 - x*z₂⁻¹ ]

end StatMech.Onsager
