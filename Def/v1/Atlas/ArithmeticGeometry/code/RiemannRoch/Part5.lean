/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RiemannRoch.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Finite
import Def.v1.Atlas.ArithmeticGeometry.code.EffectiveDivisors
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.EffectiveDivisors
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.CanonicalDivisors
import Def.v1.Atlas.ArithmeticGeometry.code.CanonicalDivisors.Part2
import Theorem.v1.Atlas.ArithmeticGeometry.code.RiemannRoch.Part4
open scoped RestrictedProduct

variable {F : Type*} [Field F] {P : Type*} {O : P → ValuationSubring F}


/-- The *Riemann-Roch space* $\mathcal{L}(D) := \{f \in F : f = 0 \text{ or }
\operatorname{div}(f) + D \ge 0\}$, viewed as a $k$-subspace of $F$. -/
noncomputable def riemannRochSpace (D : CurveDivisor C) : Submodule k F where
  carrier := {f | f = 0 ∨ ∃ (hf : f ≠ 0),
    (principalDivisor (Units.mk0 f hf) + D).IsEffective}
  zero_mem' := Or.inl rfl
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    by_cases hab : a + b = 0
    · exact Or.inl hab
    · right; refine ⟨hab, fun P => ?_⟩
      simp only [Finsupp.coe_add, Pi.add_apply, principalDivisor_apply]
      obtain (rfl | ⟨ha_ne, ha_eff⟩) := ha
      ·
        simp only [zero_add] at hab ⊢
        exact (hb.resolve_left fun h => hab (h ▸ rfl)).choose_spec P
      · obtain (rfl | ⟨hb_ne, hb_eff⟩) := hb
        ·
          simp only [add_zero] at hab ⊢; exact ha_eff P
        ·
          have h := RiemannRochData.ord_add_ge_min (k := k) P
            (Units.mk0 a ha_ne) (Units.mk0 b hb_ne) hab
          simp only [Units.val_mk0] at h
          have haP := ha_eff P
          have hbP := hb_eff P
          simp only [Finsupp.coe_add, Pi.add_apply, principalDivisor_apply] at haP hbP
          linarith [le_min haP hbP,
                    show min (ord P (Units.mk0 a ha_ne) + D P)
                             (ord P (Units.mk0 b hb_ne) + D P) =
                         min (ord P (Units.mk0 a ha_ne))
                             (ord P (Units.mk0 b hb_ne)) + D P
                     from by omega]
  smul_mem' := by
    intro c f hf
    simp only [Set.mem_setOf_eq] at *
    by_cases hcf : c • f = 0
    · exact Or.inl hcf
    · right; refine ⟨hcf, fun P => ?_⟩
      simp only [Finsupp.coe_add, Pi.add_apply, principalDivisor_apply]
      obtain (rfl | ⟨hf_ne, hf_eff⟩) := hf
      · exact absurd (smul_zero c) hcf
      ·
        have hc_ne : c ≠ 0 := by intro hc; exact hcf (hc ▸ zero_smul k f)
        have key : Units.mk0 (c • f) hcf =
          Units.map (algebraMap k F).toMonoidHom (Units.mk0 c hc_ne) *
            Units.mk0 f hf_ne := by
          apply Units.ext; simp [Algebra.smul_def]
        rw [key, ord_mul,
            RiemannRochData.ord_algebraMap (F := F) (k := k), zero_add]
        exact hf_eff P

