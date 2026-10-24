/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/HigherDerivation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finite

set_option maxHeartbeats 800000

universe v u w

namespace TensorCategories

section Ext1UnitVanishing

/-- A higher derivation system on a `k`-algebra `A` augmented by `ε : A →ₐ[k] k`: a sequence of
`k`-linear functionals `χ n : A → k` with `χ 0 = ε` and the Leibniz-type product formula
`χ_n(ab) = ∑_j (n choose j) χ_j(a) χ_{n-j}(b)`. Used to prove vanishing of higher derivations
on finite-dimensional algebras in characteristic zero. -/
structure HigherDerivationSystem (k : Type w) [Field k] (A : Type w) [Ring A] [Algebra k A]
    (ε : A →ₐ[k] k) where
  χ : ℕ → (A →ₗ[k] k)
  χ_zero : χ 0 = ε.toLinearMap
  χ_mul : ∀ (n : ℕ) (a b : A),
    χ n (a * b) = ∑ j ∈ Finset.range (n + 1),
      (n.choose j : k) * χ j a * χ (n - j) b

/-- Main vanishing theorem (used in the proof of Theorem 1.27.4): on a finite-dimensional
algebra in characteristic zero, the first higher derivation `χ 1` of any system is zero. -/
theorem higher_derivation_vanishes [CharZero k] [FiniteDimensional k A] :
    hds.χ 1 = 0 := by
  by_contra hne
  have hne' : ∃ a₀ : A, hds.χ 1 a₀ ≠ 0 := by
    by_contra h; push Not at h; exact hne (LinearMap.ext h)
  obtain ⟨a₀, ha₀⟩ := hne'
  set a := a₀ - algebraMap k A (ε a₀)
  have ha_ker : ε a = 0 := by
    show ε (a₀ - algebraMap k A (ε a₀)) = 0
    rw [map_sub, AlgHom.commutes]; exact sub_self _
  have hχ₁a : hds.χ 1 a ≠ 0 := by
    show hds.χ 1 (a₀ - algebraMap k A (ε a₀)) ≠ 0
    rw [map_sub, hds.χ_one_algebraMap, sub_zero]; exact ha₀

  have hli := hds.powers_linearIndependent ha_ker hχ₁a

  set N := Module.finrank k A + 1
  have hli_fin : LinearIndependent k ((fun n : ℕ => a ^ n) ∘ (Fin.val : Fin N → ℕ)) :=
    hli.comp Fin.val Fin.val_injective

  have hcard := hli_fin.fintype_card_le_finrank
  rw [Fintype.card_fin] at hcard
  omega

end HigherDerivationSystem

/-- Typeclass packaging the vanishing of `χ 1` for every higher derivation system on every
finite-dimensional `k`-algebra, used as a hypothesis in higher-level results. -/
class HasHigherDerivationContradiction (k : Type w) [Field k] [CharZero k] : Prop where
  higher_derivation_vanishes :
    ∀ (A : Type w) [Ring A] [Algebra k A] [FiniteDimensional k A]
      (ε : A →ₐ[k] k) (hds : HigherDerivationSystem k A ε),
      hds.χ 1 = 0

/-- Any field of characteristic zero satisfies `HasHigherDerivationContradiction`, via the
vanishing theorem `higher_derivation_vanishes`. -/
instance instHasHigherDerivationContradiction (k : Type w) [Field k] [CharZero k] :
    HasHigherDerivationContradiction k where
  higher_derivation_vanishes := fun _ _ _ _ _ hds =>
    hds.higher_derivation_vanishes

end Ext1UnitVanishing

end TensorCategories
