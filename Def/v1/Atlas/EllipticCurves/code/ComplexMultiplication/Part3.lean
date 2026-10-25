/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexMultiplication.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.EllipticCurves.code.EllipticFunction.Part3
import Lemma.Complex.Atlas.v1.EllipticCurves.code.EllipticFunction
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Theorem161
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Uniformization
import Structure.v1.Atlas.EllipticCurves.code.Theorem161
import Def.v1.Atlas.EllipticCurves.code.Uniformization
import Mathlib.Algebra.Ring.Subring.Defs
import Mathlib.RingTheory.Polynomial.Basic
import Theorem.v1.Atlas.EllipticCurves.code.ComplexMultiplication.Part2


namespace ComplexLattice

noncomputable section

open Pointwise

/-- The type of *proper $\mathcal{O}$-ideals*: pairs $(L, \mathrm{proof})$ where $L$ is
a complex lattice, $L$ is a proper $\mathcal{O}$-ideal (its endomorphism ring equals
$\mathcal{O}$), and $L$ is contained in $\mathcal{O}$ as a subset of $\mathbb{C}$. -/
def ProperIdeal (𝒪 : Subring ℂ) : Type :=
  { L : ComplexLattice // IsProperIdeal 𝒪 L ∧ ∀ z ∈ L.toAddSubgroup, z ∈ 𝒪 }

/-- The setoid structure on proper $\mathcal{O}$-ideals induced by ideal equivalence;
the quotient is the ideal class group of $\mathcal{O}$. -/
def properIdealSetoid (𝒪 : Subring ℂ) : Setoid (ProperIdeal 𝒪) where
  r L₁ L₂ := IsEquivalent 𝒪 L₁.val L₂.val
  iseqv := {
    refl := fun L => (isEquivalent_equivalence 𝒪).refl L.val
    symm := fun h => (isEquivalent_equivalence 𝒪).symm h
    trans := fun h₁ h₂ => (isEquivalent_equivalence 𝒪).trans h₁ h₂
  }

/-- The *ideal class group* $\mathrm{Cl}(\mathcal{O})$ of an order $\mathcal{O}$: the
quotient of proper $\mathcal{O}$-ideals by the equivalence relation of being equal up
to scaling by nonzero elements of $\mathcal{O}$.  It is a finite abelian group whose
order is the class number $h(\mathcal{O})$. -/
def IdealClassGroup (𝒪 : Subring ℂ) : Type :=
  Quotient (properIdealSetoid 𝒪)

/-- The class of a proper $\mathcal{O}$-ideal in the ideal class group. -/
def IdealClassGroup.mk (𝒪 : Subring ℂ) (L : ProperIdeal 𝒪) : IdealClassGroup 𝒪 :=
  Quotient.mk (properIdealSetoid 𝒪) L

/-- The *product* of two proper $\mathcal{O}$-ideals: given $\mathfrak{a}$ with period
pair $(\omega_1, \omega_2)$ and $\mathfrak{b}$ with period pair $(\omega_1', \omega_2')$,
the product is the lattice with period pair $(\omega_1\omega_1', \omega_1\omega_2')$.
The result is again a proper $\mathcal{O}$-ideal. -/
def ProperIdeal.mul (𝒪 : Subring ℂ) (𝔞 𝔟 : ProperIdeal 𝒪) : ProperIdeal 𝒪 :=
  let L₁ := 𝔞.val
  let L₂ := 𝔟.val


  have hω₁_ne : L₁.ω₁ ≠ 0 := by
    have := L₁.indep.ne_zero (⟨0, by omega⟩ : Fin 2)
    simpa using this
  have hindep : LinearIndependent ℝ ![L₁.ω₁ * L₂.ω₁, L₁.ω₁ * L₂.ω₂] := by
    let f : ℂ →ₗ[ℝ] ℂ := (Algebra.lmul ℝ ℂ) L₁.ω₁
    have hf_apply : ∀ x, f x = L₁.ω₁ * x := fun x => LinearMap.mul_apply' L₁.ω₁ x
    have hf_inj : Function.Injective f := by
      intro a b hab
      rw [hf_apply, hf_apply] at hab
      exact mul_left_cancel₀ hω₁_ne hab
    have hcomp : ![L₁.ω₁ * L₂.ω₁, L₁.ω₁ * L₂.ω₂] = f ∘ ![L₂.ω₁, L₂.ω₂] := by
      ext i; fin_cases i <;> simp [hf_apply]
    rw [hcomp]
    exact L₂.indep.map' f (LinearMap.ker_eq_bot_of_injective hf_inj)
  let Lprod : PeriodPair := ⟨L₁.ω₁ * L₂.ω₁, L₁.ω₁ * L₂.ω₂, hindep⟩
  ⟨Lprod,
    ⟨by


      show endomorphismRing Lprod = 𝒪
      rw [← 𝔟.prop.1]
      ext α
      simp only [mem_endomorphismRing]
      constructor
      ·
        intro hα z hz
        have hωz : L₁.ω₁ * z ∈ Lprod.lattice := by
          rw [PeriodPair.mem_lattice]
          obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.mp hz
          exact ⟨m, n, by ring⟩
        have hαωz' := hα _ hωz
        have hαωz : L₁.ω₁ * (α * z) ∈ Lprod.lattice := by
          rwa [show α * (L₁.ω₁ * z) = L₁.ω₁ * (α * z) by ring] at hαωz'
        rw [PeriodPair.mem_lattice] at hαωz
        obtain ⟨m, n, hmn⟩ := hαωz
        show α * z ∈ L₂.lattice
        rw [PeriodPair.mem_lattice]
        refine ⟨m, n, mul_left_cancel₀ hω₁_ne ?_⟩
        have : ↑m * (L₁.ω₁ * L₂.ω₁) + ↑n * (L₁.ω₁ * L₂.ω₂) = L₁.ω₁ * (α * z) := hmn
        linear_combination this

      ·
        intro hα z hz
        obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.mp hz
        show α * (↑m * (L₁.ω₁ * L₂.ω₁) + ↑n * (L₁.ω₁ * L₂.ω₂)) ∈ Lprod.lattice
        have helem : (↑m * L₂.ω₁ + ↑n * L₂.ω₂) ∈ L₂.toAddSubgroup := by
          show _ ∈ L₂.lattice
          exact PeriodPair.mem_lattice.mpr ⟨m, n, rfl⟩
        have hα_elem := hα _ helem
        obtain ⟨m', n', hm'n'⟩ := PeriodPair.mem_lattice.mp hα_elem
        rw [PeriodPair.mem_lattice]
        exact ⟨m', n', by linear_combination L₁.ω₁ * hm'n'⟩,

     by

      intro z hz
      have hω₁_mem : L₁.ω₁ ∈ 𝒪 :=
        𝔞.prop.2 L₁.ω₁ (show L₁.ω₁ ∈ L₁.toAddSubgroup from L₁.ω₁_mem_lattice)
      have hω₁'_mem : L₂.ω₁ ∈ 𝒪 :=
        𝔟.prop.2 L₂.ω₁ (show L₂.ω₁ ∈ L₂.toAddSubgroup from L₂.ω₁_mem_lattice)
      have hω₂'_mem : L₂.ω₂ ∈ 𝒪 :=
        𝔟.prop.2 L₂.ω₂ (show L₂.ω₂ ∈ L₂.toAddSubgroup from L₂.ω₂_mem_lattice)
      have hmem : z ∈ Lprod.lattice := hz
      rw [PeriodPair.mem_lattice] at hmem
      obtain ⟨m, n, rfl⟩ := hmem
      exact 𝒪.add_mem (𝒪.mul_mem (intCast_mem 𝒪 m) (𝒪.mul_mem hω₁_mem hω₁'_mem))
        (𝒪.mul_mem (intCast_mem 𝒪 n) (𝒪.mul_mem hω₁_mem hω₂'_mem))⟩⟩

/-- Commutativity of ideal multiplication up to equivalence: $\mathfrak{a}\mathfrak{b}
\sim \mathfrak{b}\mathfrak{a}$. -/
noncomputable def classNumber (𝒪 : Subring ℂ) : ℕ :=
  Nat.card (IdealClassGroup 𝒪)

end

end ComplexLattice

namespace ComplexLattice

noncomputable section

open Pointwise

/-- A subring $\mathcal{O} \subseteq \mathbb{C}$ is an *order in an imaginary quadratic
field* if it contains some non-integer element $\tau$ that satisfies a monic integer
quadratic polynomial $\tau^2 + b\tau + c = 0$ with negative discriminant $b^2 - 4c < 0$. -/
def IsImagQuadOrder (𝒪 : Subring ℂ) : Prop :=
  ∃ τ : ℂ, τ ∈ 𝒪 ∧ (∀ n : ℤ, τ ≠ (n : ℂ)) ∧
    ∃ b c : ℤ, τ * τ + (b : ℂ) * τ + (c : ℂ) = 0 ∧
      (b : ℤ) * b - 4 * c < 0

/-- The setoid structure on proper $\mathcal{O}$-ideals induced by *homothety*: two
proper ideals are identified if one is a complex scalar multiple of the other. -/
def homothetySetoidCM (𝒪 : Subring ℂ) : Setoid (ProperIdeal 𝒪) where
  r L₁ L₂ := IsHomothetic L₁.val L₂.val
  iseqv := {
    refl := fun L => isHomothetic_equivalence.refl L.val
    symm := fun h => isHomothetic_equivalence.symm h
    trans := fun h₁ h₂ => isHomothetic_equivalence.trans h₁ h₂
  }

/-- The set of *homothety classes* of proper $\mathcal{O}$-ideals.  When $\mathcal{O}$
is an order in an imaginary quadratic field, this set is in canonical bijection with
the ideal class group $\mathrm{Cl}(\mathcal{O})$. -/
def HomothetyClassCM (𝒪 : Subring ℂ) : Type :=
  Quotient (homothetySetoidCM 𝒪)

end
end ComplexLattice
