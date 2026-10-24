/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ComplexMultiplication.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.EllipticCurves.code.EllipticFunction
import Lemma.Complex.Atlas.v1.EllipticCurves.code.EllipticFunction
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Theorem161
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Uniformization
import sympy.atlas.v1.Atlas.EllipticCurves.code.Theorem161
import sympy.atlas.v1.Atlas.EllipticCurves.code.Uniformization
import Mathlib.Algebra.Ring.Subring.Defs
import Mathlib.RingTheory.Polynomial.Basic

namespace ComplexLattice

noncomputable section

open Pointwise

/-- The *endomorphism ring* $\mathrm{End}(L)$ of a complex lattice $L$ is the subring
of $\mathbb{C}$ consisting of all $\alpha \in \mathbb{C}$ such that $\alpha L \subseteq L$.
Equivalently, an element $\alpha$ lies in $\mathrm{End}(L)$ iff multiplication by $\alpha$
preserves the additive subgroup underlying $L$. -/
def endomorphismRing (L : ComplexLattice) : Subring ℂ where
  carrier := { α : ℂ | ∀ z ∈ L.toAddSubgroup, α * z ∈ L.toAddSubgroup }
  mul_mem' {a b} ha hb z hz := by rw [mul_assoc]; exact ha _ (hb z hz)
  one_mem' z hz := by rwa [one_mul]
  add_mem' {a b} ha hb z hz := by
    rw [add_mul]; exact L.toAddSubgroup.add_mem (ha z hz) (hb z hz)
  zero_mem' _ _ := by rw [zero_mul]; exact L.toAddSubgroup.zero_mem
  neg_mem' {a} ha z hz := by rw [neg_mul]; exact L.toAddSubgroup.neg_mem (ha z hz)

/-- Characterization of membership in the endomorphism ring: $\alpha \in \mathrm{End}(L)$
iff $\alpha \cdot z \in L$ for every $z \in L$. -/
@[simp]
theorem mem_endomorphismRing {L : ComplexLattice} {α : ℂ} :
    α ∈ L.endomorphismRing ↔ ∀ z ∈ L.toAddSubgroup, α * z ∈ L.toAddSubgroup :=
  Iff.rfl

/-- A complex lattice $L$ is a *proper $\mathcal{O}$-ideal* if its endomorphism ring
equals $\mathcal{O}$ exactly (not just contains $\mathcal{O}$).  This is the standard
notion of proper ideal in the theory of orders in imaginary quadratic fields. -/
def IsProperIdeal (𝒪 : Subring ℂ) (L : ComplexLattice) : Prop :=
  L.endomorphismRing = 𝒪

/-- Two proper $\mathcal{O}$-ideals $L_1$ and $L_2$ are *equivalent* if there exist
nonzero $\alpha, \beta \in \mathcal{O}$ with $\alpha L_1 = \beta L_2$ as subsets of
$\mathbb{C}$.  This is the equivalence relation whose classes form the ideal class
group of $\mathcal{O}$. -/
def IsEquivalent (𝒪 : Subring ℂ) (L₁ L₂ : ComplexLattice) : Prop :=
  ∃ (α β : 𝒪), (α : ℂ) ≠ 0 ∧ (β : ℂ) ≠ 0 ∧
    (α : ℂ) • (L₁.lattice : Set ℂ) = (β : ℂ) • (L₂.lattice : Set ℂ)

/-- Reflexivity of ideal equivalence: every lattice is equivalent to itself (witnessed
by $\alpha = \beta = 1$). -/
theorem IsEquivalent.refl (𝒪 : Subring ℂ) (L : ComplexLattice) : IsEquivalent 𝒪 L L :=
  ⟨1, 1, one_ne_zero, one_ne_zero, rfl⟩

/-- Symmetry of ideal equivalence: if $\alpha L_1 = \beta L_2$, then $\beta L_2 =
\alpha L_1$ (with the roles of $\alpha$ and $\beta$ swapped). -/
theorem IsEquivalent.symm {𝒪 : Subring ℂ} {L₁ L₂ : ComplexLattice}
    (h : IsEquivalent 𝒪 L₁ L₂) : IsEquivalent 𝒪 L₂ L₁ := by
  obtain ⟨α, β, hα, hβ, h⟩ := h
  exact ⟨β, α, hβ, hα, h.symm⟩

/-- Transitivity of ideal equivalence: if $\alpha_1 L_1 = \beta_1 L_2$ and
$\alpha_2 L_2 = \beta_2 L_3$, then $(\alpha_2\alpha_1) L_1 = (\beta_1\beta_2) L_3$. -/
theorem IsEquivalent.trans {𝒪 : Subring ℂ} {L₁ L₂ L₃ : ComplexLattice}
    (h₁₂ : IsEquivalent 𝒪 L₁ L₂) (h₂₃ : IsEquivalent 𝒪 L₂ L₃) :
    IsEquivalent 𝒪 L₁ L₃ := by
  obtain ⟨α₁, β₁, hα₁, hβ₁, h₁⟩ := h₁₂
  obtain ⟨α₂, β₂, hα₂, hβ₂, h₂⟩ := h₂₃
  refine ⟨α₂ * α₁, β₁ * β₂, ?_, ?_, ?_⟩
  · simp only [Subring.coe_mul]; exact mul_ne_zero hα₂ hα₁
  · simp only [Subring.coe_mul]; exact mul_ne_zero hβ₁ hβ₂
  · simp only [Subring.coe_mul, ← smul_smul]
    calc (↑α₂ : ℂ) • (↑α₁ : ℂ) • (L₁.lattice : Set ℂ)
        = (↑α₂ : ℂ) • (↑β₁ : ℂ) • (L₂.lattice : Set ℂ) := by rw [h₁]
      _ = (↑β₁ : ℂ) • (↑α₂ : ℂ) • (L₂.lattice : Set ℂ) := by
          rw [show (↑α₂ : ℂ) • (↑β₁ : ℂ) • (L₂.lattice : Set ℂ) =
                  (↑β₁ : ℂ) • (↑α₂ : ℂ) • (L₂.lattice : Set ℂ) from by
            rw [smul_smul, smul_smul, mul_comm]]
      _ = (↑β₁ : ℂ) • (↑β₂ : ℂ) • (L₃.lattice : Set ℂ) := by rw [h₂]

/-- The relation `IsEquivalent 𝒪` is an equivalence relation on complex lattices. -/
theorem isEquivalent_equivalence (𝒪 : Subring ℂ) :
    Equivalence (IsEquivalent 𝒪) :=
  ⟨IsEquivalent.refl 𝒪, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- Ideal equivalence implies homothety: if $\alpha L_1 = \beta L_2$, then
$L_2 = (\beta^{-1}\alpha) L_1$, so the lattices are homothetic with factor
$\beta^{-1}\alpha$. -/
theorem IsEquivalent.isHomothetic {𝒪 : Subring ℂ} {L₁ L₂ : ComplexLattice}
    (h : IsEquivalent 𝒪 L₁ L₂) : IsHomothetic L₁ L₂ := by
  obtain ⟨α, β, hα, hβ, h⟩ := h
  refine ⟨(β : ℂ)⁻¹ * (α : ℂ), mul_ne_zero (inv_ne_zero hβ) hα, ?_⟩

  have := congr_arg ((β : ℂ)⁻¹ • ·) h
  simp only [smul_smul, inv_mul_cancel₀ hβ, one_smul] at this
  exact this.symm

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

/-- A proper $\mathcal{O}$-ideal is contained in $\mathcal{O}$: every element of the
lattice underlying a proper ideal lies in $\mathcal{O}$. -/
theorem lattice_subset_of_isImagQuadOrder (𝒪 : Subring ℂ)
    (h𝒪 : IsImagQuadOrder 𝒪) (L : ProperIdeal 𝒪)
    (z : ℂ) (hz : z ∈ L.val.toAddSubgroup) : z ∈ 𝒪 :=
  L.property.2 z hz

/-- The first basis vector $\omega_1$ of a proper $\mathcal{O}$-ideal lies in
$\mathcal{O}$. -/
theorem omega1_mem_of_isImagQuadOrder (𝒪 : Subring ℂ) (h𝒪 : IsImagQuadOrder 𝒪)
    (L : ProperIdeal 𝒪) : L.val.ω₁ ∈ 𝒪 :=
  lattice_subset_of_isImagQuadOrder 𝒪 h𝒪 L L.val.ω₁ (ComplexLattice.ω₁_mem L.val)

/-- If $L_2 = c \cdot L_1$ (homothety) with $c \neq 0$ and both are proper
$\mathcal{O}$-ideals, then $c \omega_1(L_1) \in \mathcal{O}$. -/
theorem lambda_omega1_mem_of_isImagQuadOrder (𝒪 : Subring ℂ)
    (h𝒪 : IsImagQuadOrder 𝒪)
    (L₁ L₂ : ProperIdeal 𝒪) (c : ℂ) (hc : c ≠ 0)
    (hL : (L₂.val.lattice : Set ℂ) = c • (L₁.val.lattice : Set ℂ)) :
    c * L₁.val.ω₁ ∈ 𝒪 := by
  have hω₁_in_L₁ : L₁.val.ω₁ ∈ (L₁.val.lattice : Set ℂ) := ComplexLattice.ω₁_mem L₁.val
  have hcω₁_in_L₂ : c * L₁.val.ω₁ ∈ (L₂.val.lattice : Set ℂ) := by
    rw [hL]; exact ⟨L₁.val.ω₁, hω₁_in_L₁, rfl⟩
  exact lattice_subset_of_isImagQuadOrder 𝒪 h𝒪 L₂ (c * L₁.val.ω₁) hcω₁_in_L₂

/-- For proper ideals of an imaginary-quadratic order, homothety implies ideal
equivalence.  Combined with the converse `IsEquivalent.isHomothetic`, this means
the two notions of equivalence coincide for proper ideals. -/
theorem isEquivalent_of_isHomothetic_properIdeal (𝒪 : Subring ℂ)
    (h𝒪 : IsImagQuadOrder 𝒪) (L₁ L₂ : ProperIdeal 𝒪)
    (h : IsHomothetic L₁.val L₂.val) : IsEquivalent 𝒪 L₁.val L₂.val := by
  obtain ⟨c, hc_ne, hL2_eq⟩ := h
  have hω₁_mem : L₁.val.ω₁ ∈ 𝒪 := omega1_mem_of_isImagQuadOrder 𝒪 h𝒪 L₁
  have hcω₁_mem : c * L₁.val.ω₁ ∈ 𝒪 :=
    lambda_omega1_mem_of_isImagQuadOrder 𝒪 h𝒪 L₁ L₂ c hc_ne hL2_eq
  have hω₁_ne : L₁.val.ω₁ ≠ 0 := by
    have h0 := L₁.val.indep.ne_zero (0 : Fin 2)
    simp only [Matrix.cons_val_zero] at h0
    exact h0
  refine ⟨⟨c * L₁.val.ω₁, hcω₁_mem⟩, ⟨L₁.val.ω₁, hω₁_mem⟩, ?_, ?_, ?_⟩
  · exact mul_ne_zero hc_ne hω₁_ne
  · exact hω₁_ne
  · show (c * L₁.val.ω₁) • (L₁.val.lattice : Set ℂ) =
         L₁.val.ω₁ • (L₂.val.lattice : Set ℂ)
    rw [hL2_eq, smul_smul]
    congr 1
    ring

/-- For proper ideals of an order in an imaginary quadratic field, ideal equivalence
and homothety are equivalent notions. -/
theorem isEquivalent_iff_isHomothetic_properIdeal (𝒪 : Subring ℂ)
    (h𝒪 : IsImagQuadOrder 𝒪) (L₁ L₂ : ProperIdeal 𝒪) :
    IsEquivalent 𝒪 L₁.val L₂.val ↔ IsHomothetic L₁.val L₂.val :=
  ⟨IsEquivalent.isHomothetic, isEquivalent_of_isHomothetic_properIdeal 𝒪 h𝒪 L₁ L₂⟩

/-- For an order $\mathcal{O}$ in an imaginary quadratic field, the ideal class group
is in canonical bijection with the set of homothety classes of proper $\mathcal{O}$-ideals. -/
def idealClassGroup_equiv_homothetyClass (𝒪 : Subring ℂ) (h𝒪 : IsImagQuadOrder 𝒪) :
    IdealClassGroup 𝒪 ≃ HomothetyClassCM 𝒪 :=
  Quotient.congr (Equiv.refl _)
    (fun L₁ L₂ => isEquivalent_iff_isHomothetic_properIdeal 𝒪 h𝒪 L₁ L₂)

end

end ComplexLattice

namespace ComplexLattice

noncomputable section

/-- *Classification of endomorphism rings* (Theorem 12.17): the endomorphism ring
of any complex lattice $L$ is either isomorphic to $\mathbb{Z}$ (constructor `isZ`),
or is an order in an imaginary quadratic field (constructor `isOrderInImagQuadField`),
in which case $L$ embeds into that order via $\alpha \mapsto \alpha\omega_1$. -/
inductive EndomorphismRingClassification (L : ComplexLattice) : Prop where
  | isZ (h : ∀ α : ℂ, α ∈ L.endomorphismRing → ∃ n : ℤ, α = (n : ℂ)) :
      EndomorphismRingClassification L
  | isOrderInImagQuadField
      (hIsOrder : IsImagQuadOrder L.endomorphismRing)
      (hLatticeEmbed : ∀ α : ℂ, α ∈ L.endomorphismRing →
        ∃ a' b' : ℤ, ↑a' * L.ω₁ + ↑b' * L.ω₂ = α * L.ω₁) :
      EndomorphismRingClassification L

/-- A complex lattice $L$ *has complex multiplication* iff its endomorphism ring
contains some non-integer element (i.e. is strictly larger than $\mathbb{Z}$). -/
def HasComplexMultiplication (L : ComplexLattice) : Prop :=
  ∃ τ : ℂ, τ ∈ L.endomorphismRing ∧ ∀ n : ℤ, τ ≠ (n : ℂ)

/-- Zero belongs to the *lattice multiplier set* $\{\alpha \in \mathbb{C} : \alpha L_1
\subseteq L_2\}$. -/
theorem latticeMulSet_zero_mem (L₁ L₂ : ComplexLattice) :
    (0 : ℂ) ∈ latticeMulSet L₁ L₂ :=
  zero_mem_latticeMulSet L₁ L₂

/-- The lattice multiplier set is closed under addition: if $\alpha L_1, \beta L_1
\subseteq L_2$, then $(\alpha + \beta) L_1 \subseteq L_2$. -/
theorem latticeMulSet_add_mem (L₁ L₂ : ComplexLattice) {α β : ℂ}
    (hα : α ∈ latticeMulSet L₁ L₂) (hβ : β ∈ latticeMulSet L₁ L₂) :
    α + β ∈ latticeMulSet L₁ L₂ := by
  intro z hz
  rw [add_mul]
  exact L₂.lattice.add_mem (hα z hz) (hβ z hz)

/-- The lattice multiplier set is closed under negation: if $\alpha L_1 \subseteq L_2$,
then $-\alpha \cdot L_1 \subseteq L_2$. -/
theorem latticeMulSet_neg_mem (L₁ L₂ : ComplexLattice) {α : ℂ}
    (hα : α ∈ latticeMulSet L₁ L₂) :
    -α ∈ latticeMulSet L₁ L₂ := by
  intro z hz
  rw [neg_mul]
  exact L₂.lattice.neg_mem (hα z hz)

/-- The lattice multiplier set $\{\alpha : \alpha L_1 \subseteq L_2\}$ packaged as an
additive subgroup of $\mathbb{C}$. -/
def latticeMulAddSubgroup (L₁ L₂ : ComplexLattice) : AddSubgroup ℂ where
  carrier := latticeMulSet L₁ L₂
  zero_mem' := latticeMulSet_zero_mem L₁ L₂
  add_mem' := latticeMulSet_add_mem L₁ L₂
  neg_mem' := latticeMulSet_neg_mem L₁ L₂

/-- A function $f : \mathbb{C} \to \mathbb{C}$ is *even* iff $f(-z) = f(z)$ for all
$z$. -/
def IsEvenFunction (f : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, f (-z) = f z

variable (L : ComplexLattice)

/-- $\wp_{L_2}(\alpha z)$ is a *rational function in $\wp_{L_1}(z)$*: there exist
polynomials $u, v$ with $v \neq 0$ such that $v(\wp_{L_1}(z)) \wp_{L_2}(\alpha z) =
u(\wp_{L_1}(z))$.  Condition (2) of Theorem 16.4. -/
def IsRationalFunctionInWP (L₁ L₂ : ComplexLattice) (α : ℂ) : Prop :=
  ∃ (u v : ℂ[X]), v ≠ 0 ∧
    ∀ z : ℂ, v.eval (L₁.weierstrassP z) * L₂.weierstrassP (α * z) =
      u.eval (L₁.weierstrassP z)

/-- The "isogeny" associated to $\alpha$ exists at the level of $\wp$-functions
and their derivatives: both $\wp_{L_2}(\alpha z)$ and $\wp'_{L_2}(\alpha z)$ can
be expressed rationally in $\wp_{L_1}$ and $\wp'_{L_1}$.  Condition (3) of
Theorem 16.4. -/
def ExistsUniqueIsogenyFromAlpha (L₁ L₂ : ComplexLattice) (α : ℂ) : Prop :=
  ∃ (u v s t : ℂ[X]), v ≠ 0 ∧ t ≠ 0 ∧
    (∀ z : ℂ, v.eval (L₁.weierstrassP z) * L₂.weierstrassP (α * z) =
      u.eval (L₁.weierstrassP z)) ∧
    (∀ z : ℂ, t.eval (L₁.weierstrassP z) * L₂.derivWeierstrassP (α * z) =
      s.eval (L₁.weierstrassP z) * L₁.derivWeierstrassP z)
