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
import Theorem.v1.Atlas.ArithmeticGeometry.code.RiemannRoch.Part5
open scoped RestrictedProduct

variable {F : Type*} [Field F] {P : Type*} {O : P → ValuationSubring F}


/-- Multiplication by $f$ as a $k$-linear map $\mathcal{L}(A) \to \mathcal{L}(B)$ when
$\operatorname{div}(f) = A - B$. -/
noncomputable def mulUnitLinearMap (A B : CurveDivisor C) (f : Fˣ)
    (hf : principalDivisor f = A - B) :
    riemannRochSpace (F := F) (k := k) A →ₗ[k] riemannRochSpace (F := F) (k := k) B where
  toFun g := ⟨(f : F) * g.1, mul_unit_mem_riemannRochSpace A B f hf g.1 g.2⟩
  map_add' g₁ g₂ := by
    ext; simp [mul_add]
  map_smul' c g := by
    ext
    simp only [SetLike.val_smul, Algebra.smul_def, RingHom.id_apply]

    ring

/-- If $\operatorname{div}(f) = A - B$ then $f \cdot - : \mathcal{L}(A) \cong \mathcal{L}(B)$
is a $k$-linear isomorphism, with inverse given by multiplication by $f^{-1}$. -/
noncomputable def riemannRochSpace_linearEquiv_of_linearlyEquivalent
    (A B : CurveDivisor C) (f : Fˣ)
    (hf : principalDivisor f = A - B) :
    (riemannRochSpace (F := F) (k := k) A) ≃ₗ[k]
      (riemannRochSpace (F := F) (k := k) B) where
  toLinearMap := mulUnitLinearMap A B f hf
  invFun g := ⟨(f⁻¹ : Fˣ) * g.1,
    mul_unit_mem_riemannRochSpace B A f⁻¹
      (by rw [principalDivisor_inv, hf]; abel) g.1 g.2⟩
  left_inv _g := by
    ext
    simp only [mulUnitLinearMap, Submodule.coe_mk]
    exact Units.inv_mul_cancel_left f _
  right_inv _g := by
    ext
    simp only [mulUnitLinearMap, Submodule.coe_mk]
    exact Units.mul_inv_cancel_left f _

/-- The dimension $\ell(D) := \dim_k \mathcal{L}(D)$ of the Riemann-Roch space of a
divisor $D$. -/
noncomputable def divisorDim (D : CurveDivisor C) : ℕ :=
  Module.finrank k (riemannRochSpace (F := F) (k := k) D)

/-- Corollary 19.24 (axiomatised here): for an effective divisor $A$ there exists an
effective $B$ such that for every $n$, $\mathcal{L}(nA + B)$ contains $(n+1) \deg A$
linearly independent elements over $k$. -/
noncomputable def rDivisor (D : CurveDivisor C) : ℤ :=
  degree C D - (divisorDim (F := F) (k := k) D : ℤ)

/-- Axiomatic dimension-counting property used to prove $\dim_F \Omega = 1$ (Theorem 22.14):
for any two nonzero $\omega_1, \omega_2$ in an $F$-module $\Omega$, there exist
finite-dimensional $k$-subspaces $U_1, U_2$ of $F \cdot \omega_i$ whose individual dimensions
grow like $n + \delta_i - g + 1$ but whose union has dimension at most $g - 1 + n$, forcing
non-trivial intersection. -/
def WeilDifferentialSubspaceData (F : Type*) (k : Type*) (Ω : Type*)
    [Field F] [Field k] [Algebra k F]
    [AddCommGroup Ω] [Module F Ω] [Module k Ω] : Prop :=
  ∀ (ω₁ ω₂ : Ω), ω₁ ≠ 0 → ω₂ ≠ 0 →
    ∃ (δ₁ δ₂ : ℤ) (g : ℕ) (n₀ : ℤ), ∀ (n : ℤ), n ≥ n₀ →
      ∃ (U₁ U₂ : Submodule k Ω),
        FiniteDimensional k ↥U₁ ∧ FiniteDimensional k ↥U₂ ∧
        (∀ u ∈ U₁, ∃ f : F, u = f • ω₁) ∧
        (∀ u ∈ U₂, ∃ f : F, u = f • ω₂) ∧
        (Module.finrank k ↥U₁ : ℤ) = n + δ₁ - (g : ℤ) + 1 ∧
        (Module.finrank k ↥U₂ : ℤ) = n + δ₂ - (g : ℤ) + 1 ∧
        (Module.finrank k ↥(U₁ ⊔ U₂) : ℤ) ≤ (g : ℤ) - 1 + n

/-- (Definition 22.4.) The index of speciality $i(D) := g - 1 - r(D) = g - \deg D - 1 + \ell(D)$
measuring how far the Riemann inequality is from equality. -/
def IsCanonicalDivisor (W : CurveDivisor C) : Prop :=
  ∃ (Ω : Type) (_ : Zero Ω) (divΩ : Ω → CurveDivisor C),
    CanonicalDivisors.IsCanonical divΩ W

section DualityIsomorphism

variable {Ω : Type*} [AddCommGroup Ω] [Module F Ω] [Module k Ω] [IsScalarTower k F Ω]

/-- The $k$-subspace $\Omega(D) := \{\omega \in \Omega : \operatorname{div}(\omega) \geq D\}$
of Weil differentials whose divisor dominates $D$. The hypotheses `h_add` and `h_smul` are
the standard valuation-style inequalities relating `divΩ` to the module structure. -/
def differentialSpaceD (divΩ : Ω → CurveDivisor C) (D : CurveDivisor C)
    (h_add : ∀ ω₁ ω₂ : Ω, ω₁ + ω₂ ≠ 0 →
      ∀ P, min ((divΩ ω₁) P) ((divΩ ω₂) P) ≤ (divΩ (ω₁ + ω₂)) P)
    (h_smul : ∀ (c : k) (ω : Ω), c • ω ≠ 0 →
      ∀ P, (divΩ ω) P ≤ (divΩ (c • ω)) P) :
    Submodule k Ω where
  carrier := {ω' | ω' = 0 ∨ ∀ P, D P ≤ (divΩ ω') P}
  zero_mem' := Or.inl rfl
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    by_cases hab : a + b = 0
    · exact Or.inl hab
    · right
      intro P
      obtain (rfl | ha') := ha
      · simp only [zero_add] at hab ⊢
        exact (hb.resolve_left hab) P
      · obtain (rfl | hb') := hb
        · simp only [add_zero] at hab ⊢
          exact ha' P
        · exact le_trans (le_min (ha' P) (hb' P)) (h_add a b hab P)
  smul_mem' := by
    intro c ω hω
    simp only [Set.mem_setOf_eq] at *
    by_cases hcω : c • ω = 0
    · exact Or.inl hcω
    · right
      intro P
      obtain (rfl | hω') := hω
      · exact absurd (smul_zero c) hcω
      · exact le_trans (hω' P) (h_smul c ω hcω P)

/-- (Theorem 22.20.) The duality isomorphism $\mathcal{L}(W - D) \xrightarrow{\sim} \Omega(D)$
sending $f \in \mathcal{L}(W - D)$ to $f \cdot \omega_0$, where $\omega_0$ is a nonzero
Weil differential with $\operatorname{div}(\omega_0) = W$. -/
noncomputable def duality_theorem_iso
    (divΩ : Ω → CurveDivisor C)
    (W : CurveDivisor C) (D : CurveDivisor C)
    (ω₀ : Ω) (_hω₀ : ω₀ ≠ 0)
    (hW_eq : W = divΩ ω₀)
    (h_add : ∀ ω₁ ω₂ : Ω, ω₁ + ω₂ ≠ 0 →
      ∀ P, min ((divΩ ω₁) P) ((divΩ ω₂) P) ≤ (divΩ (ω₁ + ω₂)) P)
    (h_smul : ∀ (c : k) (ω : Ω), c • ω ≠ 0 →
      ∀ P, (divΩ ω) P ≤ (divΩ (c • ω)) P)


    (div_smul_F_eq : ∀ (f : F) (hf : f ≠ 0),
      divΩ (f • ω₀) = principalDivisor (Units.mk0 f hf) + divΩ ω₀)


    (omega_one_dim : ∀ ω' : Ω, ω' ≠ 0 → ∃ (f : F), f ≠ 0 ∧ ω' = f • ω₀)


    (smul_faithful : ∀ (f : F), f • ω₀ = 0 → f = 0) :

    (riemannRochSpace (F := F) (k := k) (W - D)) ≃ₗ[k]
      differentialSpaceD (k := k) divΩ D h_add h_smul := by

  have hfwd : ∀ f ∈ riemannRochSpace (F := F) (k := k) (W - D),
      f • ω₀ ∈ differentialSpaceD (k := k) divΩ D h_add h_smul := by
    intro f hf
    simp only [differentialSpaceD, Submodule.mem_mk, AddSubmonoid.mem_mk]
    obtain (rfl | ⟨hf_ne, hf_eff⟩) := hf
    · left; exact zero_smul F ω₀
    · right
      intro P
      have h_div := div_smul_F_eq f hf_ne
      rw [Finsupp.ext_iff] at h_div
      have h_divP := h_div P
      simp only [Finsupp.coe_add, Pi.add_apply] at h_divP
      rw [h_divP, ← hW_eq]
      have heff_P := hf_eff P
      simp only [Finsupp.coe_add, Pi.add_apply,
        Finsupp.coe_sub, Pi.sub_apply] at heff_P
      linarith

  let φ : riemannRochSpace (F := F) (k := k) (W - D) →ₗ[k]
      differentialSpaceD (k := k) divΩ D h_add h_smul := {
    toFun := fun f => ⟨f.1 • ω₀, hfwd f.1 f.2⟩
    map_add' := fun f g => Subtype.ext (add_smul f.1 g.1 ω₀)
    map_smul' := fun c f => Subtype.ext (by
      show (↑(c • f) : F) • ω₀ = c • (↑f • ω₀)
      simp only [Submodule.coe_smul_of_tower]
      exact smul_assoc c (f : F) ω₀)
  }

  exact LinearEquiv.ofBijective φ ⟨by

    intro a b h
    have heq : (a : F) • ω₀ = (b : F) • ω₀ := congr_arg Subtype.val h
    have hsub : ((a : F) - (b : F)) • ω₀ = 0 := by rw [sub_smul, heq, sub_self]
    exact Subtype.ext (sub_eq_zero.mp (smul_faithful _ hsub)),
   by

    intro ⟨ω', hω'⟩
    simp only [differentialSpaceD, Submodule.mem_mk, AddSubmonoid.mem_mk] at hω'
    obtain (hω'_zero | hω'_div) := hω'
    ·
      subst hω'_zero
      exact ⟨0, Subtype.ext (zero_smul F ω₀)⟩
    ·

      by_cases hω'_ne : ω' = 0
      ·
        subst hω'_ne
        exact ⟨0, Subtype.ext (zero_smul F ω₀)⟩
      ·
        obtain ⟨f, hf_ne, hf_eq⟩ := omega_one_dim ω' hω'_ne

        have hf_mem : f ∈ riemannRochSpace (F := F) (k := k) (W - D) := by
          right; refine ⟨hf_ne, fun P => ?_⟩

          have hD_le := hω'_div P

          have h_div := div_smul_F_eq f hf_ne
          rw [Finsupp.ext_iff] at h_div
          have h_divP := h_div P
          simp only [Finsupp.coe_add, Pi.add_apply] at h_divP
          rw [hf_eq] at hD_le
          rw [h_divP, ← hW_eq] at hD_le


          simp only [Finsupp.coe_add, Pi.add_apply,
            Finsupp.coe_sub, Pi.sub_apply]
          linarith
        refine ⟨⟨f, hf_mem⟩, Subtype.ext ?_⟩
        show f • ω₀ = ω'
        exact hf_eq.symm⟩

end DualityIsomorphism
