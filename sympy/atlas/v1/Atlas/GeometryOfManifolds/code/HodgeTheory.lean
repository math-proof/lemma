/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds

set_option autoImplicit false

open DifferentialFormSpace


/-- A complex-linear structure on the spaces of differential forms.

Equips each $\Omega^p$ with a scalar multiplication by $\mathbb{C}$ compatible with
the existing $\mathbb{R}$-module structure. -/
structure HasComplexStructure
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF] where
  complexSmul : ∀ {p : ℕ}, ℂ → Ω p → Ω p
  complexSmul_add : ∀ {p : ℕ} (z : ℂ) (ω₁ ω₂ : Ω p),
    complexSmul z (ω₁ + ω₂) = complexSmul z ω₁ + complexSmul z ω₂
  complexSmul_zero : ∀ {p : ℕ} (ω : Ω p), complexSmul 0 ω = 0
  complexSmul_mul : ∀ {p : ℕ} (z w : ℂ) (ω : Ω p),
    complexSmul z (complexSmul w ω) = complexSmul (z * w) ω
  complexSmul_one : ∀ {p : ℕ} (ω : Ω p), complexSmul 1 ω = ω
  complexSmul_real : ∀ {p : ℕ} (r : ℝ) (ω : Ω p),
    complexSmul (r : ℂ) ω = r • ω


/-- The Hodge star operator $*: \Omega^p \to \Omega^p$ (a simplified involution version);
on an oriented Riemannian $n$-manifold it normally maps $\Omega^k \to \Omega^{n-k}$. -/
structure HodgeStar
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF] where
  star : ∀ {p : ℕ}, Ω p → Ω p
  star_star : ∀ {p : ℕ} (α : Ω p), star (star α) = α


/-- The codifferential $d^*: \Omega^k \to \Omega^{k-1}$, the formal $L^2$-adjoint of $d$.

On an oriented Riemannian $n$-manifold, $d^* = (-1)^{n(k-1)+1} * d *$ where $*$ is the
Hodge star and the sign factor satisfies $(\text{sign})^2 = 1$. -/
structure Codifferential
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF] where
  dstar : ∀ {p : ℕ}, Ω (p + 1) → Ω p
  dstar_add : ∀ {p : ℕ} (α β : Ω (p + 1)), dstar (α + β) = dstar α + dstar β
  dstar_smul : ∀ {p : ℕ} (r : ℝ) (α : Ω (p + 1)), dstar (r • α) = r • dstar α
  hodge : HodgeStar (inst := inst)
  sign_factor : ℕ → ℝ
  sign_factor_sq : ∀ k, sign_factor k ^ 2 = 1
  manifold_dim : ℕ
  sign_factor_formula : ∀ k, sign_factor k = (-1 : ℝ) ^ (manifold_dim * (k - 1) + 1)
  star_deg : ∀ {k : ℕ}, k ≤ manifold_dim → Ω k → Ω (manifold_dim - k)
  star_deg_star_deg : ∀ {k : ℕ} (hk : k ≤ manifold_dim)
    (hk' : manifold_dim - k ≤ manifold_dim := by omega) (α : Ω k),
    cast (by congr 1; omega) (star_deg hk' (star_deg hk α)) = α
  dstar_formula : ∀ {p : ℕ} (h : p + 1 ≤ manifold_dim) (ω : Ω (p + 1)),
    dstar ω = sign_factor (p + 1) •
      cast (by congr 1; omega)
        (star_deg (by omega : manifold_dim - (p + 1) + 1 ≤ manifold_dim)
          (inst.d (star_deg h ω)))
  dstar_squared : ∀ {p : ℕ} (ω : Ω (p + 2)), dstar (dstar ω) = 0

/-- The composite $* \circ d \circ *: \Omega^{p+1} \to \Omega^p$ (without the sign factor),
the geometric content of the codifferential. -/
def star_d_star
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (cod : Codifferential (inst := inst))
    {p : ℕ} (h : p + 1 ≤ cod.manifold_dim) (ω : Ω (p + 1)) : Ω p :=

  let star_omega : Ω (cod.manifold_dim - (p + 1)) := cod.star_deg h ω

  let d_star_omega : Ω (cod.manifold_dim - (p + 1) + 1) := inst.d star_omega

  let star_d_star_omega : Ω (cod.manifold_dim - (cod.manifold_dim - (p + 1) + 1)) :=
    cod.star_deg (by omega : cod.manifold_dim - (p + 1) + 1 ≤ cod.manifold_dim) d_star_omega

  cast (by congr 1; omega) star_d_star_omega


/-- The Hodge–de Rham Laplacian $\Delta = dd^* + d^*d: \Omega^k \to \Omega^k$. -/
def laplacian {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (cod : Codifferential (inst := inst)) {p : ℕ} (α : Ω (p + 1)) : Ω (p + 1) :=
  inst.d (cod.dstar α) + cod.dstar (inst.d α)


/-- A form $\alpha$ is *harmonic* if $\Delta \alpha = 0$. -/
def IsHarmonic {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (cod : Codifferential (inst := inst)) {p : ℕ} (α : Ω (p + 1)) : Prop :=
  laplacian cod α = 0

/-- Synonym for `IsHarmonic`: the form $\alpha$ is harmonic. -/
abbrev IsHarmonicForm {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (cod : Codifferential (inst := inst)) {p : ℕ} (α : Ω (p + 1)) : Prop :=
  IsHarmonic cod α

/-- The space $\mathcal{H}^{p+1} = \{\alpha \in \Omega^{p+1} : \Delta \alpha = 0\}$
of harmonic forms of degree $p+1$. -/
def HarmonicForms {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (cod : Codifferential (inst := inst)) (p : ℕ) : Set (Ω (p + 1)) :=
  {α | IsHarmonic cod α}


/-- The $L^2$ inner product on differential forms: a symmetric, positive-definite,
$\mathbb{R}$-bilinear form $\langle \cdot, \cdot \rangle$ on each $\Omega^p$ for which
$d$ and $d^*$ are mutually adjoint, i.e. $\langle d\alpha, \beta\rangle = \langle \alpha, d^*\beta\rangle$. -/
structure L2InnerProduct
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (cod : Codifferential (inst := inst)) where
  inner : ∀ {p : ℕ}, Ω p → Ω p → ℝ
  inner_self_eq_zero : ∀ {p : ℕ} (α : Ω p), inner α α = 0 → α = 0
  inner_self_nonneg : ∀ {p : ℕ} (α : Ω p), 0 ≤ inner α α
  inner_symm : ∀ {p : ℕ} (α β : Ω p), inner α β = inner β α
  adjoint_d : ∀ {p : ℕ} (α : Ω p) (β : Ω (p + 1)),
    inner (inst.d α) β = inner α (cod.dstar β)
  inner_add_left : ∀ {p : ℕ} (α β γ : Ω p),
    inner (α + β) γ = inner α γ + inner β γ
  inner_smul_left : ∀ {p : ℕ} (r : ℝ) (α β : Ω p),
    inner (r • α) β = r * inner α β


/-- Packages the $L^2$ inner product as a Mathlib `Inner ℝ` instance on $\Omega^p$. -/
noncomputable def L2InnerProduct.toInner
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {cod : @Codifferential Ω VF inst}
    (ip : L2InnerProduct cod) (p : ℕ) : Inner ℝ (Ω p) where
  inner := ip.inner


/-- Auxiliary data packaging the formal adjoints $\partial^*$ and $\bar\partial^*$ together
with the decomposition $d^* = \partial^* + \bar\partial^*$. -/
structure DolbeaultLaplacian
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (dol : DolbeaultOps (inst := inst))
    (cod : Codifferential (inst := inst)) where
  del_star : ∀ {p : ℕ}, Ω (p + 1) → Ω p
  delbar_star : ∀ {p : ℕ}, Ω (p + 1) → Ω p
  dstar_decomp : ∀ {p : ℕ} (ω : Ω (p + 1)),
    cod.dstar ω = del_star ω + delbar_star ω
  delbar_star_add : ∀ {p : ℕ} (α β : Ω (p + 1)),
    delbar_star (α + β) = delbar_star α + delbar_star β
  delbar_star_smul : ∀ {p : ℕ} (r : ℝ) (α : Ω (p + 1)),
    delbar_star (r • α) = r • delbar_star α

/-- The $\bar\partial$-Laplacian $\bar\square = \bar\partial\bar\partial^* + \bar\partial^*\bar\partial$
on $(p,q)$-forms. -/
def DolbeaultLaplacian.box_bar
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {dol : DolbeaultOps (inst := inst)}
    {cod : @Codifferential Ω VF inst}
    (dol_lap : DolbeaultLaplacian dol cod)
    {p : ℕ} (α : Ω (p + 1)) : Ω (p + 1) :=
  dol.delbar (dol_lap.delbar_star α) + dol_lap.delbar_star (dol.delbar α)

/-- The $\partial$-Laplacian $\square = \partial\partial^* + \partial^*\partial$. -/
def DolbeaultLaplacian.box
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {dol : DolbeaultOps (inst := inst)}
    {cod : @Codifferential Ω VF inst}
    (dol_lap : DolbeaultLaplacian dol cod)
    {p : ℕ} (α : Ω (p + 1)) : Ω (p + 1) :=
  dol.del (dol_lap.del_star α) + dol_lap.del_star (dol.del α)


/-- Wells' anticommutation identities for the Dolbeault adjoint operators on a Kähler
manifold: $\partial\bar\partial^* + \bar\partial^*\partial = 0$ and
$\bar\partial\partial^* + \partial^*\bar\partial = 0$, plus an expansion identity. -/
structure KahlerWellsIdentities
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [IsCompactSymplectic Ω VF]
    [HasLieBracket Ω VF]
    (S : SymplecticManifold Ω VF)
    (J : AlmostComplexStr (inst := inst))
    (_hK : IsKahler S J)
    {dol : DolbeaultOps (inst := inst)}
    {cod : @Codifferential Ω VF inst}
    (dol_lap : DolbeaultLaplacian dol cod) where
  del_delbar_star_anticommute : ∀ {p : ℕ} (α : Ω (p + 1)),
    dol.del (dol_lap.delbar_star α) + dol_lap.delbar_star (dol.del α) = 0
  delbar_del_star_anticommute : ∀ {p : ℕ} (α : Ω (p + 1)),
    dol.delbar (dol_lap.del_star α) + dol_lap.del_star (dol.delbar α) = 0
  wells_expansion : ∀ {p : ℕ} (α : Ω (p + 1)),
    (dol.del (dol_lap.del_star α) + dol_lap.del_star (dol.del α)) +
    (dol.del (dol_lap.delbar_star α) + dol_lap.delbar_star (dol.del α)) -
    (dol.delbar (dol_lap.del_star α) + dol_lap.del_star (dol.delbar α)) -
    (dol.delbar (dol_lap.delbar_star α) + dol_lap.delbar_star (dol.delbar α)) = 0


/-- Restatement of $2\bar\square = \Delta$ on Kähler manifolds (given as a hypothesis here)
in the form $\bar\square \alpha + \bar\square \alpha = \Delta \alpha$. -/
theorem box_bar_eq_half_laplacian
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [HasLieBracket Ω VF]
    (_S : SymplecticManifold Ω VF)
    (_J : AlmostComplexStr (inst := inst))
    (_hK : IsKahler _S _J)
    {dol : DolbeaultOps (inst := inst)}
    {cod : @Codifferential Ω VF inst}
    (dol_lap : DolbeaultLaplacian dol cod)

    (h_two_box_bar : ∀ {p : ℕ} (α : Ω (p + 1)),
      dol_lap.box_bar α + dol_lap.box_bar α = laplacian cod α
)
    {p : ℕ} (α : Ω (p + 1)) :
    dol_lap.box_bar α + dol_lap.box_bar α = laplacian cod α :=
  h_two_box_bar α


/-- The Hodge bigrading on an almost-complex manifold of complex dimension $n$:
a decomposition $\Omega^k = \bigoplus_{p+q=k} \Omega^{p,q}$ with the Hodge star
acting as $* : \Omega^{p,q} \to \Omega^{n-q, n-p}$. -/
structure HasBigrading
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (J : AlmostComplexStr (inst := inst))
    (n : ℕ) where
  Ω_pq : ℕ → ℕ → Type*
  incl : ∀ (p q : ℕ), Ω_pq p q → Ω (p + q)
  incl_injective : ∀ (p q : ℕ), Function.Injective (incl p q)
  pq_add : ∀ (p q : ℕ), Ω_pq p q → Ω_pq p q → Ω_pq p q
  incl_add : ∀ (p q : ℕ) (α β : Ω_pq p q),
    incl p q (pq_add p q α β) = incl p q α + incl p q β
  pq_zero : ∀ (p q : ℕ), Ω_pq p q
  incl_zero : ∀ (p q : ℕ), incl p q (pq_zero p q) = 0
  incl_cast : ∀ {p₁ q₁ p₂ q₂ : ℕ} (hp : p₁ = p₂) (hq : q₁ = q₂)
      (α : Ω_pq p₁ q₁),
      incl p₂ q₂ (cast (by rw [hp, hq]) α) =
        cast (congrArg Ω (by omega)) (incl p₁ q₁ α)
  star_total : ∀ {k : ℕ}, k ≤ 2 * n → Ω k → Ω (2 * n - k)
  star_abc_decomp : ∀ {p' q' : ℕ} (hp' : p' ≤ n) (hq' : q' ≤ n) (β : Ω_pq p' q'),
    ∃ (a b c : ℕ) (ha : a + c = p') (hb : b + c = q') (habc : a + b + c ≤ n),
      ∃ γ : Ω_pq (a + (n - a - b - c)) (b + (n - a - b - c)),
        incl (a + (n - a - b - c)) (b + (n - a - b - c)) γ =
          cast (congrArg Ω (by omega))
            (star_total (by omega : p' + q' ≤ 2 * n) (incl p' q' β))


/-- Data witnessing that on a Kähler manifold, $\bar\square$ and $\Delta$ preserve the
$(p,q)$ bigrading, and that every harmonic form decomposes into harmonic $(p,q)$-components. -/
structure KahlerBigradedData
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (cod : Codifferential (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    (dol_lap : DolbeaultLaplacian dol cod)
    {J : AlmostComplexStr (inst := inst)}
    {n : ℕ}
    (bg : HasBigrading J n) where
  box_bar_preserves_bidegree :
    ∀ (k p' q' : ℕ) (h : p' + q' = k + 1) (ω : bg.Ω_pq p' q'),
      ∃ ω' : bg.Ω_pq p' q',
        cast (congrArg Ω h) (bg.incl p' q' ω') =
          dol_lap.box_bar (cast (congrArg Ω h) (bg.incl p' q' ω))


  laplacian_preserves_bidegree :
    ∀ (k p' q' : ℕ) (h : p' + q' = k + 1) (ω : bg.Ω_pq p' q'),
      ∃ ω' : bg.Ω_pq p' q',
        cast (congrArg Ω h) (bg.incl p' q' ω') =
          laplacian cod (cast (congrArg Ω h) (bg.incl p' q' ω))

  harmonic_bigrading_decomposition :
    ∀ {k : ℕ} (h_form : Ω (k + 1)) (_h_harmonic : laplacian cod h_form = 0),
      ∃ (component : Fin (k + 2) → Ω (k + 1)),
        (∀ (j : Fin (k + 2)),
          ∃ (ω : bg.Ω_pq j.val (k + 1 - j.val)),
            cast (congrArg Ω (Nat.add_sub_cancel' (Nat.lt_succ_iff.mp j.isLt)))
              (bg.incl j.val (k + 1 - j.val) ω) = component j) ∧
        (∀ j, dol.del (component j) = 0) ∧
        (∀ j, dol.delbar (component j) = 0) ∧
        (∀ j, laplacian cod (component j) = 0) ∧
        h_form = Finset.univ.sum component


/-- On a Kähler manifold, the Laplacian $\Delta$ preserves the Hodge $(p,q)$ bigrading,
deduced from the fact that $\bar\square$ preserves it and $\Delta = 2\bar\square$. -/
theorem laplacian_preserves_bidegree
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [HasLieBracket Ω VF]
    (S : SymplecticManifold Ω VF)
    (J' : AlmostComplexStr (inst := inst))
    (hK : IsKahler S J')
    (cod : Codifferential (inst := inst))
    (dol : DolbeaultOps (inst := inst))
    (dol_lap : DolbeaultLaplacian dol cod)
    {J : AlmostComplexStr (inst := inst)}
    {n : ℕ}
    (bg : HasBigrading J n)

    (h_box_bar_pres : ∀ (k p' q' : ℕ) (h : p' + q' = k + 1) (ω : bg.Ω_pq p' q'),
      ∃ ω' : bg.Ω_pq p' q',
        cast (congrArg Ω h) (bg.incl p' q' ω') =
          dol_lap.box_bar (cast (congrArg Ω h) (bg.incl p' q' ω)))

    (h_two_box_bar : ∀ {p : ℕ} (α : Ω (p + 1)),
      dol_lap.box_bar α + dol_lap.box_bar α = laplacian cod α)
    (k : ℕ) (p' q' : ℕ) (h : p' + q' = k + 1) (ω : bg.Ω_pq p' q') :
    ∃ ω' : bg.Ω_pq p' q',
      cast (congrArg Ω h) (bg.incl p' q' ω') =
        laplacian cod (cast (congrArg Ω h) (bg.incl p' q' ω)) := by

  obtain ⟨ω₁, hω₁⟩ := h_box_bar_pres k p' q' h ω


  have hΔ : laplacian cod (cast (congrArg Ω h) (bg.incl p' q' ω)) =
    dol_lap.box_bar (cast (congrArg Ω h) (bg.incl p' q' ω)) +
    dol_lap.box_bar (cast (congrArg Ω h) (bg.incl p' q' ω)) :=
    (box_bar_eq_half_laplacian S J' hK dol_lap (h_two_box_bar := h_two_box_bar) _).symm

  rw [← hω₁] at hΔ

  refine ⟨bg.pq_add p' q' ω₁ ω₁, ?_⟩

  rw [hΔ]

  have h_add : bg.incl p' q' (bg.pq_add p' q' ω₁ ω₁) =
    bg.incl p' q' ω₁ + bg.incl p' q' ω₁ := bg.incl_add p' q' ω₁ ω₁

  have h_cast_add : ∀ {m n : ℕ} (heq : m = n) (a b : Ω m),
    cast (congrArg Ω heq) (a + b) = cast (congrArg Ω heq) a + cast (congrArg Ω heq) b := by
    intro m n heq; subst heq; intros; rfl
  rw [h_add, h_cast_add h]


/-- The Lefschetz operator $L: \Omega^p \to \Omega^{p+2}$, $\alpha \mapsto \omega \wedge \alpha$
on a symplectic manifold; it commutes with $d$. -/
structure LefschetzOp
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (S : SymplecticManifold Ω VF) where
  L_op : ∀ {p : ℕ}, Ω p → Ω (p + 2)
  d_commutes : ∀ {p : ℕ} (α : Ω p), L_op (inst.d α) = inst.d (L_op α)

/-- The dual Lefschetz operator $\Lambda = L^*: \Omega^{p+2} \to \Omega^p$, the formal
$L^2$-adjoint of $L$. -/
structure DualLefschetz
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF] where
  Λ_op : ∀ {p : ℕ}, Ω (p + 2) → Ω p


/-- An action of the almost-complex structure $J$ on differential forms:
an $\mathbb{R}$-linear involution-up-to-sign $J: \Omega^p \to \Omega^p$ with $J^2 = -\mathrm{id}$. -/
structure JActsOnForms
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (J : AlmostComplexStr (inst := inst)) where
  J_form : ∀ {p : ℕ}, Ω p → Ω p
  J_form_sq : ∀ {p : ℕ} (α : Ω p), J_form (J_form α) = -(α)
  J_form_add : ∀ {p : ℕ} (α β : Ω p), J_form (α + β) = J_form α + J_form β
  J_form_smul : ∀ {p : ℕ} (r : ℝ) (α : Ω p), J_form (r • α) = r • J_form α


/-- The twisted differential $d_C = -J d J: \Omega^p \to \Omega^{p+1}$ associated to
an action of $J$ on forms. -/
noncomputable def d_C_form
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {J : AlmostComplexStr (inst := inst)}
    (Jf : JActsOnForms J)
    {p : ℕ} (α : Ω p) : Ω (p + 1) :=
  -(Jf.J_form (inst.d (Jf.J_form α)))

/-- The codifferential twisted by $J$: $d_C^* = -J d^* J: \Omega^{p+1} \to \Omega^p$. -/
noncomputable def d_C_star_form
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {J : AlmostComplexStr (inst := inst)}
    (Jf : JActsOnForms J)
    (cod : Codifferential (inst := inst))
    {p : ℕ} (α : Ω (p + 1)) : Ω p :=
  -(Jf.J_form (cod.dstar (Jf.J_form α)))


/-- A linear differential operator $L: \Omega^{p+1} \to \Omega^{p+1}$ of order `order`
equipped with its principal symbol $\sigma_k(L)(\xi)$ that is homogeneous of degree
`order` in $\xi$. -/
structure IsDifferentialOperator
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (L : ∀ {p : ℕ}, Ω (p + 1) → Ω (p + 1)) where
  order : ℕ
  symbol : Ω 1 → (∀ {p : ℕ}, Ω (p + 1) → Ω (p + 1))
  L_add : ∀ {p : ℕ} (α β : Ω (p + 1)), L (α + β) = L α + L β
  L_smul : ∀ {p : ℕ} (r : ℝ) (α : Ω (p + 1)), L (r • α) = r • L α
  symbol_homogeneous : ∀ (r : ℝ) (ξ : Ω 1) {p : ℕ} (α : Ω (p + 1)),
    symbol (r • ξ) α = r ^ order • symbol ξ α

/-- A general elliptic operator $L: \Gamma E \to \Gamma F$: a linear operator
whose principal symbol $\sigma(L)(\xi)$ is a bijection for every nonzero $\xi$. -/
structure IsElliptic
    {ΓE : Type*} {ΓF : Type*} {T : Type*}
    [AddCommGroup ΓE] [Module ℝ ΓE]
    [AddCommGroup ΓF] [Module ℝ ΓF]
    [AddCommGroup T] [Module ℝ T]
    (L : ΓE → ΓF) where
  order : ℕ
  symbol : T → (ΓE → ΓF)
  L_add : ∀ (s t : ΓE), L (s + t) = L s + L t
  L_smul : ∀ (r : ℝ) (s : ΓE), L (r • s) = r • L s
  symbol_homogeneous : ∀ (r : ℝ) (ξ : T) (s : ΓE),
    symbol (r • ξ) s = r ^ order • symbol ξ s
  elliptic : ∀ (ξ : T), ξ ≠ 0 → Function.Bijective (symbol ξ)

/-- An elliptic differential endomorphism $L: \Omega^{p+1} \to \Omega^{p+1}$:
a differential operator whose principal symbol is bijective at every nonzero covector. -/
structure IsEllipticEndo
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (L : ∀ {p : ℕ}, Ω (p + 1) → Ω (p + 1))
    extends IsDifferentialOperator (inst := inst) L where
  elliptic : ∀ (ξ : Ω 1), ξ ≠ 0 → ∀ {p : ℕ}, Function.Bijective (symbol ξ (p := p))


/-- A compact manifold of positive dimension `dim`. -/
class IsCompactManifold (Ω : ℕ → Type*) (VF : Type*)
    [DifferentialFormSpace Ω VF] where
  dim : ℕ
  dim_pos : 0 < dim

/-- A compact oriented Riemannian manifold equipped with a codifferential, an $L^2$
inner product, a volume form, Stokes' theorem for exact forms, and the integral formula
$\langle \alpha, \beta\rangle = \int_M \alpha \wedge *\beta$. Also assumes finite
dimensionality of harmonic forms in each degree. -/
class IsCompactOrientedRiemannian (Ω : ℕ → Type*) (VF : Type*)
    [inst : DifferentialFormSpace Ω VF] extends IsCompactManifold Ω VF where
  cod : @Codifferential Ω VF inst
  ip : @L2InnerProduct Ω VF inst cod
  vol : Ω dim
  vol_nonzero : vol ≠ 0
  wedge_star : ∀ (p : ℕ), Ω p → Ω p → Ω dim
  integrate : Ω dim → ℝ
  integrate_linear : ∀ (r : ℝ) (ω₁ ω₂ : Ω dim),
    integrate (r • ω₁ + ω₂) = r * integrate ω₁ + integrate ω₂

  stokes_exact_vanishes : ∀ (p : ℕ) (hp : p + 1 = dim) (η : Ω p),
    integrate (hp ▸ inst.d η) = 0

  inner_eq_integrate_wedge_star : ∀ {p : ℕ} (α β : Ω p),
    ip.inner α β = integrate (wedge_star p α β)
  compact_finite_dim_harmonic : ∀ (k : ℕ),
    ∃ (S : Finset (Ω (k + 1))),
      (∀ s ∈ S, IsHarmonic cod s) ∧
      (∀ (α : Ω (k + 1)), IsHarmonic cod α →
        ∃ (coeffs : Ω (k + 1) → ℝ),
          α = S.sum (fun s => coeffs s • s))


/-- Builds an `IsCompactOrientedRiemannian` structure on a compact symplectic manifold
(of real dimension $2n$) from explicit choices of codifferential, $L^2$ inner product,
volume form, Stokes data, and finite-dimensional harmonic spaces. -/
@[reducible] noncomputable def IsCompactSymplectic.toIsCompactOrientedRiemannian
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [h : IsCompactSymplectic Ω VF]
    (cod : Codifferential (inst := inst))
    (ip : @L2InnerProduct Ω VF inst cod)
    (vol : Ω (2 * h.n))
    (vol_nonzero : vol ≠ 0)
    (wedge_star : ∀ (p : ℕ), Ω p → Ω p → Ω (2 * h.n))
    (integrate : Ω (2 * h.n) → ℝ)
    (integrate_linear : ∀ (r : ℝ) (ω₁ ω₂ : Ω (2 * h.n)),
      integrate (r • ω₁ + ω₂) = r * integrate ω₁ + integrate ω₂)
    (stokes : ∀ (p : ℕ) (hp : p + 1 = 2 * h.n) (η : Ω p),
      integrate (hp ▸ inst.d η) = 0)

    (inner_eq : ∀ {p : ℕ} (α β : Ω p),
      ip.inner α β = integrate (wedge_star p α β))
    (finite_harmonic : ∀ (k : ℕ),
      ∃ (S : Finset (Ω (k + 1))),
        (∀ s ∈ S, IsHarmonic cod s) ∧
        (∀ (α : Ω (k + 1)), IsHarmonic cod α →
          ∃ (coeffs : Ω (k + 1) → ℝ),
            α = S.sum (fun s => coeffs s • s)))
    : IsCompactOrientedRiemannian Ω VF where
  dim := 2 * h.n
  dim_pos := Nat.mul_pos (by norm_num) h.n_pos
  cod := cod
  ip := ip
  vol := vol
  vol_nonzero := vol_nonzero
  wedge_star := wedge_star
  integrate := integrate
  integrate_linear := integrate_linear
  stokes_exact_vanishes := stokes
  inner_eq_integrate_wedge_star := inner_eq
  compact_finite_dim_harmonic := finite_harmonic

/-- Every compact symplectic manifold (of complex dimension $n$) is a compact manifold
of real dimension $2n$. -/
instance (priority := 100) IsCompactSymplectic.toIsCompactManifold
    {Ω : ℕ → Type*} {VF : Type*} [DifferentialFormSpace Ω VF]
    [h : IsCompactSymplectic Ω VF] : IsCompactManifold Ω VF where
  dim := 2 * h.n
  dim_pos := Nat.mul_pos (by norm_num) h.n_pos

/-- Minimal data required for Hodge theory: a codifferential and a compatible $L^2$
inner product on differential forms. -/
class HasHodgeData (Ω : ℕ → Type*) (VF : Type*)
    [inst : DifferentialFormSpace Ω VF] where
  codiff : @Codifferential Ω VF inst
  l2ip   : @L2InnerProduct Ω VF inst codiff

/-- Every compact oriented Riemannian manifold provides Hodge data. -/
noncomputable instance (priority := 100) IsCompactOrientedRiemannian.toHasHodgeData
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [hR : IsCompactOrientedRiemannian Ω VF] : HasHodgeData Ω VF where
  codiff := hR.cod
  l2ip := hR.ip

/-- The Hodge star operator extracted from the codifferential data on a compact oriented
Riemannian manifold. -/
noncomputable def IsCompactOrientedRiemannian.hodgeStar
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [hR : IsCompactOrientedRiemannian Ω VF] : @HodgeStar Ω VF inst :=
  hR.cod.hodge


/-- A predicate giving the Sobolev regularity scale $H^s$ for differential forms. -/
class HasSobolevSpaces (Ω : ℕ → Type*) (VF : Type*) [DifferentialFormSpace Ω VF] where
  IsSobolevRegular : ℕ → ∀ {p : ℕ}, Ω (p + 1) → Prop


/-- A *smoothing operator* $S$: linear and raises Sobolev regularity by at least one
order (and by two when iterated). -/
class IsSmoothing {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [sob : HasSobolevSpaces Ω VF]
    (S : ∀ {p : ℕ}, Ω (p + 1) → Ω (p + 1)) : Prop where
  S_add : ∀ {p : ℕ} (a b : Ω (p + 1)), S (a + b) = S a + S b
  S_smul : ∀ {p : ℕ} (r : ℝ) (a : Ω (p + 1)), S (r • a) = r • S a
  sobolev_improvement : ∀ (s : ℕ) {p : ℕ} (α : Ω (p + 1)),
    sob.IsSobolevRegular s α → sob.IsSobolevRegular (s + 1) (S α)
  compact_improvement : ∀ (s : ℕ) {p : ℕ} (α : Ω (p + 1)),
    sob.IsSobolevRegular s α → sob.IsSobolevRegular (s + 2) (S (S α))


/-- A smoothing operator $S: E \to E$ on an abstract topological vector space, characterized
by raising the Sobolev regularity by one order. -/
structure IsSmoothingOp {E : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousConstSMul ℝ E]
    (S : E →L[ℝ] E)
    (IsSobReg : ℕ → E → Prop) : Prop where
  sobolev_improvement : ∀ (s : ℕ) (α : E),
    IsSobReg s α → IsSobReg (s + 1) (S α)

/-- A parametrix (pseudo-inverse) for a continuous linear operator $L: E \to F$:
a continuous linear $P: F \to E$ with $PL = \mathrm{id} + S_{\text{left}}$ and
$LP = \mathrm{id} + S_{\text{right}}$, where $S_{\text{left}}$ and $S_{\text{right}}$
are smoothing operators. -/
structure HasParametrix
    {E F : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousConstSMul ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [IsTopologicalAddGroup F] [ContinuousConstSMul ℝ F]
    (L : E →L[ℝ] F) where
  P : F →L[ℝ] E
  S_left : E →L[ℝ] E
  S_right : F →L[ℝ] F
  PL_eq : ∀ (α : E), P (L α) = α + S_left α
  LP_eq : ∀ (β : F), L (P β) = β + S_right β
  IsSobRegE : ℕ → E → Prop
  IsSobRegF : ℕ → F → Prop
  isSmoothingOp_S_left : IsSmoothingOp S_left IsSobRegE
  isSmoothingOp_S_right : IsSmoothingOp S_right IsSobRegF

/-- The left smoothing remainder $S_{\text{left}}$ of a parametrix as an $\mathbb{R}$-linear map. -/
def HasParametrix.sLeftLinearMap
    {E F : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousConstSMul ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [IsTopologicalAddGroup F] [ContinuousConstSMul ℝ F]
    {L : E →L[ℝ] F}
    (h : HasParametrix L) : E →ₗ[ℝ] E :=
  h.S_left.toLinearMap

/-- The right smoothing remainder $S_{\text{right}}$ of a parametrix as an $\mathbb{R}$-linear map. -/
def HasParametrix.sRightLinearMap
    {E F : Type*}
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [IsTopologicalAddGroup E] [ContinuousConstSMul ℝ E]
    [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
    [IsTopologicalAddGroup F] [ContinuousConstSMul ℝ F]
    {L : E →L[ℝ] F}
    (h : HasParametrix L) : F →ₗ[ℝ] F :=
  h.S_right.toLinearMap

/-- A parametrix (pseudo-inverse) for an operator $L$ on the differential form spaces:
$PL = \mathrm{id} + S_{\text{left}}$ and $LP = \mathrm{id} + S_{\text{right}}$ with
smoothing remainders. -/
structure HasParametrixDFS
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [HasSobolevSpaces Ω VF]
    (L : ∀ {p : ℕ}, Ω (p + 1) → Ω (p + 1)) where
  P : ∀ {p : ℕ}, Ω (p + 1) → Ω (p + 1)
  S_left : ∀ {p : ℕ}, Ω (p + 1) → Ω (p + 1)
  S_right : ∀ {p : ℕ}, Ω (p + 1) → Ω (p + 1)
  PL_eq : ∀ {p : ℕ} (α : Ω (p + 1)), P (L α) = α + S_left α
  LP_eq : ∀ {p : ℕ} (α : Ω (p + 1)), L (P α) = α + S_right α
  S_left_isSmoothing : IsSmoothing (inst := inst) S_left
  S_right_isSmoothing : IsSmoothing (inst := inst) S_right


/-- A Fredholm operator on differential forms: linear, with a parametrix, having finite
dimensional kernel and cokernel and complemented (closed) range. -/
structure IsFredholm
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (L : ∀ {p : ℕ}, Ω (p + 1) → Ω (p + 1)) where
  P : ∀ {p : ℕ}, Ω (p + 1) → Ω (p + 1)
  S_left : ∀ {p : ℕ}, Ω (p + 1) → Ω (p + 1)
  S_right : ∀ {p : ℕ}, Ω (p + 1) → Ω (p + 1)
  PL_eq : ∀ {p : ℕ} (α : Ω (p + 1)), P (L α) = α + S_left α
  LP_eq : ∀ {p : ℕ} (α : Ω (p + 1)), L (P α) = α + S_right α
  ker_contained : ∀ {p : ℕ} (α : Ω (p + 1)),
    L α = 0 → α + S_left α = P (0 : Ω (p + 1))
  L_add : ∀ {p : ℕ} (α β : Ω (p + 1)), L (α + β) = L α + L β
  L_smul : ∀ {p : ℕ} (r : ℝ) (α : Ω (p + 1)), L (r • α) = r • L α
  kernel_finiteDim : ∀ (p : ℕ),
    FiniteDimensional ℝ ↥(LinearMap.ker
      ({ toFun := (L : Ω (p + 1) → Ω (p + 1))
         map_add' := L_add
         map_smul' := L_smul } : Ω (p + 1) →ₗ[ℝ] Ω (p + 1)))
  cokernel_finiteDim : ∀ (p : ℕ),
    FiniteDimensional ℝ (Ω (p + 1) ⧸ LinearMap.range
      ({ toFun := (L : Ω (p + 1) → Ω (p + 1))
         map_add' := L_add
         map_smul' := L_smul } : Ω (p + 1) →ₗ[ℝ] Ω (p + 1)))
  range_complemented : ∀ (p : ℕ),
    ∃ (C : Submodule ℝ (Ω (p + 1))),
      LinearMap.range
        ({ toFun := (L : Ω (p + 1) → Ω (p + 1))
           map_add' := L_add
           map_smul' := L_smul } : Ω (p + 1) →ₗ[ℝ] Ω (p + 1)) ⊔ C = ⊤ ∧
      LinearMap.range
        ({ toFun := (L : Ω (p + 1) → Ω (p + 1))
           map_add' := L_add
           map_smul' := L_smul } : Ω (p + 1) →ₗ[ℝ] Ω (p + 1)) ⊓ C = ⊥

/-- Packages a Fredholm operator on $\Omega^{p+1}$ as an $\mathbb{R}$-linear map. -/
def IsFredholm.toLinearMap
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {L : ∀ {p : ℕ}, Ω (p + 1) → Ω (p + 1)}
    (hF : IsFredholm (inst := inst) L) (p : ℕ) : Ω (p + 1) →ₗ[ℝ] Ω (p + 1) :=
  { toFun := L
    map_add' := hF.L_add
    map_smul' := hF.L_smul }


/-- A Green-operator decomposition $\mathrm{id} = LG + H$ where $H$ is the harmonic
projection (with $LH = 0$) and $G$ is the Green operator (inverse of $L$ on
$(\ker L)^\perp$). Asserts the orthogonality $\langle H\alpha, LG\alpha\rangle = 0$. -/
structure HasGreenOperatorDecomp
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (L : ∀ {p : ℕ}, Ω (p + 1) → Ω (p + 1)) where
  G : ∀ {p : ℕ}, Ω (p + 1) → Ω (p + 1)
  H : ∀ {p : ℕ}, Ω (p + 1) → Ω (p + 1)
  H_maps_to_ker : ∀ {p : ℕ} (α : Ω (p + 1)), L (H α) = 0
  LG_eq : ∀ {p : ℕ} (α : Ω (p + 1)), L (G α) = α + -(H α)
  GL_eq : ∀ {p : ℕ} (α : Ω (p + 1)), G (L α) = α + -(H α)
  H_idem : ∀ {p : ℕ} (α : Ω (p + 1)), H (H α) = H α
  G_add : ∀ {p : ℕ} (α β : Ω (p + 1)), G (α + β) = G α + G β
  H_add : ∀ {p : ℕ} (α β : Ω (p + 1)), H (α + β) = H α + H β
  G_smul : ∀ {p : ℕ} (r : ℝ) (α : Ω (p + 1)), G (r • α) = r • G α
  H_smul : ∀ {p : ℕ} (r : ℝ) (α : Ω (p + 1)), H (r • α) = r • H α
  G_preserves_regularity : ∀ [sob : HasSobolevSpaces Ω VF] (s : ℕ) {p : ℕ} (α : Ω (p + 1)),
    sob.IsSobolevRegular s α → sob.IsSobolevRegular s (G α)
  H_preserves_regularity : ∀ [sob : HasSobolevSpaces Ω VF] (s : ℕ) {p : ℕ} (α : Ω (p + 1)),
    sob.IsSobolevRegular s α → sob.IsSobolevRegular s (H α)
  orth_decomp : ∀ (cod : Codifferential (inst := inst))
      (ip : @L2InnerProduct Ω VF inst cod)
      {p : ℕ} (α : Ω (p + 1)),
      ip.inner (H α) (L (G α)) = 0
  G_H_eq_zero : ∀ {p : ℕ} (α : Ω (p + 1)), G (H α) = 0
  H_G_eq_zero : ∀ {p : ℕ} (α : Ω (p + 1)), H (G α) = 0


/-- The formal adjoint $\bar\partial^*: \Omega^{p+1} \to \Omega^p$ of the Dolbeault
operator $\bar\partial$. -/
structure DelbarStar
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (dol : DolbeaultOps (inst := inst)) where
  delbar_star : ∀ {p : ℕ}, Ω (p + 1) → Ω p
  delbar_star_add : ∀ {p : ℕ} (α β : Ω (p + 1)),
    delbar_star (α + β) = delbar_star α + delbar_star β
  delbar_star_smul : ∀ {p : ℕ} (r : ℝ) (α : Ω (p + 1)),
    delbar_star (r • α) = r • delbar_star α

/-- The formal adjoint $\partial^*: \Omega^{p+1} \to \Omega^p$ of the Dolbeault
operator $\partial$. -/
structure DelStar
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (dol : DolbeaultOps (inst := inst)) where
  del_star : ∀ {p : ℕ}, Ω (p + 1) → Ω p
  del_star_add : ∀ {p : ℕ} (α β : Ω (p + 1)),
    del_star (α + β) = del_star α + del_star β
  del_star_smul : ∀ {p : ℕ} (r : ℝ) (α : Ω (p + 1)),
    del_star (r • α) = r • del_star α


/-- Typeclass packaging the existence of a Green-operator decomposition for the
Hodge Laplacian. -/
class HasLaplacianGreenDecomp
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (cod : @Codifferential Ω VF inst) where
  green_decomp : Nonempty (@HasGreenOperatorDecomp Ω VF inst (fun α => laplacian cod α))

/-- Two forms $\alpha_1, \alpha_2$ are de Rham cohomologous if they differ by an exact form:
$\alpha_1 - \alpha_2 = d\gamma$ for some $\gamma$. -/
def IsDRCohomologous
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {k : ℕ} (α₁ α₂ : Ω (k + 1)) : Prop :=
  ∃ (γ : Ω k), α₁ - α₂ = inst.d γ


/-- A form $\alpha \in \Omega^{p+q}$ is a pure $(p,q)$-form if it lies in the image of
the inclusion $\Omega^{p,q} \hookrightarrow \Omega^{p+q}$. -/
def HasBigrading.is_pq_form
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {J : AlmostComplexStr (inst := inst)} {n : ℕ}
    (bg : HasBigrading J n) (p q : ℕ) (α : Ω (p + q)) : Prop :=
  ∃ β : bg.Ω_pq p q, bg.incl p q β = α

/-- The Hodge star restricted to the bigraded piece $\Omega^{p,q}$, with image in
$\Omega^{n-q, n-p}$. -/
noncomputable def HasBigrading.star_pq
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {J : AlmostComplexStr (inst := inst)} {n : ℕ}
    (bg : HasBigrading J n)
    {p q : ℕ} (hp : p ≤ n) (hq : q ≤ n)
    (β : bg.Ω_pq p q) : bg.Ω_pq (n - q) (n - p) :=
  (bg.star_bigraded hp hq β).choose


/-- An $L^2$ inner product compatible with the Dolbeault $\bar\partial$ operator:
the formal adjoint $\bar\partial^*$ is the $L^2$-adjoint of $\bar\partial$,
witnessed via Stokes-type integration formulas. -/
structure ComplexL2InnerProduct
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (cod : @Codifferential Ω VF inst)
    (dol : DolbeaultOps (inst := inst))
    (dbs : DelbarStar dol)
    extends L2InnerProduct cod where
  integrate_delbar_top : ∀ {p : ℕ}, Ω p → Ω (p + 1) → ℝ
  stokes_delbar_leibniz : ∀ {p : ℕ} (α : Ω p) (β : Ω (p + 1)),
    inner (dol.delbar α) β = (-1 : ℝ)^(p + 1) • integrate_delbar_top α β
  h_delbar_star_sign : ∀ {p : ℕ} (α : Ω p) (β : Ω (p + 1)),
    (-1 : ℝ)^(p + 1) • integrate_delbar_top α β = inner α (dbs.delbar_star β)


/-- The $\partial$-counterpart of `ComplexL2InnerProduct`: an $L^2$ inner product
compatible with the Dolbeault $\partial$ operator and its formal adjoint $\partial^*$. -/
structure ComplexL2InnerProductDel
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (cod : @Codifferential Ω VF inst)
    (dol : DolbeaultOps (inst := inst))
    (ds : DelStar dol)
    extends L2InnerProduct cod where
  integrate_del_top : ∀ {p : ℕ}, Ω p → Ω (p + 1) → ℝ
  stokes_del_leibniz : ∀ {p : ℕ} (α : Ω p) (β : Ω (p + 1)),
    inner (dol.del α) β = (-1 : ℝ)^(p + 1) • integrate_del_top α β
  h_del_star_sign : ∀ {p : ℕ} (α : Ω p) (β : Ω (p + 1)),
    (-1 : ℝ)^(p + 1) • integrate_del_top α β = inner α (ds.del_star β)

/-- The harmonic projection acts as the identity on $\bar\square$-harmonic forms. -/
def JActsOnForms.d_C
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {J : AlmostComplexStr (inst := inst)}
    (Jf : JActsOnForms J)
    {p : ℕ} (α : Ω p) : Ω (p + 1) :=
  -(Jf.J_form (inst.d (Jf.J_form α)))


/-- The twisted Laplacian $\Delta_C = -J \Delta J$ associated to the $J$-action on forms. -/
def JActsOnForms.laplacian_C
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {J : AlmostComplexStr (inst := inst)}
    (Jf : JActsOnForms J)
    (cod : @Codifferential Ω VF inst)
    {p : ℕ} (α : Ω (p + 1)) : Ω (p + 1) :=
  -(Jf.J_form (laplacian cod (Jf.J_form α)))

/-- Compatibility data witnessing that $J$ commutes with each of $\partial, \bar\partial,
\partial^*, \bar\partial^*$ on a Kähler manifold. -/
structure KahlerJDolbeaultComm
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (dol : DolbeaultOps (inst := inst))
    {J : AlmostComplexStr (inst := inst)}
    (Jf : JActsOnForms J)
    (cod : @Codifferential Ω VF inst)
    (dol_lap : DolbeaultLaplacian dol cod) where
  J_commutes_del : ∀ {p : ℕ} (α : Ω p), dol.del (Jf.J_form α) = Jf.J_form (dol.del α)
  J_commutes_delbar : ∀ {p : ℕ} (α : Ω p), dol.delbar (Jf.J_form α) = Jf.J_form (dol.delbar α)
  J_commutes_del_star : ∀ {p : ℕ} (α : Ω (p + 1)),
    dol_lap.del_star (Jf.J_form α) = Jf.J_form (dol_lap.del_star α)
  J_commutes_delbar_star : ∀ {p : ℕ} (α : Ω (p + 1)),
    dol_lap.delbar_star (Jf.J_form α) = Jf.J_form (dol_lap.delbar_star α)


/-- The twisted codifferential $d_C^* = -J d^* J$ as a method on `JActsOnForms`. -/
def JActsOnForms.d_C_star
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {J : AlmostComplexStr (inst := inst)}
    (Jf : JActsOnForms J)
    (cod : @Codifferential Ω VF inst)
    {p : ℕ} (α : Ω (p + 1)) : Ω p :=
  -(Jf.J_form (cod.dstar (Jf.J_form α)))


/-- A form is *smooth via Sobolev* if it lies in every Sobolev space $H^s$:
$\alpha \in C^\infty \iff \alpha \in \bigcap_s H^s$. -/
def IsSmoothViaSobolev
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [sob : HasSobolevSpaces Ω VF]
    {p : ℕ} (α : Ω (p + 1)) : Prop :=
  ∀ s : ℕ, sob.IsSobolevRegular s α

/-- The difference of two smooth-via-Sobolev forms is smooth via Sobolev. -/
