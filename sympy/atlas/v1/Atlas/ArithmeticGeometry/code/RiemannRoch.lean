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
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.EffectiveDivisors
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.EffectiveDivisors
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.CanonicalDivisors
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.CanonicalDivisors

open scoped RestrictedProduct

/-- The adele ring of a function field $F$ with set of places $P$ and valuation subrings
$O_p \subseteq F$: the restricted product $\prod_{p \in P}' F$ of copies of $F$ with
respect to the family $(O_p)$. An element $(\alpha_p)_{p \in P}$ is an adele iff
$\alpha_p \in O_p$ for all but finitely many $p$. -/
def FunctionFieldAdeleRing (F : Type*) [Field F] (P : Type*)
    (O : P → ValuationSubring F) : Type _ :=
  Πʳ _p : P, [(fun _ => F) _p, O _p]

variable {F : Type*} [Field F] {P : Type*} {O : P → ValuationSubring F}

namespace FunctionFieldAdeleRing

/-- The adele ring inherits a commutative ring structure from the restricted product. -/
noncomputable instance instCommRing : CommRing (FunctionFieldAdeleRing F P O) :=
  inferInstanceAs (CommRing (Πʳ _p : P, [(fun _ => F) _p, (O _p : ValuationSubring F)]))

/-- Adeles act as functions $P \to F$ via the underlying restricted product. -/
instance instDFunLike :
    DFunLike (FunctionFieldAdeleRing F P O) P (fun _ => F) :=
  inferInstanceAs <|
    DFunLike (Πʳ _p : P, [(fun _ => F) _p, (O _p : ValuationSubring F)]) P (fun _ => F)

/-- Two adeles are equal if they agree pointwise at every place. -/
@[ext]
lemma ext {α β : FunctionFieldAdeleRing F P O} (h : ∀ p, α p = β p) : α = β :=
  Subtype.ext <| funext h

/-- A subfield $k \subseteq F$ is called a *field of constants* for the family of valuation
subrings $(O_p)$ if every element of $k$ is integral at every place $p$ and each residue
field $O_p / \mathfrak{m}_p$ is finite-dimensional over $k$. -/
class ConstantField (k : Type*) {F : Type*} {P : Type*} [Field k] [Field F] [Algebra k F]
    {O : P → ValuationSubring F} : Prop where
  algebraMap_mem : ∀ (p : P) (c : k), algebraMap k F c ∈ O p
  residueField_finiteDimensional : ∀ (p : P),
    letI : Algebra k ↥(O p) :=
      ((algebraMap k F).codRestrict (O p).toSubring (fun c => algebraMap_mem p c)).toAlgebra
    letI : Algebra k (IsLocalRing.ResidueField ↥(O p)) :=
      (IsLocalRing.residue ↥(O p) |>.comp (algebraMap k ↥(O p))).toAlgebra
    FiniteDimensional k (IsLocalRing.ResidueField ↥(O p))

/-- Axiom: every constant $c \in k$ lies in $O_p$ at every place $p$. -/
variable [ConstantField k (O := O)]

/-- The diagonal embedding $k \hookrightarrow \mathbb{A}_F$ sending a constant $c$ to the
constant adele $(c, c, c, \dots)$. -/
noncomputable def diagonalRingHom : k →+* FunctionFieldAdeleRing F P O where
  toFun c := ⟨fun _ => algebraMap k F c, Filter.Eventually.of_forall
    (fun p => ConstantField.algebraMap_mem (k := k) p c)⟩
  map_one' := ext fun _ => map_one (algebraMap k F)
  map_mul' x y := ext fun _ => map_mul (algebraMap k F) x y
  map_zero' := ext fun _ => map_zero (algebraMap k F)
  map_add' x y := ext fun _ => map_add (algebraMap k F) x y

/-- The $k$-algebra structure on the adele ring induced by the diagonal embedding. -/
noncomputable instance instAlgebra : Algebra k (FunctionFieldAdeleRing F P O) :=
  (diagonalRingHom k).toAlgebra

/-- Pointwise formula for the $k$-action on adeles: $(c \cdot \alpha)_p = c \cdot \alpha_p$. -/
@[simp]
lemma smul_apply (c : k) (α : FunctionFieldAdeleRing F P O) (p : P) :
    (c • α) p = algebraMap k F c * α p := by
  simp only [Algebra.smul_def]; rfl

/-- Assumed: from a family $(O_p)_{p \in P}$ of valuation subrings of $F$ one obtains the
function-field-curve structure on $P$ used elsewhere. -/
class FunctionFieldProperty (F : Type*) (P : Type*) [Field F]
    (O : P → ValuationSubring F) extends FunctionFieldCurve P F

/-- Default instance deriving `FunctionFieldProperty` from a family of valuation subrings. -/
class DiscreteValuationFamily (P : Type*) (F : Type*) (k : Type*)
    [Field k] [Field F] [Algebra k F] where
  ord : P → F → WithTop ℤ
  ord_zero : ∀ p, ord p 0 = ⊤
  uniformizer_exists : ∀ p, ∃ t : F, ord p t = (1 : ℤ)
  ord_add_ge_min : ∀ (p : P) (x y : F),
    ord p (x + y) ≥ min (ord p x) (ord p y)
  ord_algebraMap : ∀ (p : P) (c : k), c ≠ 0 → ord p (algebraMap k F c) = (0 : ℤ)
  ord_mul : ∀ (p : P) (x y : F), ord p (x * y) = ord p x + ord p y

/-- Auxiliary: the underlying order function $\operatorname{ord}_p : F \to \mathbb{Z}_\infty$
used to build the canonical discrete valuation family. -/
variable [DiscreteValuationFamily P F k]

open DiscreteValuationFamily in
/-- The adele subspace $\mathbb{A}_F(D) := \{\alpha \in \mathbb{A}_F :
\operatorname{ord}_p(\alpha_p) \ge -D(p) \text{ for all } p\}$ associated to a
$\mathbb{Z}$-valued divisor $D$. -/
noncomputable def adeleSpace (D : P → ℤ) :
    Submodule k (FunctionFieldAdeleRing F P O) where
  carrier := { α | ∀ p, ord (k := k) p (α p) ≥ ↑(-D p) }
  add_mem' {α β} hα hβ p :=
    le_trans (le_min (hα p) (hβ p)) (ord_add_ge_min (k := k) p (α p) (β p))
  zero_mem' p := by
    simp only [show (0 : FunctionFieldAdeleRing F P O) p = 0 from rfl, ord_zero]
    exact le_top
  smul_mem' c α hα p := by
    simp only [smul_apply]
    by_cases hc : c = 0
    · simp only [hc, map_zero, zero_mul, ord_zero]; exact le_top
    · rw [ord_mul, ord_algebraMap p c hc]; simp; exact hα p

/-- The space of *Weil differentials* on $D$: the annihilator in $\mathbb{A}_F^*$ of the
subspace $\mathbb{A}_F(D) + F$. That is, $k$-linear functionals on $\mathbb{A}_F$ that
vanish on both the adele subspace of $D$ and the principal adeles. -/
end FunctionFieldAdeleRing

/-- The complete data structure for a curve $C$ with function field $F$ and constant
subfield $k$ needed to prove Riemann-Roch: a `CurveWithConstants` together with all
ancillary structure used in the proof. -/
class RiemannRochData (C : Type*) (F : Type*) (k : Type*)
    [Field k] [Field F] [Algebra k F] extends CurveWithConstants C k F


/-- Axiom form: constants $c \in k^\times$ have order zero at every point $P \in C$. -/
theorem RiemannRochData.ord_algebraMap_eq_ax {C : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F] [RiemannRochData C F k]
    (P : C) (c : kˣ) :
    CurveWithOrd.ord P (Units.map (algebraMap k F).toMonoidHom c) = 0 :=
  CurveWithConstants.ord_constant P c

/-- Ultrametric inequality for sums of nonzero elements at a point: when $f + g \ne 0$,
$\operatorname{ord}_P(f + g) \ge \min(\operatorname{ord}_P(f), \operatorname{ord}_P(g))$. -/
theorem RiemannRochData.ord_add_ge_min_field {C : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F] [RiemannRochData C F k]
    (P : C) (f g : Fˣ) (hfg : (f : F) + (g : F) ≠ 0) :
    CurveWithOrd.ord P (Units.mk0 ((f : F) + (g : F)) hfg) ≥
      min (CurveWithOrd.ord P f) (CurveWithOrd.ord P g) :=
  CurveWithOrd.ord_add P f g hfg

/-- The order at $P$ packaged as a multiplicative monoid homomorphism
$F^\times \to \mathbb{Z}$ (written multiplicatively). -/
noncomputable def CurveWithOrd.ordMonoidHom {C : Type*} {F : Type*} [Field F]
    [CurveWithOrd C F] (P : C) : Fˣ →* Multiplicative ℤ where
  toFun f := Multiplicative.ofAdd (CurveWithOrd.ord P f)
  map_one' := by
    have : CurveWithOrd.ord P (1 : Fˣ) = 0 := by
      have h := CurveWithOrd.ord_mul P (1 : Fˣ) 1
      simp at h; linarith
    simp [this]
  map_mul' f g := by
    rw [CurveWithOrd.ord_mul P f g, ofAdd_add]

/-- Alias: constants have order zero at every point. -/
theorem RiemannRochData.ord_algebraMap_eq {C : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F] [RiemannRochData C F k]
    (P : C) (c : kˣ) :
    CurveWithOrd.ord P (Units.map (algebraMap k F).toMonoidHom c) = 0 :=
  RiemannRochData.ord_algebraMap_eq_ax P c

/-- Short alias for `RiemannRochData.ord_algebraMap_eq`: constants have order zero. -/
theorem RiemannRochData.ord_algebraMap {C : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F] [RiemannRochData C F k]
    (P : C) (c : kˣ) :
    CurveWithOrd.ord P (Units.map (algebraMap k F).toMonoidHom c) = 0 :=
  RiemannRochData.ord_algebraMap_eq P c

/-- Axiom alias for the ultrametric inequality at a point of a curve. -/
theorem RiemannRochData.ord_add_ge_min_ax {C : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F] [RiemannRochData C F k]
    (P : C) (f g : Fˣ) (hfg : (f : F) + (g : F) ≠ 0) :
    CurveWithOrd.ord P (Units.mk0 ((f : F) + (g : F)) hfg) ≥
      min (CurveWithOrd.ord P f) (CurveWithOrd.ord P g) :=
  RiemannRochData.ord_add_ge_min_field P f g hfg

/-- Short alias: the ultrametric inequality $\operatorname{ord}_P(f+g) \ge
\min(\operatorname{ord}_P f, \operatorname{ord}_P g)$ for nonzero $f+g$. -/
theorem RiemannRochData.ord_add_ge_min {C : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F] [RiemannRochData C F k]
    (P : C) (f g : Fˣ) (hfg : (f : F) + (g : F) ≠ 0) :
    CurveWithOrd.ord P (Units.mk0 ((f : F) + (g : F)) hfg) ≥
      min (CurveWithOrd.ord P f) (CurveWithOrd.ord P g) :=
  RiemannRochData.ord_add_ge_min_ax P f g hfg

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

/-- Membership in $\mathcal{L}(D)$ unfolded: $f \in \mathcal{L}(D)$ iff $f = 0$ or
$\operatorname{div}(f) + D$ is effective. -/
theorem mem_riemannRochSpace_iff (D : CurveDivisor C) (f : F) :
    f ∈ riemannRochSpace (k := k) D ↔
      f = 0 ∨ ∃ (hf : f ≠ 0),
        (principalDivisor (Units.mk0 f hf) + D).IsEffective :=
  Iff.rfl

/-- Multiplication by a unit $f$ with $\operatorname{div}(f) = A - B$ sends
$\mathcal{L}(A)$ into $\mathcal{L}(B)$. -/
lemma mul_unit_mem_riemannRochSpace (A B : CurveDivisor C) (f : Fˣ)
    (hf : principalDivisor f = A - B)
    (g : F) (hg : g ∈ riemannRochSpace (k := k) A) :
    (f : F) * g ∈ riemannRochSpace (k := k) B := by
  rw [mem_riemannRochSpace_iff] at hg ⊢
  by_cases hg0 : g = 0
  · left; simp [hg0]
  · right
    have hfg_ne : (f : F) * g ≠ 0 := mul_ne_zero f.ne_zero hg0
    refine ⟨hfg_ne, fun P => ?_⟩
    obtain ⟨hg_ne, heff⟩ := hg.resolve_left hg0
    have heffP := heff P
    simp only [Finsupp.coe_add, Pi.add_apply, principalDivisor_apply] at heffP ⊢
    have key : Units.mk0 ((f : F) * g) hfg_ne = f * Units.mk0 g hg_ne := by
      apply Units.ext; simp
    rw [key, ord_mul]
    have hAP : A P = ord P f + B P := by
      have := congr_fun (congr_arg DFunLike.coe hf) P
      simp only [Finsupp.coe_sub, Pi.sub_apply, principalDivisor_apply] at this
      linarith
    linarith

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
