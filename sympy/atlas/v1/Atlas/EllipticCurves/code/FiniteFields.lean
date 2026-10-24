/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFields.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.IntegralDomain
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Data.Nat.Prime.Basic

/-- Notation `𝔽 p` for the finite field with `p` elements, defined as
`ZMod p` (the quotient `ℤ / p ℤ`). Matches Definition 3.2. -/
abbrev 𝔽 (p : ℕ) := ZMod p

/-- Alternative non-`abbrev` synonym `Fp p := ZMod p` for `𝔽 p`. -/
def Fp (p : ℕ) : Type := ZMod p

example (p : ℕ) [Fact (Nat.Prime p)] : Field (𝔽 p) := inferInstance

open Polynomial in
/-- Notation `𝔽q p n` for the finite field with `p^n` elements, defined
as `GaloisField p n` (the splitting field of `X^(p^n) - X` over `𝔽_p`).
Matches Definition 3.4. -/
abbrev 𝔽q (p : ℕ) [Fact p.Prime] (n : ℕ) := GaloisField p n

section Def34

variable (p : ℕ) [Fact p.Prime] (n : ℕ)

open Polynomial

noncomputable example : Field (𝔽q p n) := inferInstance

example : CharP (𝔽q p n) p := inferInstance

/-- `𝔽q p 1` is canonically isomorphic to `𝔽_p = ZMod p` as a `ZMod p`-algebra. -/
noncomputable def 𝔽q_equivZModP : 𝔽q p 1 ≃ₐ[ZMod p] ZMod p :=
  GaloisField.equivZmodP p

end Def34

section Theorem_3_6

variable (p : ℕ) [Fact p.Prime] (n : ℕ)

/-- Theorem 3.6, uniqueness half (data form): a choice of ring isomorphism
between any finite field `K` of cardinality `p^n` and `𝔽q p n`. -/
noncomputable def 𝔽q_ringEquiv_of_card (hn : n ≠ 0)
    (K : Type*) [Field K] [Fintype K] (hK : Fintype.card K = p ^ n) :
    K ≃+* 𝔽q p n := by
  haveI : Fintype (𝔽q p n) := Fintype.ofFinite _
  have hcard : Fintype.card (𝔽q p n) = p ^ n := by
    rw [Fintype.card_eq_nat_card]
    exact GaloisField.card p n hn
  exact FiniteField.ringEquivOfCardEq (hK.trans hcard.symm)

/-- `𝔽 p` is a field whenever `p` is prime. -/
instance Fp_field (p : ℕ) [hp : Fact (Nat.Prime p)] : Field (𝔽 p) := ZMod.instField p

/-- Definition 3.17: `f` is separable iff it has `deg f` distinct roots in
any algebraic closure — encoded here via Mathlib's `Polynomial.Separable`. -/
def IsSeparablePoly (f : k[X]) : Prop := f.Separable

/-- A polynomial is inseparable iff it is not separable. -/
def IsInseparablePoly (f : k[X]) : Prop := ¬f.Separable

open Subgroup in
/-- Theorem 3.12: every finite subgroup of the multiplicative group `kˣ` of a
field is cyclic. -/
theorem finite_mult_subgroup_of_field_isCyclic
    (k : Type*) [Field k] (G : Subgroup kˣ) [Finite G] : IsCyclic G :=
  isCyclic_subgroup_units G

end Theorem_3_12

section Corollary_3_13

/-- Corollary 3.13: the multiplicative group `kˣ` of a finite field is cyclic. -/
theorem finite_field_mult_isCyclic
    (k : Type*) [Field k] [Fintype k] : IsCyclic kˣ := by
  have : IsCyclic (⊤ : Subgroup kˣ) := finite_mult_subgroup_of_field_isCyclic k ⊤
  exact isCyclic_of_surjective Subgroup.topEquiv Subgroup.topEquiv.surjective

/-- Specialization of Corollary 3.13 to `𝔽q p n`: the multiplicative group
`(𝔽q p n)ˣ` is cyclic. -/
noncomputable instance 𝔽q_units_isCyclic (p : ℕ) [Fact p.Prime] (n : ℕ) :
    IsCyclic (𝔽q p n)ˣ := by
  haveI : Fintype (𝔽q p n) := Fintype.ofFinite _
  exact finite_field_mult_isCyclic (𝔽q p n)

end Corollary_3_13

section Definition_3_14

variable (p : ℕ) [Fact p.Prime]

open Polynomial

/-- Definition 3.14: a monic irreducible `f ∈ 𝔽_p[x]` is primitive iff its
adjoined root has order `p^(deg f) - 1` (i.e. generates the multiplicative
group of `𝔽_p[x]/(f)`). -/
def Polynomial.IsPrimitivePolynomial (f : (ZMod p)[X]) : Prop :=
  f.Monic ∧ Irreducible f ∧ orderOf (AdjoinRoot.root f) = p ^ f.natDegree - 1

/-- Theorem 3.9 (data form): for any irreducible `f ∈ 𝔽_p[x]` of positive
degree `n`, the quotient ring `𝔽_p[x]/(f)` is ring-isomorphic to `𝔽_{p^n}`. -/
noncomputable def quotient_irred_ringEquiv_𝔽q
    (f : (ZMod p)[X]) [hf : Fact (Irreducible f)] (hn : f.natDegree ≠ 0) :
    AdjoinRoot f ≃+* 𝔽q p f.natDegree := by


  have hf0 : f ≠ 0 := hf.out.ne_zero
  let pb := AdjoinRoot.powerBasis hf0
  haveI : Fintype (AdjoinRoot f) := Module.fintypeOfFintype pb.basis
  have hcard_adj : Fintype.card (AdjoinRoot f) = p ^ f.natDegree := by
    have := Module.card_fintype pb.basis
    rw [Fintype.card_fin, AdjoinRoot.powerBasis_dim, ZMod.card] at this
    exact this

  haveI : Fintype (𝔽q p f.natDegree) := Fintype.ofFinite _
  have hcard_gf : Fintype.card (𝔽q p f.natDegree) = p ^ f.natDegree := by
    rw [Fintype.card_eq_nat_card]
    exact GaloisField.card p f.natDegree hn
  exact FiniteField.ringEquivOfCardEq (hcard_adj.trans hcard_gf.symm)

/-- The `i`-th Conway coefficient of an order polynomial `f` from
Definition 3.16: take `(-1)^(deg f - i)·coeff_i(f)` and reduce to a
natural number in `[0, p)`. -/
noncomputable def conwayCoeff (f : (ZMod p)[X]) (i : ℕ) : ℕ :=
  ZMod.val ((-1 : ZMod p) ^ (f.natDegree - i) * f.coeff i)

/-- The strict lexicographic order on Conway coefficients used to compare two
order polynomials of the same degree, per Definition 3.16. -/
def conwayLT (f g : (ZMod p)[X]) : Prop :=
  ∃ k : ℕ, k < f.natDegree ∧
    conwayCoeff p f k < conwayCoeff p g k ∧
    ∀ j : ℕ, j < k → conwayCoeff p f j = conwayCoeff p g j

/-- Conway compatibility (Definition 3.16): for every proper divisor `m ∣ n`
and every root `α` of `fam m`, `f(α^(n/m)) = 0` holds in the algebraic
closure of `𝔽_p`. -/
def ConwayCompatible
    (fam : ∀ m : ℕ, 0 < m → (ZMod p)[X]) (n : ℕ) (f : (ZMod p)[X]) : Prop :=
  ∀ m : ℕ, ∀ (hm : 0 < m), m < n → m ∣ n →
    ∀ α : AlgebraicClosure (ZMod p),
      (((fam m hm).map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))).IsRoot α) →
        ((f.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))).IsRoot (α ^ (n / m)))

/-- A family `fam : ∀ n > 0, 𝔽_p[X]` is a Conway polynomial system if it
satisfies the recursive definition (Definition 3.16): the degree-one case is
`X - r` for the least primitive root `r`; each higher polynomial is primitive,
has the right degree, is compatible with smaller members, and is minimal under
the Conway lex order among such primitives. -/
structure IsConwayPolynomialSystem
    (fam : ∀ n : ℕ, 0 < n → (ZMod p)[X]) : Prop where
  degree_one : ∃ (r : ℕ), 0 < r ∧ r < p ∧
    orderOf ((r : ZMod p) : ZMod p) = p - 1 ∧
    (∀ s : ℕ, 0 < s → s < r → orderOf ((s : ZMod p) : ZMod p) ≠ p - 1) ∧
    fam 1 (by omega) = X - C (r : ZMod p)
  isPrimitive : ∀ n : ℕ, ∀ (hn : 0 < n), 1 < n →
    (fam n hn).IsPrimitivePolynomial p
  hasDegree : ∀ n : ℕ, ∀ (hn : 0 < n), 1 < n → (fam n hn).natDegree = n
  compatible : ∀ n : ℕ, ∀ (hn : 0 < n), 1 < n →
    ConwayCompatible p (fun m hm => fam m hm) n (fam n hn)
  isLeast : ∀ n : ℕ, ∀ (hn : 0 < n), 1 < n →
    ∀ g : (ZMod p)[X],
      g.IsPrimitivePolynomial p → g.natDegree = n →
      ConwayCompatible p (fun m hm => fam m hm) n g →
      ¬ conwayLT p g (fam n hn)

/-- Existence of a Conway polynomial system over `𝔽_p` (Definition 3.16). -/
end Definition_3_16

section Theorem_3_15

open Polynomial IntermediateField

/-- Auxiliary lemma for Theorem 3.15: for an integral element `α` of `E/F`,
the order of `AdjoinRoot.root (minpoly F α)` equals `orderOf α`, via the
ring isomorphism between `F[x]/(minpoly α)` and `F(α)`. -/
lemma orderOf_adjoinRoot_root_eq_orderOf (F : Type*) [Field F]
    (E : Type*) [Field E] [Algebra F E]
    (α : E) (hint : IsIntegral F α) :
    orderOf (AdjoinRoot.root (minpoly F α)) = orderOf α := by
  let e := adjoinRootEquivAdjoin F hint
  let incl : ↥(F⟮α⟯) →+* E := (IntermediateField.val (F⟮α⟯)).toRingHom
  let φ : AdjoinRoot (minpoly F α) →+* E := incl.comp e.toRingEquiv.toRingHom
  have hφ_inj : Function.Injective φ := by
    intro x y h; exact e.toRingEquiv.injective (Subtype.val_injective h)
  have hφ_root : φ (AdjoinRoot.root (minpoly F α)) = α := by
    show incl (e (AdjoinRoot.root (minpoly F α))) = α
    rw [adjoinRootEquivAdjoin_apply_root]; rfl
  conv_rhs => rw [← hφ_root]
  exact (orderOf_injective φ.toMonoidHom hφ_inj _).symm

/-- If `g` is a unit of `𝔽_{p^n}` of order `p^n - 1`, then `g` generates the
multiplicative group of `𝔽_{p^n}` and `𝔽_p(g) = 𝔽_{p^n}`. -/
lemma adjoin_top_of_unit_generator (p : ℕ) [hp : Fact p.Prime] (n : ℕ) (hn : 0 < n)
    (g : (GaloisField p n)ˣ) (hg : orderOf g = p ^ n - 1) :
    (ZMod p)⟮(g : GaloisField p n)⟯ = ⊤ := by
  classical
  haveI : Fintype (GaloisField p n) := Fintype.ofFinite _
  set α := (g : GaloisField p n)
  rw [eq_top_iff]; intro x _
  by_cases hx : x = 0
  · rw [hx]; exact (ZMod p)⟮α⟯.zero_mem
  · have hord_u : orderOf g = Fintype.card (GaloisField p n)ˣ := by
      rw [hg, Fintype.card_eq_nat_card, Nat.card_units, GaloisField.card p n hn.ne']
    have hgen : Subgroup.zpowers g = ⊤ := by
      have := @Fintype.card_zpowers (GaloisField p n)ˣ _ _ g
      rw [hord_u] at this; apply Subgroup.eq_top_of_card_eq
      rw [← Fintype.card_eq_nat_card, ← Fintype.card_eq_nat_card]; exact this
    obtain ⟨k, hk⟩ := show Units.mk0 x hx ∈ Subgroup.zpowers g by rw [hgen]; trivial
    have : x = α ^ k := by
      have h := congr_arg Units.val hk
      simp only [Units.val_zpow_eq_zpow_val, Units.val_mk0] at h; exact h.symm
    rw [this]
    exact zpow_mem (mem_adjoin_simple_self (ZMod p) (E := GaloisField p n) α) k

/-- If `g` is a generator of `(𝔽_{p^n})ˣ`, then its minimal polynomial over
`𝔽_p` is a primitive polynomial of degree `n` (cf. Theorem 3.15). -/
lemma generator_minpoly_is_prim (p : ℕ) [hp : Fact p.Prime] (n : ℕ) (hn : 0 < n)
    (g : (GaloisField p n)ˣ) (hg : orderOf g = p ^ n - 1) :
    let f := minpoly (ZMod p) (g : GaloisField p n)
    f.IsPrimitivePolynomial p ∧ f.natDegree = n := by
  classical
  haveI : Fintype (GaloisField p n) := Fintype.ofFinite _
  set α := (g : GaloisField p n); set f := minpoly (ZMod p) α
  have hint : IsIntegral (ZMod p) α := Algebra.IsIntegral.isIntegral α
  have htop := adjoin_top_of_unit_generator p n hn g hg
  have hord_α : orderOf α = p ^ n - 1 := by
    change orderOf ((Units.coeHom _) g) = _
    rw [orderOf_injective (Units.coeHom _) Units.val_injective g, hg]
  have hf_deg : f.natDegree = n := by
    have h1 := adjoin.finrank hint
    have h2 : Module.finrank (ZMod p) ↥(ZMod p)⟮α⟯ = n := by
      rw [htop,
        (IntermediateField.topEquiv (F := ZMod p)
          (E := GaloisField p n)).toLinearEquiv.finrank_eq]
      exact GaloisField.finrank p hn.ne'
    linarith
  refine ⟨⟨minpoly.monic hint, minpoly.irreducible hint, ?_⟩, hf_deg⟩
  rw [hf_deg, orderOf_adjoinRoot_root_eq_orderOf (ZMod p) (GaloisField p n) α hint, hord_α]

/-- The set of primitive polynomials of degree `n` in `𝔽_p[x]` is finite: a
primitive polynomial of degree `n` is determined by its `n` lower coefficients
in `𝔽_p`, of which there are finitely many. -/
instance finite_primitivePolys (p : ℕ) [hp : Fact p.Prime] (n : ℕ) :
    Finite {f : (ZMod p)[X] // f.IsPrimitivePolynomial p ∧ f.natDegree = n} := by
  apply Finite.of_injective
    (fun (⟨f, ⟨hm, _, _⟩, _⟩ :
      {f : (ZMod p)[X] // f.IsPrimitivePolynomial p ∧ f.natDegree = n}) =>
      (fun (i : Fin n) => f.coeff i.val : Fin n → ZMod p))
  intro ⟨f, ⟨hfm, _, _⟩, hfn⟩ ⟨g, ⟨hgm, _, _⟩, hgn⟩ h
  simp only [Subtype.mk.injEq]; ext i
  by_cases hi : i < n
  · exact congr_fun h ⟨i, hi⟩
  · by_cases hi2 : i = n
    · have h1 : f.coeff i = 1 := by rw [hi2, ← hfn]; exact hfm.leadingCoeff
      have h2 : g.coeff i = 1 := by rw [hi2, ← hgn]; exact hgm.leadingCoeff
      rw [h1, h2]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : f.natDegree < i)]
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : g.natDegree < i)]

/-- The map from multiplicative generators of `𝔽_{p^n}` to primitive
polynomials of degree `n`, sending `g` to its minimal polynomial over `𝔽_p`. -/
noncomputable def minpoly_of_generator (p : ℕ) [hp : Fact p.Prime] (n : ℕ) (hn : 0 < n)
    (g : {g : (GaloisField p n)ˣ // orderOf g = p ^ n - 1}) :
    {f : (ZMod p)[X] // f.IsPrimitivePolynomial p ∧ f.natDegree = n} :=
  ⟨minpoly (ZMod p) (g.1 : GaloisField p n),
   generator_minpoly_is_prim p n hn g.1 g.2⟩
