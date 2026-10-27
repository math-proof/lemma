import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Mathlib_RingTheory_Valuation_LowerRamificationGroupDepth
open IsLocalRing Polynomial IsDiscreteValuationRing
open IntermediateField


private lemma irreducible_of_addVal_eq_one
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsDiscreteValuationRing R]
  {x : R} (hx : addVal R x = 1) :
  Irreducible x := by
  obtain ⟨π, hπ⟩ := exists_irreducible R
  have hx0 : x ≠ 0 := fun h => by simp [h] at hx
  obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible hx0 hπ
  have hu : addVal R (u : R) = 0 := by
    rw [← le_zero_iff, ← (addVal R).map_one, addVal_le_iff_dvd]; apply u.isUnit.dvd
  rw [addVal_mul, hπ.addVal_pow, hu, zero_add] at hx
  obtain rfl : n = 1 := by exact_mod_cast hx
  rw [pow_one, irreducible_iff_uniformizer, hπ.maximalIdeal_eq,
    Ideal.span_singleton_eq_span_singleton]
  exact ⟨u, mul_comm π u⟩

private lemma eq_top_of_irreducible_mem_of_residue_surjective
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [Algebra A B]
  [Module.Finite A B]
  (hinj : Function.Injective (algebraMap A B))
  (S : Subalgebra A B) {π : B} (hπ : Irreducible π) (hπS : π ∈ S)
  (hres : ∀ b : B, ∃ s ∈ S, b - s ∈ IsLocalRing.maximalIdeal B) :
  S = ⊤ := by
  obtain ⟨πA, hπA⟩ := exists_irreducible A
  set a : B := algebraMap A B πA with ha_def
  have ha0 : a ≠ 0 := fun h => hπA.ne_zero (hinj (h.trans (map_zero _).symm))
  have ha_ne : addVal B a ≠ ⊤ := fun h => ha0 (addVal_eq_top_iff.mp h)
  set n₀ : ℕ := (addVal B a).toNat with hn₀_def
  have hn₀ : (n₀ : ENat) = addVal B a := ENat.natCast_toNat ha_ne
  have hind : ∀ k : ℕ, ∀ b : B, ∃ s ∈ S, b - s ∈ (IsLocalRing.maximalIdeal B) ^ k := by
    intro k
    induction k with
    | zero => exact fun b => ⟨0, S.zero_mem, by simp⟩
    | succ k ih =>
      intro b
      obtain ⟨s, hs, hbs⟩ := ih b
      rw [mem_maximalIdeal_pow_iff_le_addVal, ← hπ.addVal_pow,
        addVal_le_iff_dvd] at hbs
      obtain ⟨c, hc⟩ := hbs
      obtain ⟨s', hs', hcs'⟩ := hres c
      refine ⟨s + π ^ k * s', S.add_mem hs (S.mul_mem (S.pow_mem hπS k) hs'), ?_⟩
      have hsub : b - (s + π ^ k * s') = π ^ k * (c - s') := by
        rw [show b - (s + π ^ k * s') = (b - s) - π ^ k * s' by ring, hc]; ring
      rw [hsub, mem_maximalIdeal_pow_iff_le_addVal, addVal_mul, hπ.addVal_pow,
        Nat.cast_add, Nat.cast_one]
      gcongr
      rwa [show (1 : ENat) = ((1 : ℕ) : ENat) from rfl,
        ← mem_maximalIdeal_pow_iff_le_addVal, pow_one]
  rw [← Algebra.toSubmodule_eq_top, ← IsLocalRing.map_mkQ_eq_top, eq_top_iff]
  rintro y -
  obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective _ y
  obtain ⟨s, hs, hbs⟩ := hind n₀ b
  refine ⟨s, hs, (Submodule.Quotient.eq _).mpr ?_⟩
  rw [Ideal.smul_top_eq_map, hπA.maximalIdeal_eq, Ideal.map_span,
    Set.image_singleton, Submodule.restrictScalars_mem, Ideal.mem_span_singleton,
    ← neg_sub, dvd_neg]
  rwa [mem_maximalIdeal_pow_iff_le_addVal, hn₀, addVal_le_iff_dvd] at hbs

private lemma residue_aeval_eq
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Module.Finite A B]
  (G : A[X]) (x : B) :
  residue B (aeval x G) = aeval (residue B x) (G.map (residue A)) := by
  conv_rhs => rw [aeval_def, eval₂_map]
  rw [aeval_def, Polynomial.hom_eval₂]
  congr 1

private lemma adjoin_residue_surjective_of_adjoin_residue_eq_top
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Module.Finite A B]
  {x : B} (hx : Algebra.adjoin (ResidueField A) {residue B x} = ⊤) :
  ∀ b : B, ∃ s ∈ Algebra.adjoin A {x}, b - s ∈ IsLocalRing.maximalIdeal B := by
  intro b
  have hb : residue B b ∈ (Polynomial.aeval (R := ResidueField A) (residue B x)).range := by
    rw [← Algebra.adjoin_singleton_eq_range_aeval, hx]; apply Algebra.mem_top
  obtain ⟨p, hp⟩ := hb
  obtain ⟨P, hP⟩ := (Polynomial.mem_lifts p).mp
    ((Polynomial.lifts_iff_coeff_lifts p).mpr fun n =>
      residue_surjective (R := A) (p.coeff n))
  have h1 : residue B (aeval x P) = residue B b := by
    rwa [residue_aeval_eq P x, hP]
  refine ⟨aeval x P, Polynomial.aeval_mem_adjoin_singleton A x,
    (Submodule.Quotient.eq _).mp (h1.symm : residue B b = residue B (aeval x P))⟩

private lemma exists_adjoin_singleton_eq_top
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Module.Finite A B]
  (hinj : Function.Injective (algebraMap A B))
  (hsep : Algebra.IsSeparable (ResidueField A) (ResidueField B)) :
  ∃ x : B, Algebra.adjoin A {x} = ⊤ := by
  have : FiniteDimensional (ResidueField A) (ResidueField B) :=
    ResidueField.finite_of_module_finite
  obtain ⟨ᾱ, hᾱ⟩ := Field.exists_primitive_element (ResidueField A) (ResidueField B)
  obtain ⟨x, hx⟩ := residue_surjective (R := B) ᾱ
  have hxtop : Algebra.adjoin (ResidueField A) {residue B x} = ⊤ := by
    rw [hx, ← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsIntegral.isIntegral ᾱ).isAlgebraic, hᾱ]
    rfl
  set g : (ResidueField A)[X] := minpoly (ResidueField A) ᾱ with hg_def
  have hgmon : g.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral ᾱ)
  have hglift : g ∈ Polynomial.lifts (residue A) :=
    (Polynomial.lifts_iff_coeff_lifts g).mpr fun n =>
      residue_surjective (R := A) (g.coeff n)
  obtain ⟨G, hGmap, -, -⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hglift hgmon
  set Φ : B[X] := G.map (algebraMap A B) with hΦ_def
  have haeval : ∀ y : B, aeval y G = Φ.eval y := fun y => by
    rw [hΦ_def, aeval_def, eval_map]
  have haeval' : ∀ y : B, aeval y G.derivative = Φ.derivative.eval y := fun y => by
    rw [hΦ_def, Polynomial.derivative_map, aeval_def, eval_map]
  have hΦx_mem : Φ.eval x ∈ IsLocalRing.maximalIdeal B := by
    rw [← haeval, ← Ideal.Quotient.eq_zero_iff_mem]
    change residue B (aeval x G) = 0
    rw [residue_aeval_eq, hGmap, hx]
    exact minpoly.aeval _ _
  have hgsep : g.Separable := Algebra.IsSeparable.isSeparable (ResidueField A) ᾱ
  have hgroot : aeval ᾱ g = 0 := minpoly.aeval (ResidueField A) ᾱ
  have hΦ'x_unit : IsUnit (Φ.derivative.eval x) := by
    rw [← haeval']
    refine IsLocalRing.notMem_maximalIdeal.mp (fun hmem => ?_)
    refine hgsep.aeval_derivative_ne_zero hgroot ?_
    rw [← hx, ← hGmap, Polynomial.derivative_map, ← residue_aeval_eq]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  have hΦ'x_val : addVal B (Φ.derivative.eval x) = 0 := by
    rw [← le_zero_iff, ← (addVal B).map_one, addVal_le_iff_dvd]; apply hΦ'x_unit.dvd
  have hΦx_adj : ∀ y : B, Φ.eval y ∈ Algebra.adjoin A {y} := fun y => by
    rw [← haeval]; exact aeval_mem_adjoin_singleton A y
  have hΦx1 : (1 : ENat) ≤ addVal B (Φ.eval x) := by
    rwa [show (1 : ENat) = ((1 : ℕ) : ENat) from rfl,
      ← mem_maximalIdeal_pow_iff_le_addVal, pow_one]
  obtain heq | hlt := eq_or_lt_of_le hΦx1
  ·
    exact ⟨x, eq_top_of_irreducible_mem_of_residue_surjective hinj _
      (irreducible_of_addVal_eq_one heq.symm) (hΦx_adj x)
      (adjoin_residue_surjective_of_adjoin_residue_eq_top hxtop)⟩
  ·
    have h2 : (2 : ENat) ≤ addVal B (Φ.eval x) := Order.add_one_le_of_lt hlt
    obtain ⟨π₀, hπ₀⟩ := exists_irreducible B
    set x' : B := x + π₀ with hx'_def
    obtain ⟨k, hk⟩ := Polynomial.binomExpansion Φ x π₀
    have hΦx'1 : addVal B (Φ.eval x') = 1 := by
      have hGu : addVal B (Φ.derivative.eval x * π₀) = 1 := by
        rw [addVal_mul, addVal_uniformizer hπ₀, hΦ'x_val, zero_add]
      have hrest : (2 : ENat) ≤ addVal B (Φ.eval x + k * π₀ ^ 2) := by
        refine le_trans (le_min h2 ?_) ((addVal B).map_add _ _)
        rw [addVal_mul, addVal_pow, addVal_uniformizer hπ₀, nsmul_one]
        apply le_add_self
      have hne : addVal B (Φ.derivative.eval x * π₀) ≠
        addVal B (Φ.eval x + k * π₀ ^ 2) :=
        fun h => absurd (h ▸ hrest) (by rw [hGu]; decide)
      have hΦeval : Φ.eval x' = Φ.derivative.eval x * π₀ + (Φ.eval x + k * π₀ ^ 2) := by
        rw [hx'_def, hk]; ring
      rw [hΦeval,
        (addVal B).map_add_of_distinct_val hne, hGu,
        min_eq_left (le_trans (by decide) hrest)]
    have hx'top : Algebra.adjoin (ResidueField A) {residue B x'} = ⊤ := by
      have hπ₀res : residue B π₀ = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
        (hπ₀.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π₀)
      rwa [hx'_def, map_add, hπ₀res, add_zero]
    exact ⟨x', eq_top_of_irreducible_mem_of_residue_surjective hinj _
      (irreducible_of_addVal_eq_one hΦx'1) (hΦx_adj x')
      (adjoin_residue_surjective_of_adjoin_residue_eq_top hx'top)⟩
/--
[IsDiscreteValuationRing_exists_adjoin_singleton_eq_top_of_isSeparable_residueField](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsDiscreteValuationRing_exists_adjoin_singleton_eq_top_of_isSeparable_residueField.lean)
-/
@[path]
private lemma main
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B] [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
-- given
  (hinj : Function.Injective (algebraMap A B)) :
-- imply
  ∃ x : B, Algebra.adjoin A {x} = ⊤ :=
-- proof
  exists_adjoin_singleton_eq_top hinj inferInstance


-- created on 2026-10-23
