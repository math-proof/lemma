import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.AlgebraicCurve.RegularProlongation
import Lemma.Int.P2MUtil

open AlgebraicCurve IsLocalRing

/--
[AlgebraicCurve_RegularProlongation_exists_mem_nonunit_ord_residue_eq_zero_of_ne_centre](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_RegularProlongation_exists_mem_nonunit_ord_residue_eq_zero_of_ne_centre.lean)
-/

private lemma  ord_nonneg_of_mem
  {K F : Type*}
  [Field K]
  [Field F]
  [Algebra K F]
  (v : Place K F)
  {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rwa [zpow_natCast]
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

private lemma  ord_eq_zero_iff_adicValuation_eq_one
  {K F : Type*}
  [Field K]
  [Field F]
  [Algebra K F]
  (v : Place K F)
  {f : F} (hf : f ≠ 0) :
  v.ord f = 0 ↔ v.adicValuation f = 1 := by
  simp only [Place.ord, neg_eq_zero]
  constructor
  ·
    intro h
    have h2 := WithZero.exp_log (v.adicValuation_ne_zero hf)
    rw [h, WithZero.exp_zero] at h2
    apply h2.symm
  ·
    intro h
    rw [h, WithZero.log_one]

private lemma  mem_maximalIdeal_iff_ord_pos
  {K F : Type*}
  [Field K]
  [Field F]
  [Algebra K F]
  (v : Place K F)
  {x : F} (hx : x ≠ 0) (hmem : x ∈ v.toValuationSubring) :
  (⟨x, hmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring ↔
    0 < v.ord x := by
  have hnonneg : 0 ≤ v.ord x := ord_nonneg_of_mem v hmem
  have hcoe : ((⟨x, hmem⟩ : v.toValuationSubring) : F) = x := rfl
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← v.adicValuation_coe_eq_one_iff,
    hcoe, ← ord_eq_zero_iff_adicValuation_eq_one v hx]
  omega
@[path]
private lemma main
  [Field L] [Field F] [Algebra L F] [Field FSS]
  {A : ValuationSubring L} [Algebra (ResidueField ↥A) FSS]
  {R : RegularProlongation A F FSS}
  {O : Subring F} [IsLocalRing ↥O]
  {Bx : Subring F}
  {nd y : Place (ResidueField ↥A) FSS}
-- given
  (hOR : ∀ f : F, f ∈ O → f ∈ R.integers)
  (hBO : Bx ≤ O)
  (hloc : ∀ f : F, f ∈ O ↔ ∃ g h : F, g ∈ Bx ∧ h ∈ Bx ∧ (∀ hh : h ∈ O, IsUnit (⟨h, hh⟩ : ↥O)) ∧ f * h = g)
  (huniq : ∀ y' : Place (ResidueField ↥A) FSS, (∀ (b : F) (hb : b ∈ Bx), R.residue ⟨b, hOR b (hBO hb)⟩ ∈ y'.toValuationSubring) → (∀ (b : F) (hb : b ∈ Bx), ¬ IsUnit (⟨b, hBO hb⟩ : ↥O) → ∃ hm : R.residue ⟨b, hOR b (hBO hb)⟩ ∈ y'.toValuationSubring, (⟨_, hm⟩ : ↥y'.toValuationSubring) ∈ maximalIdeal ↥y'.toValuationSubring) → y' = nd)
  (hy : ∀ (b : F) (hb : b ∈ Bx), R.residue ⟨b, hOR b (hBO hb)⟩ ∈ y.toValuationSubring)
  (hne : y ≠ nd) :
-- imply
  ∃ (g : F) (hg : g ∈ Bx), ¬ IsUnit (⟨g, hBO hg⟩ : ↥O) ∧
      y.ord (R.residue ⟨g, hOR g (hBO hg)⟩) = 0 ∧ R.residue ⟨g, hOR g (hBO hg)⟩ ≠ 0 := by
-- proof
  by_contra hcon
  push Not at hcon
  apply hne
  refine huniq y hy ?_
  intro b hb hbu
  refine ⟨hy b hb, ?_⟩
  by_cases h0 : R.residue ⟨b, hOR b (hBO hb)⟩ = 0
  ·
    have : (⟨R.residue ⟨b, hOR b (hBO hb)⟩, hy b hb⟩ : ↥y.toValuationSubring) = 0 :=
      Subtype.ext h0
    rw [this]
    exact Ideal.zero_mem _
  ·
    rw [mem_maximalIdeal_iff_ord_pos y h0 (hy b hb)]
    have hnn := ord_nonneg_of_mem y (hy b hb)
    have hne0 : y.ord (R.residue ⟨b, hOR b (hBO hb)⟩) ≠ 0 := fun h => h0 (hcon b hb hbu h)
    omega


-- created on 2026-10-23
