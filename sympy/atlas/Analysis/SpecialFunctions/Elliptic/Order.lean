/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Elliptic/Order.lean -/

import Mathlib.Analysis.Meromorphic.Divisor
import sympy.atlas.Analysis.SpecialFunctions.Elliptic.Function
import sympy.atlas.Analysis.SpecialFunctions.Elliptic.FundamentalParallelogram
/-!
# Pole sets and elliptic order of meromorphic elliptic functions

For an elliptic function `f` relative to a period pair `L`, this module provides:

* `PeriodPair.poleMultiplicity`, the pointwise pole multiplicity, defined locally from
  `meromorphicOrderAt f z` as the negation (truncated to `ℕ`) of the order. No global
  meromorphicity hypothesis is built into the definition: at points where `f` is not
  even locally meromorphic, the order takes the junk value `0`, so the multiplicity
  is `0` there for an explicitly local reason.
* `PeriodPair.poleSetInFundamentalParallelogram`, the set of poles of `f` lying in
  the fundamental parallelogram with vertex `α`. The parallelogram uses the half-open
  convention `0 ≤ tᵢ < 1` (see `PeriodPair.mem_fundamentalParallelogram_iff`), so the
  vertex `α` belongs to it while the translates `α + ω₁`, `α + ω₂`, `α + ω₁ + ω₂`
  do not.
* `PeriodPair.ellipticOrderInFundamentalParallelogram`, the sum of the pole
  multiplicities over that set, for an arbitrary vertex `α`.
* `PeriodPair.ellipticOrder`, the canonical order at vertex `0`, with an unfolding
  bridge to the arbitrary-vertex count. No independence of the vertex is claimed.
-/

namespace PeriodPair

/-- Pointwise pole multiplicity of `f` at `z`, defined locally from
`meromorphicOrderAt f z`.

The multiplicity is the negation of the order, truncated to `ℕ`: a pole of order
`-n` contributes `n`, while zeros, nonzero values, and points where `f` is not
locally meromorphic (junk order `0`) contribute `0`. Since only the local order is
used, the value at `z` never depends on the behavior of `f` far away from `z`.
-/
noncomputable def poleMultiplicity (f : ℂ → ℂ) (z : ℂ) : ℕ :=
  (-(meromorphicOrderAt f z).untop₀).toNat

/-- The multiplicity vanishes where `f` is not locally meromorphic (junk order `0`).
This is an explicitly local statement: no global hypothesis on `f` is used. -/
theorem poleMultiplicity_eq_zero_of_not_meromorphicAt {f : ℂ → ℂ} {z : ℂ}
    (h : ¬MeromorphicAt f z) : poleMultiplicity f z = 0 := by
  rw [poleMultiplicity, meromorphicOrderAt_of_not_meromorphicAt h]
  rfl

/-- The multiplicity vanishes at points of nonnegative order. -/
theorem poleMultiplicity_eq_zero_of_nonneg {f : ℂ → ℂ} {z : ℂ}
    (h : 0 ≤ meromorphicOrderAt f z) : poleMultiplicity f z = 0 := by
  unfold poleMultiplicity
  cases h' : meromorphicOrderAt f z with
  | top => simp
  | coe n =>
    rw [WithTop.untop₀_coe]
    exact Int.toNat_eq_zero.mpr (neg_nonpos.mpr (by exact_mod_cast h' ▸ h))

/-- The multiplicity is nonzero if and only if the order is negative, that is, if
and only if `f` has a genuine pole at `z`. This holds unconditionally: where `f` is
not locally meromorphic, both sides are false for an explicitly local reason. -/
theorem poleMultiplicity_ne_zero_iff {f : ℂ → ℂ} {z : ℂ} :
    poleMultiplicity f z ≠ 0 ↔ meromorphicOrderAt f z < 0 := by
  constructor
  · intro hne
    by_contra hge
    push Not at hge
    exact hne (poleMultiplicity_eq_zero_of_nonneg hge)
  · intro hlt hcon
    unfold poleMultiplicity at hcon
    rw [Int.toNat_eq_zero] at hcon
    have hle : (0 : ℤ) ≤ (meromorphicOrderAt f z).untop₀ := neg_nonpos.mp hcon
    have htop : meromorphicOrderAt f z ≠ ⊤ := ne_top_of_lt hlt
    have hcoe : ((meromorphicOrderAt f z).untop₀ : WithTop ℤ) =
        meromorphicOrderAt f z :=
      WithTop.coe_untop₀_of_ne_top htop
    have hle' : (0 : WithTop ℤ) ≤ meromorphicOrderAt f z :=
      hcoe ▸ (by exact_mod_cast hle)
    exact not_lt_of_ge hle' hlt

/-- On a set where `f` is meromorphic, the multiplicity is the negated divisor value.
This is the explicit-domain counterpart of `poleMultiplicity`: unlike
`MeromorphicOn.divisor`, the definition of `poleMultiplicity` itself takes no domain
argument, so no global meromorphicity is hidden in it. -/
theorem poleMultiplicity_eq_neg_divisor {f : ℂ → ℂ} {U : Set ℂ} {z : ℂ}
    (hf : MeromorphicOn f U) (hz : z ∈ U) :
    poleMultiplicity f z = (-(MeromorphicOn.divisor f U z)).toNat := by
  rw [hf.divisor_apply hz]
  rfl

/-- The set of poles of `f` in the fundamental parallelogram with vertex `α`: the
points of the parallelogram where the pointwise multiplicity is nonzero. -/
noncomputable def poleSetInFundamentalParallelogram (L : PeriodPair) (f : ℂ → ℂ)
    (α : ℂ) : Set ℂ :=
  {z ∈ L.fundamentalParallelogram α | poleMultiplicity f z ≠ 0}

/-- Membership in the pole set unfolds to the conjunction of its defining data. -/
theorem mem_poleSetInFundamentalParallelogram_iff {L : PeriodPair} {f : ℂ → ℂ}
    {α z : ℂ} :
    z ∈ L.poleSetInFundamentalParallelogram f α ↔
      z ∈ L.fundamentalParallelogram α ∧ poleMultiplicity f z ≠ 0 :=
  Iff.rfl

/-- The fundamental parallelogram is bounded. The proof covers it by the continuous
image of a compact cube, rather than by an explicit norm estimate. -/
theorem isBounded_fundamentalParallelogram (L : PeriodPair) (α : ℂ) :
    Bornology.IsBounded (L.fundamentalParallelogram α) := by
  have hsub : L.fundamentalParallelogram α ⊆
      (fun p : ℝ × ℝ => α + p.1 • L.ω₁ + p.2 • L.ω₂) ''
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) := by
    intro z hz
    rw [mem_fundamentalParallelogram_iff] at hz
    obtain ⟨t₁, t₂, h1, h2, h3, h4, rfl⟩ := hz
    exact ⟨(t₁, t₂),
      ⟨Set.mem_Icc.mpr ⟨h1, le_of_lt h2⟩, Set.mem_Icc.mpr ⟨h3, le_of_lt h4⟩⟩,
      rfl⟩
  have hcont : Continuous (fun p : ℝ × ℝ => α + p.1 • L.ω₁ + p.2 • L.ω₂) := by
    fun_prop
  exact (isCompact_Icc.prod isCompact_Icc |>.image hcont).isBounded.subset hsub

/-- The pole set of an elliptic function in a fundamental parallelogram is finite.
The proof restricts the divisor to a closed ball covering the parallelogram and uses
finiteness of divisor support there. -/
theorem poleSetInFundamentalParallelogram_finite (L : PeriodPair) {f : ℂ → ℂ}
    (hf : L.IsEllipticFunction f) (α : ℂ) :
    (L.poleSetInFundamentalParallelogram f α).Finite := by
  obtain ⟨R, hR⟩ := (L.isBounded_fundamentalParallelogram α).subset_closedBall 0
  have hU : MeromorphicOn f (Metric.closedBall 0 R) := hf.meromorphic.meromorphicOn
  have hfin := hU.divisor_support_finite_of_subset (isCompact_closedBall 0 R) hR
  refine hfin.subset ?_
  intro z hz
  rw [mem_poleSetInFundamentalParallelogram_iff] at hz
  obtain ⟨hzFP, hmult⟩ := hz
  have hlt : meromorphicOrderAt f z < 0 := poleMultiplicity_ne_zero_iff.mp hmult
  rw [Function.mem_support]
  rw [MeromorphicOn.divisor_apply (hU.mono_set hR) hzFP]
  intro hcon
  rw [WithTop.untop₀_eq_zero] at hcon
  rcases hcon with h0 | htop'
  · rw [h0] at hlt
    exact lt_irrefl _ hlt
  · rw [htop'] at hlt
    exact not_top_lt hlt

/-- The elliptic order of `f` counted in the fundamental parallelogram with arbitrary
vertex `α`: the sum of the pointwise pole multiplicities over the finite pole set.
The sum is taken over the finite set supplied by
`PeriodPair.poleSetInFundamentalParallelogram_finite`, which requires the elliptic
hypothesis `hf`. -/
noncomputable def ellipticOrderInFundamentalParallelogram (L : PeriodPair)
    (f : ℂ → ℂ) (α : ℂ) (hf : L.IsEllipticFunction f) : ℕ :=
  ∑ z ∈ (L.poleSetInFundamentalParallelogram_finite hf α).toFinset,
    poleMultiplicity f z

/-- The canonical elliptic order of `f`: the count in the fundamental parallelogram
with vertex `0`. -/
noncomputable def ellipticOrder (L : PeriodPair) (f : ℂ → ℂ)
    (hf : L.IsEllipticFunction f) : ℕ :=
  L.ellipticOrderInFundamentalParallelogram f 0 hf

/-- Transparent unfolding bridge between the canonical order and the arbitrary-vertex
count at vertex `0`. -/
@[simp]
theorem ellipticOrder_eq_orderInFundamentalParallelogram_zero (L : PeriodPair)
    {f : ℂ → ℂ} (hf : L.IsEllipticFunction f) :
    L.ellipticOrder f hf = L.ellipticOrderInFundamentalParallelogram f 0 hf :=
  rfl

/-- A constant function has pole multiplicity `0` everywhere, including the zero
constant (whose order is `⊤`). -/
theorem poleMultiplicity_const (c z : ℂ) :
    poleMultiplicity (fun _ => c) z = 0 := by
  by_cases hc : c = 0
  · subst hc
    simp [poleMultiplicity, meromorphicOrderAt_const]
  · have h : (0 : WithTop ℤ) ≤ meromorphicOrderAt (fun _ => c) z := by
      simp [meromorphicOrderAt_const, hc]
    exact poleMultiplicity_eq_zero_of_nonneg h

end PeriodPair
