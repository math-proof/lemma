/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/SpecialFunctions/Elliptic/Order.lean -/


import sympy.atlas.Analysis.SpecialFunctions.Elliptic.Order
import Lemma.Real.SpecialFunctions.Elliptic.Order

/-!
# Tests for pole sets and elliptic order

Compile-time examples exercising `PeriodPair.poleMultiplicity`,
`PeriodPair.poleSetInFundamentalParallelogram`,
`PeriodPair.ellipticOrderInFundamentalParallelogram`, and `PeriodPair.ellipticOrder`.
It also contains an honest far-away failure witness: a function with pole
multiplicity one at `0` that is nonmeromorphic on every neighborhood of the
remote point `1`, hence not globally meromorphic.
-/


open scoped Topology

namespace PeriodPair

/-- A constant function has canonical elliptic order zero. -/
example (L : PeriodPair) (c : ℂ) :
    L.ellipticOrder (fun _ => c) (IsEllipticFunction.const L c) = 0 := by
  unfold ellipticOrder ellipticOrderInFundamentalParallelogram
  exact Finset.sum_eq_zero fun z _ => poleMultiplicity_const c z

/-- A constant function has arbitrary-vertex elliptic order zero. -/
example (L : PeriodPair) (c α : ℂ) :
    L.ellipticOrderInFundamentalParallelogram (fun _ => c) α
        (IsEllipticFunction.const L c) = 0 := by
  unfold ellipticOrderInFundamentalParallelogram
  exact Finset.sum_eq_zero fun z _ => poleMultiplicity_const c z

/-- Canonical and arbitrary-vertex orders agree on constants. -/
example (L : PeriodPair) (c α : ℂ) :
    L.ellipticOrder (fun _ => c) (IsEllipticFunction.const L c)
      = L.ellipticOrderInFundamentalParallelogram (fun _ => c) α
        (IsEllipticFunction.const L c) := by
  have hzero : ∀ (β : ℂ) (hβ : L.IsEllipticFunction (fun _ => c)),
      L.ellipticOrderInFundamentalParallelogram (fun _ => c) β hβ = 0 := by
    intro β hβ
    unfold ellipticOrderInFundamentalParallelogram
    exact Finset.sum_eq_zero fun z _ => poleMultiplicity_const c z
  unfold ellipticOrder
  rw [hzero, hzero]

/-- The genuinely local inverse pole has multiplicity one. The statement and proof
mention no global meromorphicity hypothesis: only the local order at `a` is used,
so the value cannot depend on the behavior of the function far from `a`. -/
example (a : ℂ) : poleMultiplicity (fun z : ℂ => (z - a)⁻¹) a = 1 :=
  mult_inv_sub_self a

/-- Locality under far-away modification: changing the function value at a point
`b ≠ a` does not affect the multiplicity at `a`, since the two functions agree on a
punctured neighborhood of `a`. -/
example (a b : ℂ) (hab : a ≠ b) :
    poleMultiplicity (fun z : ℂ => if z = b then (0 : ℂ) else (z - a)⁻¹) a
      = 1 := by
  have heq : (fun z : ℂ => if z = b then (0 : ℂ) else (z - a)⁻¹)
      =ᶠ[𝓝[≠] a] (fun z : ℂ => (z - a)⁻¹) := by
    have hb : {b}ᶜ ∈ 𝓝[≠] a :=
      mem_nhdsWithin_of_mem_nhds ((compl_singleton_mem_nhds_iff).mpr hab)
    filter_upwards [self_mem_nhdsWithin, hb] with z _ hzb
    rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hzb
    rw [ite_eq_right hzb]
  have hcongr : meromorphicOrderAt
      (fun z : ℂ => if z = b then (0 : ℂ) else (z - a)⁻¹) a
      = meromorphicOrderAt (fun z : ℂ => (z - a)⁻¹) a :=
    meromorphicOrderAt_congr heq
  unfold poleMultiplicity
  rw [hcongr, order_inv_sub_self a]
  rfl

open Classical in
/-- A function with a genuine pole at `0` but no global meromorphicity: it agrees
with the inverse pole `z ↦ (z - 0)⁻¹` away from a small ball around the remote
point `1`, and equals complex conjugation on that ball. Unlike a single-point
value change (which preserves `MeromorphicAt` by punctured-locality, see above),
conjugation is nonmeromorphic on every neighborhood of `1`. -/
private noncomputable def poleWithConjBranch : ℂ → ℂ := fun z =>
  if z ∈ Metric.ball (1 : ℂ) (1 / 2 : ℝ) then (starRingEnd ℂ) z else (z - 0)⁻¹

/-- The test function has pole multiplicity one at `0`, by transport of the order
along the local equality above. Only the behavior near `0` is used. -/
example : poleMultiplicity poleWithConjBranch 0 = 1 := by
  have hne : poleWithConjBranch =ᶠ[𝓝[≠] (0 : ℂ)] (fun z : ℂ => (z - 0)⁻¹) :=
    poleWithConjBranch_eq_near_zero.filter_mono nhdsWithin_le_nhds
  have hcongr : meromorphicOrderAt poleWithConjBranch 0
      = meromorphicOrderAt (fun z : ℂ => (z - 0)⁻¹) 0 :=
    meromorphicOrderAt_congr hne
  unfold poleMultiplicity
  rw [hcongr, order_inv_sub_self 0]
  rfl

/-- Pointwise failure at the remote point. -/
example : ¬ MeromorphicAt poleWithConjBranch 1 :=
  poleWithConjBranch_not_meromorphicAt

/-- Hence the test function is not globally meromorphic. -/
example : ¬ Meromorphic poleWithConjBranch :=
  fun h => poleWithConjBranch_not_meromorphicAt (h 1)

/-- The Weierstrass function is elliptic, using the public Mathlib API. -/
example (L : PeriodPair) : L.IsEllipticFunction L.weierstrassP :=
  ⟨L.meromorphic_weierstrassP, L.periodic_weierstrassP⟩

/-- The Weierstrass function has a double pole at the origin, by the public order
computation `PeriodPair.order_weierstrassP`. -/
example (L : PeriodPair) : poleMultiplicity L.weierstrassP 0 = 2 := by
  have horder : meromorphicOrderAt L.weierstrassP 0 = -2 :=
    L.order_weierstrassP 0 (Submodule.zero_mem _)
  unfold poleMultiplicity
  rw [horder]
  rfl

/-- The origin lies in the pole set of the Weierstrass function at vertex `0`. -/
example (L : PeriodPair) :
    0 ∈ L.poleSetInFundamentalParallelogram L.weierstrassP 0 := by
  have h2 : poleMultiplicity L.weierstrassP 0 = 2 := by
    have horder : meromorphicOrderAt L.weierstrassP 0 = -2 :=
      L.order_weierstrassP 0 (Submodule.zero_mem _)
    unfold poleMultiplicity
    rw [horder]
    rfl
  rw [mem_poleSetInFundamentalParallelogram_iff]
  refine ⟨?_, by rw [h2]; decide⟩
  rw [fundamentalParallelogram_zero, ZSpan.mem_fundamentalDomain]
  intro i
  simp only [map_zero]
  exact Set.mem_Ico.mpr ⟨le_rfl, zero_lt_one⟩

/-- The vertex belongs to its own fundamental parallelogram (half-open convention:
`0 ≤ tᵢ` includes the lower boundary). -/
example (L : PeriodPair) (α : ℂ) : α ∈ L.fundamentalParallelogram α := by
  rw [mem_fundamentalParallelogram_iff]
  exact ⟨0, 0, le_rfl, one_pos, le_rfl, one_pos, by simp⟩

/-- The period translate `α + ω₁` lies outside the parallelogram (half-open
convention: `tᵢ < 1` excludes the upper boundary). -/
example (L : PeriodPair) (α : ℂ) :
    α + L.ω₁ ∉ L.fundamentalParallelogram α := by
  rw [mem_fundamentalParallelogram_iff]
  rintro ⟨t₁, t₂, _, h1, _, _, h⟩
  have hω : L.ω₁ = t₁ • L.ω₁ + t₂ • L.ω₂ := by
    have hcancel : α + L.ω₁ = α + (t₁ • L.ω₁ + t₂ • L.ω₂) := by
      calc α + L.ω₁ = α + t₁ • L.ω₁ + t₂ • L.ω₂ := h
        _ = α + (t₁ • L.ω₁ + t₂ • L.ω₂) := add_assoc _ _ _
    exact add_left_cancel_iff.mp hcancel
  have hr := congrArg (fun w => L.basis.repr w 0) hω
  rw [basis_repr_omega] at hr
  have hLHS : L.basis.repr L.ω₁ 0 = 1 := by
    have hrepr := L.basis_repr_omega 1 0 0
    simpa using hrepr
  rw [hLHS] at hr
  have ht1 : t₁ = 1 := by simpa using hr.symm
  linarith

/-- The transparent bridge between canonical and arbitrary-vertex order. -/
example (L : PeriodPair) {f : ℂ → ℂ} (hf : L.IsEllipticFunction f) :
    L.ellipticOrder f hf = L.ellipticOrderInFundamentalParallelogram f 0 hf :=
  ellipticOrder_eq_orderInFundamentalParallelogram_zero L hf

end PeriodPair
