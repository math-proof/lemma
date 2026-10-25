/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/SpecialFunctions/Elliptic/Order.lean -/


import Def.Analysis.SpecialFunctions.Elliptic.Order
import Lemma.Real.SpecialFunctions.Elliptic.Order
open scoped Topology

/-!
# Tests for pole sets and elliptic order

Compile-time examples exercising `PeriodPair.poleMultiplicity`,
`PeriodPair.poleSetInFundamentalParallelogram`,
`PeriodPair.ellipticOrderInFundamentalParallelogram`, and `PeriodPair.ellipticOrder`.
It also contains an honest far-away failure witness: a function with pole
multiplicity one at `0` that is nonmeromorphic on every neighborhood of the
remote point `1`, hence not globally meromorphic.
-/


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

end PeriodPair
