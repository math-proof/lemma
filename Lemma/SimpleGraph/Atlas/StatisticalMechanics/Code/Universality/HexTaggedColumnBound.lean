import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexTaggedColumnBound
open StatMech StatMech.Universality


/--
[finiteTagged_sum_le_card_mul_tsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexTaggedColumnBound.lean)
-/
@[path]
private lemma finiteTagged_sum_le_card_mul_tsum_eq
  [Fintype Tag]
  {S : Finset B}
  {encode : B → Tag × W}
  {rawWeight : B → ℝ}
  {columnWeight : W → ℝ}
  {K : ℝ}
-- given
  (hinj : Set.InjOn encode (S : Set B))
  (hK : 0 ≤ K)
  (hcolnn : ∀ w, 0 ≤ columnWeight w)
  (hcolsum : Summable columnWeight)
  (hweight : ∀ b ∈ S, rawWeight b ≤ K * columnWeight (encode b).2) :
-- imply
  ∑ b ∈ S, rawWeight b ≤ K * Fintype.card Tag * ∑' w, columnWeight w := by
-- proof
  apply StatMech.Universality.finiteTagged_sum_le_card_mul_tsum S encode hinj rawWeight columnWeight K hK hcolnn hcolsum hweight

/--
[raw_pow_le_inv_mul_endpoint_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexTaggedColumnBound.lean)
-/
@[path]
private lemma raw_pow_le_inv_mul_endpoint_pow_eq
  {x : ℝ}
  {rawLen endpointLen : ℕ}
-- given
  (hx : 0 < x)
  (hxone : x ≤ 1)
  (hlen : endpointLen = rawLen ∨ endpointLen = rawLen + 1) :
-- imply
  x ^ rawLen ≤ x⁻¹ * x ^ endpointLen := by
-- proof
  apply StatMech.Universality.raw_pow_le_inv_mul_endpoint_pow hx hxone rawLen endpointLen hlen


-- created on 2026-10-23
