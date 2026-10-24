import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.HexEndpointColumnBoundary
open StatMech StatMech.Universality


/--
[hecb_endpoint_finset_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointColumnBoundary.lean)
-/
@[path]
private lemma hecb_endpoint_finset_bound_eq
  {f : W → ℝ}
  {strip : Finset W → Finset W}
  {lam tau : Finset W → ℝ}
-- given
  (hnn : ∀ w, 0 ≤ f w)
  (hsub : ∀ s, s ⊆ strip s)
  (hlam : ∀ s, 0 ≤ lam s)
  (htau : ∀ s, 0 ≤ tau s)
  (hbdry : ∀ s, hexCl * lam s + hexCt * tau s + ∑ w ∈ strip s, f w = 1) :
-- imply
  ∀ s : Finset W, ∑ w ∈ s, f w ≤ 1 := by
-- proof
  apply StatMech.Universality.hecb_endpoint_finset_bound f hnn strip hsub lam tau hlam htau hbdry

/--
[hecb_hexEndpointColumn_colSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointColumnBoundary.lean)
-/
@[path]
private lemma hecb_hexEndpointColumn_colSum_eq
  {a : ℂ}
  {T : ℕ}
  (hlen strip hsub lam tau hlam htau hbdry)
  {x : ℝ}
-- given
  (h0 : ℤ)
  (mem : List ℤ → Prop) :
-- imply
  (hecb_hexEndpointColumnOfSingleStrip a h0 T mem hlen strip hsub lam tau hlam htau hbdry).colSum x = ∑' w : {ts : List ℤ // mem ts}, x ^ (ofTurns a h0 w.1).endpointNumVertices := by
-- proof
  apply StatMech.Universality.hecb_hexEndpointColumn_colSum a h0 T mem x

/--
[hecb_hexEndpointColumn_critical_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointColumnBoundary.lean)
-/
@[path]
private lemma hecb_hexEndpointColumn_critical_le_one_eq
  {a : ℂ}
  {T : ℕ}
  (hlen strip hsub lam tau hlam htau hbdry)
-- given
  (h0 : ℤ)
  (mem : List ℤ → Prop) :
-- imply
  (hecb_hexEndpointColumnOfSingleStrip a h0 T mem hlen strip hsub lam tau hlam htau hbdry).colSum hexChiE ≤ 1 := by
-- proof
  apply StatMech.Universality.hecb_hexEndpointColumn_critical_le_one a h0 T mem


-- created on 2026-10-23
