import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointWalk.Part3
open StatMech StatMech.Universality StatMech.Universality.HexWalk


/--
[endpointNumVertices_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointWalk.lean)
-/
@[path]
private lemma endpointNumVertices_eq_eq
  {w : HexWalk} :
-- imply
  w.endpointNumVertices = w.turns.length := by
-- proof
  apply StatMech.Universality.HexWalk.endpointNumVertices_eq w

/--
[length_endpointVertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointWalk.lean)
-/
@[path]
private lemma length_endpointVertices_eq
  {w : HexWalk} :
-- imply
  w.endpointVertices.length = w.endpointNumVertices := by
-- proof
  apply StatMech.Universality.HexWalk.length_endpointVertices w

/--
[endpointVerticesAux_append_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointWalk.lean)
-/
@[path]
private lemma endpointVerticesAux_append_one_eq
  {m : ℂ}
  {ts : List ℤ}
  {t : ℤ}
-- given
  (h : ℤ) :
-- imply
  (verticesAux m h (ts ++ [t])).dropLast = verticesAux m h ts := by
-- proof
  apply StatMech.Universality.HexWalk.endpointVerticesAux_append_one m h ts t

/--
[endpointVertices_ofTurns_append_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointWalk.lean)
-/
@[path]
private lemma endpointVertices_ofTurns_append_one_eq
  {a : ℂ}
  {ts : List ℤ}
  {t : ℤ}
-- given
  (h0 : ℤ) :
-- imply
  (ofTurns a h0 (ts ++ [t])).endpointVertices = (ofTurns a h0 ts).vertices := by
-- proof
  apply StatMech.Universality.HexWalk.endpointVertices_ofTurns_append_one a h0 ts t

/--
[endpointIsSAW_append_one_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointWalk.lean)
-/
@[path]
private lemma endpointIsSAW_append_one_iff_eq
  {a : ℂ}
  {ts : List ℤ}
  {t : ℤ}
-- given
  (h0 : ℤ) :
-- imply
  (ofTurns a h0 (ts ++ [t])).EndpointIsSAW ↔ (ofTurns a h0 ts).IsSAW := by
-- proof
  apply StatMech.Universality.HexWalk.endpointIsSAW_append_one_iff a h0 ts t

/--
[legalTurns_append_one_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointWalk.lean)
-/
@[path]
private lemma legalTurns_append_one_iff_eq
  {a : ℂ}
  {ts : List ℤ}
  {t : ℤ}
-- given
  (h0 : ℤ) :
-- imply
  (ofTurns a h0 (ts ++ [t])).LegalTurns ↔ (ofTurns a h0 ts).LegalTurns ∧ (t = 1 ∨ t = -1) := by
-- proof
  apply StatMech.Universality.HexWalk.legalTurns_append_one_iff a h0 ts t

/--
[endpointIsLegalSAW_append_one_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointWalk.lean)
-/
@[path]
private lemma endpointIsLegalSAW_append_one_iff_eq
  {a : ℂ}
  {ts : List ℤ}
  {t : ℤ}
-- given
  (h0 : ℤ) :
-- imply
  (ofTurns a h0 (ts ++ [t])).EndpointIsLegalSAW ↔ (ofTurns a h0 ts).IsLegalSAW ∧ (t = 1 ∨ t = -1) := by
-- proof
  apply StatMech.Universality.HexWalk.endpointIsLegalSAW_append_one_iff a h0 ts t

/--
[endpoint_nil_isLegalSAW](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointWalk.lean)
-/
@[path]
private lemma endpoint_nil_isLegalSAW_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  (ofTurns a h0 []).EndpointIsLegalSAW := by
-- proof
  apply StatMech.Universality.HexWalk.endpoint_nil_isLegalSAW a h0

/--
[hexEndpoint_mem_sawFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointWalk.lean)
-/
@[path]
private lemma hexEndpoint_mem_sawFinset_eq
  {a : ℂ}
  {n : ℕ}
  {ts : List ℤ}
-- given
  (h0 : ℤ) :
-- imply
  ts ∈ hexEndpointSAWFinset a h0 n ↔ (ofTurns a h0 ts).EndpointIsLegalSAW ∧ ts.length = n := by
-- proof
  apply StatMech.Universality.hexEndpoint_mem_sawFinset a h0 n ts

/--
[hexEndpointSAWCount_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointWalk.lean)
-/
@[path]
private lemma hexEndpointSAWCount_zero_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  hexEndpointSAWCount a h0 0 = 1 := by
-- proof
  apply StatMech.Universality.hexEndpointSAWCount_zero a h0

/--
[hexEndpointSAWCount_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointWalk.lean)
-/
@[path]
private lemma hexEndpointSAWCount_succ_eq
  {a : ℂ}
  {n : ℕ}
-- given
  (h0 : ℤ) :
-- imply
  hexEndpointSAWCount a h0 (n + 1) = 2 * hlc_sawCount a h0 n := by
-- proof
  apply StatMech.Universality.hexEndpointSAWCount_succ a h0 n

/--
[hexEndpointSAWCountR_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointWalk.lean)
-/
@[path]
private lemma hexEndpointSAWCountR_zero_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  hexEndpointSAWCountR a h0 0 = 1 := by
-- proof
  apply StatMech.Universality.hexEndpointSAWCountR_zero a h0

/--
[hexEndpointSAWCountR_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointWalk.lean)
-/
@[path]
private lemma hexEndpointSAWCountR_succ_eq
  {a : ℂ}
  {n : ℕ}
-- given
  (h0 : ℤ) :
-- imply
  hexEndpointSAWCountR a h0 (n + 1) = 2 * hlc_sawCountR a h0 n := by
-- proof
  apply StatMech.Universality.hexEndpointSAWCountR_succ a h0 n

/--
[hexEndpointCoeffWeight_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointWalk.lean)
-/
@[path]
private lemma hexEndpointCoeffWeight_zero_eq
  {a : ℂ}
  {x : ℝ}
-- given
  (h0 : ℤ) :
-- imply
  hexEndpointCoeffWeight a h0 x 0 = 1 := by
-- proof
  apply StatMech.Universality.hexEndpointCoeffWeight_zero a h0 x

/--
[hexEndpointCoeffWeight_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointWalk.lean)
-/
@[path]
private lemma hexEndpointCoeffWeight_succ_eq
  {a : ℂ}
  {x : ℝ}
  {n : ℕ}
-- given
  (h0 : ℤ) :
-- imply
  hexEndpointCoeffWeight a h0 x (n + 1) = (2 * x) * (hlc_sawCountR a h0 n * x ^ n) := by
-- proof
  apply StatMech.Universality.hexEndpointCoeffWeight_succ a h0 x n

/--
[hexEndpoint_summable_iff_hlc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointWalk.lean)
-/
@[path]
private lemma hexEndpoint_summable_iff_hlc_eq
  {a : ℂ}
  {x : ℝ}
-- given
  (h0 : ℤ)
  (hx : x ≠ 0) :
-- imply
  Summable (hexEndpointCoeffWeight a h0 x) ↔ Summable (fun n : ℕ => hlc_sawCountR a h0 n * x ^ n) := by
-- proof
  apply StatMech.Universality.hexEndpoint_summable_iff_hlc a h0 hx

/--
[hexEndpoint_summable_iff_hlc_of_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointWalk.lean)
-/
@[path]
private lemma hexEndpoint_summable_iff_hlc_of_pos_eq
  {a : ℂ}
  {x : ℝ}
-- given
  (h0 : ℤ)
  (hx : 0 < x) :
-- imply
  Summable (hexEndpointCoeffWeight a h0 x) ↔ Summable (fun n : ℕ => hlc_sawCountR a h0 n * x ^ n) := by
-- proof
  apply StatMech.Universality.hexEndpoint_summable_iff_hlc_of_pos a h0 hx

/--
[hexEndpoint_not_summable_iff_hlc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointWalk.lean)
-/
@[path]
private lemma hexEndpoint_not_summable_iff_hlc_eq
  {a : ℂ}
  {x : ℝ}
-- given
  (h0 : ℤ)
  (hx : 0 < x) :
-- imply
  (¬ Summable (hexEndpointCoeffWeight a h0 x)) ↔ ¬ Summable (fun n : ℕ => hlc_sawCountR a h0 n * x ^ n) := by
-- proof
  apply StatMech.Universality.hexEndpoint_not_summable_iff_hlc a h0 hx

/--
[hexEndpoint_tsum_eq_of_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointWalk.lean)
-/
@[path]
private lemma hexEndpoint_tsum_eq_of_summable_eq
  {a : ℂ}
  {x : ℝ}
-- given
  (h0 : ℤ)
  (hcoeff : Summable (fun n : ℕ => hlc_sawCountR a h0 n * x ^ n)) :
-- imply
  (∑' n, hexEndpointCoeffWeight a h0 x n) = 1 + 2 * x * ∑' n, hlc_sawCountR a h0 n * x ^ n := by
-- proof
  apply StatMech.Universality.hexEndpoint_tsum_eq_of_summable a h0 hcoeff

/--
[hexEndpoint_hasSum_of_hlc_hasSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointWalk.lean)
-/
@[path]
private lemma hexEndpoint_hasSum_of_hlc_hasSum_eq
  {a : ℂ}
  {x z : ℝ}
-- given
  (h0 : ℤ)
  (hcoeff : HasSum (fun n : ℕ => hlc_sawCountR a h0 n * x ^ n) z) :
-- imply
  HasSum (hexEndpointCoeffWeight a h0 x) (1 + 2 * x * z) := by
-- proof
  apply StatMech.Universality.hexEndpoint_hasSum_of_hlc_hasSum a h0 hcoeff


-- created on 2026-10-23
