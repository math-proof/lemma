import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
open StatMech StatMech.Universality StatMech.Universality.HexWalk


/--
[norm_hexUnit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean)
-/
@[path]
private lemma norm_hexUnit_eq
-- given
  (h : ℤ) :
-- imply
  ‖hexUnit h‖ = 1 := by
-- proof
  apply StatMech.Universality.norm_hexUnit h

/--
[hexUnit_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean)
-/
@[path]
private lemma hexUnit_ne_zero_eq
-- given
  (h : ℤ) :
-- imply
  hexUnit h ≠ 0 := by
-- proof
  apply StatMech.Universality.hexUnit_ne_zero h

/--
[hexUnit_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean)
-/
@[path]
private lemma hexUnit_zero_eq :
-- imply
  hexUnit 0 = Complex.exp (Complex.I * (Real.pi / 6)) := by
-- proof
  apply StatMech.Universality.hexUnit_zero

/--
[hexUnit_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean)
-/
@[path]
private lemma hexUnit_one_eq :
-- imply
  hexUnit 1 = Complex.exp (Complex.I * (Real.pi / 2)) := by
-- proof
  apply StatMech.Universality.hexUnit_one

/--
[hexUnit_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean)
-/
@[path]
private lemma hexUnit_two_eq :
-- imply
  hexUnit 2 = Complex.exp (Complex.I * (5 * Real.pi / 6)) := by
-- proof
  apply StatMech.Universality.hexUnit_two

/--
[hexUnit_add_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean)
-/
@[path]
private lemma hexUnit_add_three_eq
-- given
  (h : ℤ) :
-- imply
  hexUnit (h + 3) = - hexUnit h := by
-- proof
  apply StatMech.Universality.hexUnit_add_three h

/--
[headingsAux_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean)
-/
@[path]
private lemma headingsAux_nil_eq
-- given
  (h : ℤ) :
-- imply
  headingsAux h [] = [h] := by
-- proof
  apply StatMech.Universality.HexWalk.headingsAux_nil h

/--
[headingsAux_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean)
-/
@[path]
private lemma headingsAux_cons_eq
  {ts : List ℤ}
-- given
  (h t : ℤ) :
-- imply
  headingsAux h (t :: ts) = h :: headingsAux (h + t) ts := by
-- proof
  apply StatMech.Universality.HexWalk.headingsAux_cons h t ts

/--
[length_headingsAux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean)
-/
@[path]
private lemma length_headingsAux_eq
  {ts : List ℤ}
-- given
  (h : ℤ) :
-- imply
  (headingsAux h ts).length = ts.length + 1 := by
-- proof
  apply StatMech.Universality.HexWalk.length_headingsAux h ts

/--
[length_headings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean)
-/
@[path]
private lemma length_headings_eq
  {w : HexWalk} :
-- imply
  w.headings.length = w.turns.length + 1 := by
-- proof
  apply StatMech.Universality.HexWalk.length_headings w

/--
[headings_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean)
-/
@[path]
private lemma headings_head_eq
  {w : HexWalk} :
-- imply
  (w.headings).headI = w.h0 := by
-- proof
  apply StatMech.Universality.HexWalk.headings_head w

/--
[midsAux_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean)
-/
@[path]
private lemma midsAux_nil_eq
  {m : ℂ}
-- given
  (h : ℤ) :
-- imply
  midsAux m h [] = [m] := by
-- proof
  apply StatMech.Universality.HexWalk.midsAux_nil m h

/--
[midsAux_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean)
-/
@[path]
private lemma midsAux_cons_eq
  {m : ℂ}
  {ts : List ℤ}
-- given
  (h t : ℤ) :
-- imply
  midsAux m h (t :: ts) = m :: midsAux (m + halfStep h + halfStep (h + t)) (h + t) ts := by
-- proof
  apply StatMech.Universality.HexWalk.midsAux_cons m h t ts

/--
[length_midsAux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean)
-/
@[path]
private lemma length_midsAux_eq
  {m : ℂ}
  {ts : List ℤ}
-- given
  (h : ℤ) :
-- imply
  (midsAux m h ts).length = ts.length + 1 := by
-- proof
  apply StatMech.Universality.HexWalk.length_midsAux m h ts

/--
[length_mids](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean)
-/
@[path]
private lemma length_mids_eq
  {w : HexWalk} :
-- imply
  w.mids.length = w.turns.length + 1 := by
-- proof
  apply StatMech.Universality.HexWalk.length_mids w

/--
[mids_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean)
-/
@[path]
private lemma mids_head_eq
  {w : HexWalk} :
-- imply
  (w.mids).headI = w.startMid := by
-- proof
  apply StatMech.Universality.HexWalk.mids_head w

/--
[verticesAux_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean)
-/
@[path]
private lemma verticesAux_nil_eq
  {m : ℂ}
-- given
  (h : ℤ) :
-- imply
  verticesAux m h [] = [m + halfStep h] := by
-- proof
  apply StatMech.Universality.HexWalk.verticesAux_nil m h

/--
[verticesAux_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean)
-/
@[path]
private lemma verticesAux_cons_eq
  {m : ℂ}
  {ts : List ℤ}
-- given
  (h t : ℤ) :
-- imply
  verticesAux m h (t :: ts) = (m + halfStep h) :: verticesAux (m + halfStep h + halfStep (h + t)) (h + t) ts := by
-- proof
  apply StatMech.Universality.HexWalk.verticesAux_cons m h t ts

/--
[length_verticesAux](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean)
-/
@[path]
private lemma length_verticesAux_eq
  {m : ℂ}
  {ts : List ℤ}
-- given
  (h : ℤ) :
-- imply
  (verticesAux m h ts).length = ts.length + 1 := by
-- proof
  apply StatMech.Universality.HexWalk.length_verticesAux m h ts

/--
[length_vertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean)
-/
@[path]
private lemma length_vertices_eq
  {w : HexWalk} :
-- imply
  w.vertices.length = w.turns.length + 1 := by
-- proof
  apply StatMech.Universality.HexWalk.length_vertices w

/--
[numVertices_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean)
-/
@[path]
private lemma numVertices_eq_eq
  {w : HexWalk} :
-- imply
  w.numVertices = w.turns.length + 1 := by
-- proof
  apply StatMech.Universality.HexWalk.numVertices_eq w

/--
[length_vertices_eq_numVertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean)
-/
@[path]
private lemma length_vertices_eq_numVertices_eq
  {w : HexWalk} :
-- imply
  w.vertices.length = w.numVertices := by
-- proof
  apply StatMech.Universality.HexWalk.length_vertices_eq_numVertices w

/--
[turnCount_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean)
-/
@[path]
private lemma turnCount_eq_eq
  {w : HexWalk} :
-- imply
  w.turnCount = w.turns.sum := by
-- proof
  apply StatMech.Universality.HexWalk.turnCount_eq w

/--
[turning_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean)
-/
@[path]
private lemma turning_eq_eq
  {w : HexWalk} :
-- imply
  w.turning = (Real.pi / 3) * (w.turns.sum : ℝ) := by
-- proof
  apply StatMech.Universality.HexWalk.turning_eq w

/--
[trivialWalk_startMid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean)
-/
@[path]
private lemma trivialWalk_startMid_eq
  {a : ℂ}
-- given
  (h : ℤ) :
-- imply
  (trivialWalk a h).startMid = a := by
-- proof
  apply StatMech.Universality.HexWalk.trivialWalk_startMid a h

/--
[trivialWalk_h0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean)
-/
@[path]
private lemma trivialWalk_h0_eq
  {a : ℂ}
-- given
  (h : ℤ) :
-- imply
  (trivialWalk a h).h0 = h := by
-- proof
  apply StatMech.Universality.HexWalk.trivialWalk_h0 a h

/--
[trivialWalk_turns](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean)
-/
@[path]
private lemma trivialWalk_turns_eq
  {a : ℂ}
-- given
  (h : ℤ) :
-- imply
  (trivialWalk a h).turns = [] := by
-- proof
  apply StatMech.Universality.HexWalk.trivialWalk_turns a h

/--
[trivialWalk_numVertices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean)
-/
@[path]
private lemma trivialWalk_numVertices_eq
  {a : ℂ}
-- given
  (h : ℤ) :
-- imply
  (trivialWalk a h).numVertices = 1 := by
-- proof
  apply StatMech.Universality.HexWalk.trivialWalk_numVertices a h

/--
[trivialWalk_turning](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean)
-/
@[path]
private lemma trivialWalk_turning_eq
  {a : ℂ}
-- given
  (h : ℤ) :
-- imply
  (trivialWalk a h).turning = 0 := by
-- proof
  apply StatMech.Universality.HexWalk.trivialWalk_turning a h

/--
[trivialWalk_legalTurns](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean)
-/
@[path]
private lemma trivialWalk_legalTurns_eq
  {a : ℂ}
-- given
  (h : ℤ) :
-- imply
  (trivialWalk a h).LegalTurns := by
-- proof
  apply StatMech.Universality.HexWalk.trivialWalk_legalTurns a h

/--
[trivialWalk_isSAW](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean)
-/
@[path]
private lemma trivialWalk_isSAW_eq
  {a : ℂ}
-- given
  (h : ℤ) :
-- imply
  (trivialWalk a h).IsSAW := by
-- proof
  apply StatMech.Universality.HexWalk.trivialWalk_isSAW a h

/--
[trivialWalk_isLegalSAW](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean)
-/
@[path]
private lemma trivialWalk_isLegalSAW_eq
  {a : ℂ}
-- given
  (h : ℤ) :
-- imply
  (trivialWalk a h).IsLegalSAW := by
-- proof
  apply StatMech.Universality.HexWalk.trivialWalk_isLegalSAW a h

/--
[turnCount_append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean)
-/
@[path]
private lemma turnCount_append_eq
  {a : ℂ}
  {s t : List ℤ}
-- given
  (h : ℤ) :
-- imply
  turnCount ⟨a, h, s ++ t⟩ = turnCount ⟨a, h, s⟩ + turnCount ⟨a, h, t⟩ := by
-- proof
  apply StatMech.Universality.HexWalk.turnCount_append a h s t

/--
[turning_append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean)
-/
@[path]
private lemma turning_append_eq
  {a : ℂ}
  {s t : List ℤ}
-- given
  (h : ℤ) :
-- imply
  turning ⟨a, h, s ++ t⟩ = turning ⟨a, h, s⟩ + turning ⟨a, h, t⟩ := by
-- proof
  apply StatMech.Universality.HexWalk.turning_append a h s t

/--
[turning_concat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean)
-/
@[path]
private lemma turning_concat_eq
  {a : ℂ}
  {s : List ℤ}
  {t : ℤ}
-- given
  (h : ℤ) :
-- imply
  turning ⟨a, h, s ++ [t]⟩ = turning ⟨a, h, s⟩ + (Real.pi / 3) * (t : ℝ) := by
-- proof
  apply StatMech.Universality.HexWalk.turning_concat a h s t

/--
[ofTurns_turns](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean)
-/
@[path]
private lemma ofTurns_turns_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ) :
-- imply
  (ofTurns a h0 ts).turns = ts := by
-- proof
  apply StatMech.Universality.HexWalk.ofTurns_turns a h0 ts

/--
[ofTurns_startMid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean)
-/
@[path]
private lemma ofTurns_startMid_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ) :
-- imply
  (ofTurns a h0 ts).startMid = a := by
-- proof
  apply StatMech.Universality.HexWalk.ofTurns_startMid a h0 ts

/--
[ofTurns_h0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean)
-/
@[path]
private lemma ofTurns_h0_eq
  {a : ℂ}
  {ts : List ℤ}
-- given
  (h0 : ℤ) :
-- imply
  (ofTurns a h0 ts).h0 = h0 := by
-- proof
  apply StatMech.Universality.HexWalk.ofTurns_h0 a h0 ts

/--
[hexZSummand_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean)
-/
@[path]
private lemma hexZSummand_nil_eq
  {a : ℂ}
  {x : ℝ}
-- given
  (h0 : ℤ) :
-- imply
  hexZSummand a h0 x [] = ENNReal.ofReal x := by
-- proof
  apply StatMech.Universality.hexZSummand_nil a h0 x

/--
[trivialWalk_endMid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean)
-/
@[path]
private lemma trivialWalk_endMid_eq
  {a : ℂ}
-- given
  (h0 : ℤ) :
-- imply
  HexWalk.endMid (trivialWalk a h0) = a := by
-- proof
  apply StatMech.Universality.trivialWalk_endMid a h0

/--
[parafSummand_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean)
-/
@[path]
private lemma parafSummand_self_eq
  {a : ℂ}
  {σ x : ℝ}
-- given
  (region : ℂ → Prop)
  (h0 : ℤ)
  (hreg : region a) :
-- imply
  parafSummand region a h0 a σ x [] = (x : ℂ) := by
-- proof
  apply StatMech.Universality.parafSummand_self region a h0 σ x hreg


-- created on 2026-10-23
