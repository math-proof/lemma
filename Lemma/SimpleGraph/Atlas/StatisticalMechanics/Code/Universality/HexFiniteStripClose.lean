import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripClose.Part2
open StatMech StatMech.Universality


/--
[hfs_verticesAux_take](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripClose.lean)
-/
@[path]
private lemma hfs_verticesAux_take_eq
  {m : ℂ}
  {ts : List ℤ}
  {cp : ℕ}
-- given
  (h : ℤ) :
-- imply
  verticesAux m h (ts.take cp) = (verticesAux m h ts).take (cp + 1) := by
-- proof
  apply StatMech.Universality.hfs_verticesAux_take m h ts cp

/--
[hfs_verticesAux_drop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripClose.lean)
-/
@[path]
private lemma hfs_verticesAux_drop_eq
  {m : ℂ}
  {ts : List ℤ}
  {cp : ℕ}
-- given
  (h : ℤ)
  (hcp : cp ≤ ts.length) :
-- imply
  verticesAux (hfs_stMid m h (ts.take cp)) (hfs_stHead h (ts.take cp)) (ts.drop cp) = (verticesAux m h ts).drop cp := by
-- proof
  apply StatMech.Universality.hfs_verticesAux_drop m h ts cp hcp

/--
[hfs_legalTurns_take](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripClose.lean)
-/
@[path]
private lemma hfs_legalTurns_take_eq
  {a : ℂ}
  {ts : List ℤ}
  {cp : ℕ}
-- given
  (h0 : ℤ)
  (hleg : (ofTurns a h0 ts).LegalTurns) :
-- imply
  (ofTurns a h0 (ts.take cp)).LegalTurns := by
-- proof
  apply StatMech.Universality.hfs_legalTurns_take a h0 ts cp hleg

/--
[hfs_legalTurns_drop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripClose.lean)
-/
@[path]
private lemma hfs_legalTurns_drop_eq
  {a2 : ℂ}
  {a : ℂ}
  {ts : List ℤ}
  {cp : ℕ}
-- given
  (h2 : ℤ)
  (h0 : ℤ)
  (hleg : (ofTurns a h0 ts).LegalTurns) :
-- imply
  (ofTurns a2 h2 (ts.drop cp)).LegalTurns := by
-- proof
  apply StatMech.Universality.hfs_legalTurns_drop a2 h2 a h0 ts cp hleg

/--
[hfs_isSAW_take](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripClose.lean)
-/
@[path]
private lemma hfs_isSAW_take_eq
  {a : ℂ}
  {ts : List ℤ}
  {cp : ℕ}
-- given
  (h0 : ℤ)
  (h : (ofTurns a h0 ts).IsSAW) :
-- imply
  (ofTurns a h0 (ts.take cp)).IsSAW := by
-- proof
  apply StatMech.Universality.hfs_isSAW_take a h0 ts cp h

/--
[hfs_isSAW_drop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripClose.lean)
-/
@[path]
private lemma hfs_isSAW_drop_eq
  {a : ℂ}
  {ts : List ℤ}
  {cp : ℕ}
-- given
  (h0 : ℤ)
  (hcp : cp ≤ ts.length)
  (h : (ofTurns a h0 ts).IsSAW) :
-- imply
  (ofTurns (hfs_stMid a h0 (ts.take cp)) (hfs_stHead h0 (ts.take cp)) (ts.drop cp)).IsSAW := by
-- proof
  apply StatMech.Universality.hfs_isSAW_drop a h0 ts cp hcp h

/--
[hfs_isLegalSAW_take](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripClose.lean)
-/
@[path]
private lemma hfs_isLegalSAW_take_eq
  {a : ℂ}
  {ts : List ℤ}
  {cp : ℕ}
-- given
  (h0 : ℤ)
  (h : (ofTurns a h0 ts).IsLegalSAW) :
-- imply
  (ofTurns a h0 (ts.take cp)).IsLegalSAW := by
-- proof
  apply StatMech.Universality.hfs_isLegalSAW_take a h0 ts cp h

/--
[hfs_isLegalSAW_drop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripClose.lean)
-/
@[path]
private lemma hfs_isLegalSAW_drop_eq
  {a : ℂ}
  {ts : List ℤ}
  {cp : ℕ}
-- given
  (h0 : ℤ)
  (hcp : cp ≤ ts.length)
  (h : (ofTurns a h0 ts).IsLegalSAW) :
-- imply
  (ofTurns (hfs_stMid a h0 (ts.take cp)) (hfs_stHead h0 (ts.take cp)) (ts.drop cp)).IsLegalSAW := by
-- proof
  apply StatMech.Universality.hfs_isLegalSAW_drop a h0 ts cp hcp h

/--
[hfs_legality_fires](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripClose.lean)
-/
@[path]
private lemma hfs_legality_fires_eq :
-- imply
  (ofTurns (0 : ℂ) 0 [1, -1]).LegalTurns ∧ (ofTurns (0 : ℂ) 0 ([1, -1].take 1)).LegalTurns ∧ (ofTurns (0 : ℂ) 0 [1, -1]).numVertices = 3 ∧ (ofTurns (0 : ℂ) 0 ([1, -1].take 1)).numVertices = 2 ∧ (ofTurns (0 : ℂ) 0 ([1, -1].drop 1)).numVertices = 2 := by
-- proof
  apply StatMech.Universality.hfs_legality_fires


-- created on 2026-10-23
