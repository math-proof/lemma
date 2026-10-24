import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.WindingAssembly
open StatMech StatMech.Onsager StatMech.Onsager.WindingAssembly


/--
[isAxisAligned_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WindingAssembly.lean)
-/
@[path]
private lemma isAxisAligned_symm_eq
  {p q : Pt}
-- given
  (h : isAxisAligned p q) :
-- imply
  isAxisAligned q p := by
-- proof
  apply StatMech.Onsager.WindingAssembly.isAxisAligned_symm h

/--
[ccCount_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WindingAssembly.lean)
-/
@[path]
private lemma ccCount_nonneg_eq
  {V : List Pt} :
-- imply
  0 ≤ ccCount V := by
-- proof
  apply StatMech.Onsager.WindingAssembly.ccCount_nonneg V

/--
[rcCount_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WindingAssembly.lean)
-/
@[path]
private lemma rcCount_nonneg_eq
  {V : List Pt} :
-- imply
  0 ≤ rcCount V := by
-- proof
  apply StatMech.Onsager.WindingAssembly.rcCount_nonneg V

/--
[structural_chord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WindingAssembly.lean)
-/
@[path]
private lemma structural_chord_eq
  {V : List Pt}
  {a b : ℕ}
-- given
  (hnd : V.Nodup)
  (hchain : List.IsChain isAxisAligned V)
  (hwrap : ∀ x ∈ V.getLast?, ∀ y ∈ V.head?, isAxisAligned x y)
  (ha : a < V.length)
  (hb : b < V.length)
  (hab : a + 1 < b)
  (hstrict : 0 < a ∨ b + 1 < V.length)
  (hchord : isAxisAligned V[a] V[b]) :
-- imply
  simplePred (arc V a b) ∧ simplePred (coarc V a b) ∧ (arc V a b).length < V.length ∧ (coarc V a b).length < V.length := by
-- proof
  apply StatMech.Onsager.WindingAssembly.structural_chord V a b hnd hchain hwrap ha hb hab hstrict hchord

/--
[getElem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WindingAssembly.lean)
-/
@[path]
private lemma getElem_eq
  {V : List Pt}
  {a : ℕ}
-- given
  (h : a < V.length) :
-- imply
  V[a]! = V[a] := by
-- proof
  apply StatMech.Onsager.WindingAssembly.getElem V a h

/--
[propIV_conditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WindingAssembly.lean)
-/
@[path]
private lemma propIV_conditional_eq
  {V : List Pt}
-- given
  (hbase : ∀ V : List Pt, simplePred V → rcCount V = 0 → ccCount V = 4)
  (hchord : ∀ V : List Pt, simplePred V → 0 < rcCount V → ∃ a b : ℕ, a + 1 < b ∧ b < V.length ∧ (0 < a ∨ b + 1 < V.length) ∧ isAxisAligned V[a]! V[b]! ∧ ccCount (arc V a b) + ccCount (coarc V a b) = ccCount V + 3 ∧ rcCount (arc V a b) + rcCount (coarc V a b) = rcCount V - 1)
  (hV : simplePred V) :
-- imply
  ccCount V - rcCount V = 4 := by
-- proof
  apply StatMech.Onsager.WindingAssembly.propIV_conditional hbase hchord V hV


-- created on 2026-10-23
