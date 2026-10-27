import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Tiling.DominoTilings.Part13
import Lemma.Nat.DominoTilings
import Lemma.Nat.EqShiftNat.of.Ge1Add1.Ge1Add1.Domino
import Lemma.Nat.Ge12.Ge12.of.NeVertical11.In_Dominos.InVertical11Dominos.Domino.DominoTiling
open DominoTilings
open Domino DominoTiling
open Finset
open Nat


/--
[DominoTilings](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/Details/DominoTilings.lean)
-/
@[path]
private lemma main
-- given
  (T : DominoTiling (n + 1) 2)
  (hv : vertical_1_1 ∈ T.dominos) :
-- imply
  prependVertical (restrictAfterVertical T hv) = T := by
-- proof
  cases T with
  | mk dominos dominos_in_rect covers_all pairwise_disjoint =>
    unfold prependVertical restrictAfterVertical
    congr 1
    ext d
    simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
    constructor
    ·
      intro hd
      obtain rfl | ⟨d', hd'_mem, hd'_eq⟩ := hd
      · exact hv
      ·
        obtain ⟨d'', hd''_erase, hd''_eq⟩ := hd'_mem
        have hd''_in := Finset.mem_of_mem_erase hd''_erase
        have hd''_ne := (Finset.mem_erase.mp hd''_erase).1
        have hcols := Ge12.Ge12.of.NeVertical11.In_Dominos.InVertical11Dominos.Domino.DominoTiling
          ⟨dominos, dominos_in_rect, covers_all, pairwise_disjoint⟩ d'' hv hd''_in hd''_ne
        -- d' = d''.shiftNeg 1 ..., d = d'.shiftNat 1
        -- So d = (d''.shiftNeg 1 ...).shiftNat 1 = d''
        rw [← hd'_eq, ← hd''_eq]
        rwa [EqShiftNat.of.Ge1Add1.Ge1Add1.Domino]
    ·
      intro hd
      if hne : d = vertical_1_1 then
        left
        exact hne
      else
        right
        have hd_erase : d ∈ dominos.erase vertical_1_1 := Finset.mem_erase.mpr ⟨hne, hd⟩
        have hcols := Ge12.Ge12.of.NeVertical11.In_Dominos.InVertical11Dominos.Domino.DominoTiling
          ⟨dominos, dominos_in_rect, covers_all, pairwise_disjoint⟩ d hv hd hne
        use d.shiftNeg 1 hcols.1 hcols.2
        constructor
        · use d, hd_erase
        · exact EqShiftNat.of.Ge1Add1.Ge1Add1.Domino d 1 hcols.1 hcols.2


-- created on 2026-10-20
