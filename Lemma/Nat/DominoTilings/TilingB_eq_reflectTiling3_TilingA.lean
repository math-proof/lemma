import Mathlib
import sympy.Basic
import sympy.matrices.determinants.DominoTilings
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
  (n : ℕ)
  (hn : Even n)
  (hn_ge : n ≥ 2) :
-- imply
  TilingB n hn hn_ge = reflectTiling3 (TilingA n hn hn_ge) := by
-- proof
  -- Two DominoTiling structures are equal if their dominos fields are equal
  -- (the other fields are propositions, so equal by proof irrelevance)
  -- First show the dominos are equal, then use that to conclude
  have h_dominos : (TilingB n hn hn_ge).dominos = (reflectTiling3 (TilingA n hn hn_ge)).dominos := by
    -- Unfold the definitions
    simp only [TilingB, reflectTiling3, TilingA]
    -- Show the two Finsets are equal
    ext d
    constructor
    · -- d ∈ TilingB.dominos → d ∈ (reflectTiling3 TilingA).dominos
      intro hd
      simp only [Finset.mem_union, Finset.mem_singleton] at hd
      simp only [Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists,
        ← Function.Embedding.toFun_eq_coe]
      -- Case analysis on which subset d comes from
      obtain ((((hbase | hleft) | hright) | hmid) | hbot) := hd
      · -- d ∈ basementDominosB n (reflected from basementDominos)
        simp only [basementDominosB, Finset.mem_map, Finset.mem_range,
          ← Function.Embedding.toFun_eq_coe] at hbase
        obtain ⟨i, hi, rfl⟩ := hbase
        -- The original domino in basementDominos
        let d' : Domino := ⟨(2 * i + 1, 1), (2 * i + 2, 1),
              by simp only [ne_eq, Prod.mk.injEq, and_true]; omega,
              by right; exact ⟨rfl, Or.inl rfl⟩⟩
        refine ⟨d', ?_, ?_⟩
        · -- This domino is in TilingA.dominos
          simp only [Finset.mem_union, Finset.mem_singleton, basementDominos, Finset.mem_map,
            Finset.mem_range, ← Function.Embedding.toFun_eq_coe]
          left; left; left; left
          exact ⟨i, hi, rfl⟩
        · rfl
      · -- d = leftWallB (reflected from leftWall)
        refine ⟨leftWall, ?_, ?_⟩
        ·
          simp only [Finset.mem_union, Finset.mem_singleton]
          left; left; left; right; trivial
        ·
          subst hleft
          rfl
      · -- d = rightWallB n (reflected from rightWall n)
        refine ⟨rightWall n, ?_, ?_⟩
        ·
          simp only [Finset.mem_union, Finset.mem_singleton]
          left; left; right; trivial
        ·
          subst hright
          rfl
      · -- d ∈ middleDominos n (unchanged by reflection since row 2 is fixed)
        simp only [middleDominos, Finset.mem_map, Finset.mem_range,
          ← Function.Embedding.toFun_eq_coe] at hmid
        obtain ⟨i, hi, rfl⟩ := hmid
        let d' : Domino := ⟨(2 * i + 2, 2), (2 * i + 3, 2),
              by simp only [ne_eq, Prod.mk.injEq, and_true]; omega,
              by right; exact ⟨rfl, Or.inl rfl⟩⟩
        refine ⟨d', ?_, ?_⟩
        ·
          simp only [Finset.mem_union, Finset.mem_singleton, middleDominos, Finset.mem_map,
            Finset.mem_range, ← Function.Embedding.toFun_eq_coe]
          left; right
          exact ⟨i, hi, rfl⟩
        · rfl
      · -- d ∈ bottomDominosB n (reflected from topDominos)
        simp only [bottomDominosB, Finset.mem_map, Finset.mem_range,
          ← Function.Embedding.toFun_eq_coe] at hbot
        obtain ⟨i, hi, rfl⟩ := hbot
        let d' : Domino := ⟨(2 * i + 2, 3), (2 * i + 3, 3),
              by simp only [ne_eq, Prod.mk.injEq, and_true]; omega,
              by right; exact ⟨rfl, Or.inl rfl⟩⟩
        refine ⟨d', ?_, ?_⟩
        ·
          simp only [Finset.mem_union, Finset.mem_singleton, topDominos, Finset.mem_map,
            Finset.mem_range, ← Function.Embedding.toFun_eq_coe]
          right
          exact ⟨i, hi, rfl⟩
        · rfl
    · -- d ∈ (reflectTiling3 TilingA).dominos → d ∈ TilingB.dominos
      intro hd
      simp only [Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists,
        ← Function.Embedding.toFun_eq_coe] at hd
      obtain ⟨d', hd'_mem, hd'_eq⟩ := hd
      simp only [Finset.mem_union, Finset.mem_singleton] at hd'_mem ⊢
      -- Case analysis on which subset d' comes from
      obtain ((((hbase | hleft) | hright) | hmid) | htop) := hd'_mem
      · -- d' ∈ basementDominos n → d ∈ basementDominosB n
        simp only [basementDominos, Finset.mem_map, Finset.mem_range,
          ← Function.Embedding.toFun_eq_coe] at hbase
        obtain ⟨i, hi, rfl⟩ := hbase
        left; left; left; left
        simp only [basementDominosB, Finset.mem_map, Finset.mem_range, ← Function.Embedding.toFun_eq_coe]
        use i, hi
        exact hd'_eq
      · -- d' = leftWall → d = leftWallB
        left; left; left; right
        subst hleft
        exact hd'_eq.symm
      · -- d' = rightWall n → d = rightWallB n
        left; left; right
        subst hright
        exact hd'_eq.symm
      · -- d' ∈ middleDominos n → d ∈ middleDominos n
        simp only [middleDominos, Finset.mem_map, Finset.mem_range,
          ← Function.Embedding.toFun_eq_coe] at hmid
        obtain ⟨i, hi, rfl⟩ := hmid
        left; right
        simp only [middleDominos, Finset.mem_map, Finset.mem_range, ← Function.Embedding.toFun_eq_coe]
        use i, hi
        exact hd'_eq
      · -- d' ∈ topDominos n → d ∈ bottomDominosB n
        simp only [topDominos, Finset.mem_map, Finset.mem_range,
          ← Function.Embedding.toFun_eq_coe] at htop
        obtain ⟨i, hi, rfl⟩ := htop
        right
        simp only [bottomDominosB, Finset.mem_map, Finset.mem_range, ← Function.Embedding.toFun_eq_coe]
        use i, hi
        exact hd'_eq
  -- Now conclude equality of the DominoTiling structures
  cases hB : TilingB n hn hn_ge
  cases hR : reflectTiling3 (TilingA n hn hn_ge)
  simp only [DominoTiling.mk.injEq]
  simp only [hB, hR] at h_dominos
  exact h_dominos

/-!
## Main Classification Theorem

Proposition prop.gf.weighted-set.domino.Rn3.ABC states that the faultfree domino tilings
of height-3 rectangles are precisely:
- A_2, A_4, A_6, A_8, ... (tilings with vertical domino in top of column 1)
- B_2, B_4, B_6, B_8, ... (tilings with vertical domino in bottom of column 1)
- C (the unique tiling with no vertical domino in column 1)
-/


-- created on 2026-10-20
