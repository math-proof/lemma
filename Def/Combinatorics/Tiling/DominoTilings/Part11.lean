import Mathlib
import Theorem.Combinatorics.Tiling.DominoTilings.Part8
open Finset BigOperators


namespace DominoTilings

namespace DominoTiling

variable {n m : ℕ}


noncomputable def tiling_2_to_sum (T : DominoTiling (n + 2) 2) :
    (DominoTiling n 2) ⊕ (DominoTiling (n + 1) 2) :=
  if hv : hasVerticalFirstColumn T then
    -- Vertical case: there's a domino covering (1,1) and (1,2)
    let v := Classical.choose hv
    let hv_spec := Classical.choose_spec hv
    let hv_mem := hv_spec.1
    let hv_cells := hv_spec.2
    Sum.inr (restrictAfterVerticalGen T v hv_mem hv_cells)
  else
    -- Horizontal case: there are dominos covering (1,1)-(2,1) and (1,2)-(2,2)
    let hpair := horizontalPair_of_not_hasVerticalFirstColumn T hv
    let d1 := Classical.choose hpair.1
    let hd1_spec := Classical.choose_spec hpair.1
    let hd1_mem := hd1_spec.1
    let hd1_cells := hd1_spec.2
    let d2 := Classical.choose hpair.2
    let hd2_spec := Classical.choose_spec hpair.2
    let hd2_mem := hd2_spec.1
    let hd2_cells := hd2_spec.2
    Sum.inl (restrictAfterHorizontalPairGen T d1 d2 hd1_mem hd2_mem hd1_cells hd2_cells)


def tiling_2_from_sum : (DominoTiling n 2) ⊕ (DominoTiling (n + 1) 2) → DominoTiling (n + 2) 2 :=
  Sum.elim prependHorizontalPair prependVertical


end DominoTiling


def mkHorizontalDomino (x y : ℕ) : Domino where
  cell1 := (x, y)
  cell2 := (x + 1, y)
  distinct := by simp only [ne_eq, Prod.mk.injEq, and_true]; omega
  adjacent := by right; constructor; rfl; left; rfl


def mkVerticalDomino (x y : ℕ) : Domino where
  cell1 := (x, y)
  cell2 := (x, y + 1)
  distinct := by simp only [ne_eq, Prod.mk.injEq, true_and]; omega
  adjacent := by left; constructor; rfl; left; rfl


def basementDominos (n : ℕ) : Finset Domino :=
  (Finset.range (n / 2)).map ⟨fun i =>
    { cell1 := (2 * i + 1, 1)
      cell2 := (2 * i + 2, 1)
      distinct := by simp only [ne_eq, Prod.mk.injEq, and_true]; omega
      adjacent := by right; exact ⟨rfl, Or.inl rfl⟩ }, by
    intro a b hab
    simp only [Domino.mk.injEq, Prod.mk.injEq] at hab
    omega⟩


def leftWall : Domino where
  cell1 := (1, 2)
  cell2 := (1, 3)
  distinct := by simp only [ne_eq, Prod.mk.injEq, true_and]; omega
  adjacent := by left; exact ⟨rfl, Or.inl rfl⟩


def rightWall (n : ℕ) : Domino where
  cell1 := (n, 2)
  cell2 := (n, 3)
  distinct := by simp only [ne_eq, Prod.mk.injEq, true_and]; omega
  adjacent := by left; exact ⟨rfl, Or.inl rfl⟩


def middleDominos (n : ℕ) : Finset Domino :=
  (Finset.range (n / 2 - 1)).map ⟨fun i =>
    { cell1 := (2 * i + 2, 2)
      cell2 := (2 * i + 3, 2)
      distinct := by simp only [ne_eq, Prod.mk.injEq, and_true]; omega
      adjacent := by right; exact ⟨rfl, Or.inl rfl⟩ }, by
    intro a b hab
    simp only [Domino.mk.injEq, Prod.mk.injEq] at hab
    omega⟩


def topDominos (n : ℕ) : Finset Domino :=
  (Finset.range (n / 2 - 1)).map ⟨fun i =>
    { cell1 := (2 * i + 2, 3)
      cell2 := (2 * i + 3, 3)
      distinct := by simp only [ne_eq, Prod.mk.injEq, and_true]; omega
      adjacent := by right; exact ⟨rfl, Or.inl rfl⟩ }, by
    intro a b hab
    simp only [Domino.mk.injEq, Prod.mk.injEq] at hab
    omega⟩


def TilingA (n : ℕ) (hn : Even n) (hn_ge : n ≥ 2) : DominoTiling n 3 where
  dominos := basementDominos n ∪ {leftWall} ∪ {rightWall n} ∪
             middleDominos n ∪ topDominos n
  dominos_in_rect := by
    intro d hd
    simp only [Finset.mem_union, Finset.mem_singleton] at hd
    rcases hd with ((((hd | hd) | hd) | hd) | hd)
    · -- d ∈ basementDominos n
      simp only [basementDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd
      obtain ⟨i, hi, hd_eq⟩ := hd
      intro c hc
      simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc
      have hcell1 : d.cell1 = (2 * i + 1, 1) := by rw [← hd_eq]
      have hcell2 : d.cell2 = (2 * i + 2, 1) := by rw [← hd_eq]
      rcases hc with hc1 | hc2
      · rw [hc1, hcell1, mem_Rectangle]
        refine ⟨?_, ?_, ?_, ?_⟩
        · omega
        · have h1 : 2 * i + 1 ≤ 2 * (n / 2) := by omega
          have h2 : 2 * (n / 2) ≤ n := by rw [mul_comm]; exact Nat.div_mul_le_self n 2
          omega
        · omega
        · omega
      · rw [hc2, hcell2, mem_Rectangle]
        refine ⟨?_, ?_, ?_, ?_⟩
        · omega
        · have h1 : 2 * i + 2 ≤ 2 * (n / 2) := by
            have : i + 1 ≤ n / 2 := hi
            omega
          have h2 : 2 * (n / 2) ≤ n := by rw [mul_comm]; exact Nat.div_mul_le_self n 2
          omega
        · omega
        · omega
    · -- d = leftWall
      subst hd
      intro c hc
      simp only [leftWall, Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl
      · rw [mem_Rectangle]; omega
      · rw [mem_Rectangle]; omega
    · -- d = rightWall n
      subst hd
      intro c hc
      simp only [rightWall, Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl
      · rw [mem_Rectangle]; omega
      · rw [mem_Rectangle]; omega
    · -- d ∈ middleDominos n
      simp only [middleDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd
      obtain ⟨i, hi, hd_eq⟩ := hd
      intro c hc
      simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc
      have hcell1 : d.cell1 = (2 * i + 2, 2) := by rw [← hd_eq]
      have hcell2 : d.cell2 = (2 * i + 3, 2) := by rw [← hd_eq]
      rcases hc with hc1 | hc2
      · rw [hc1, hcell1, mem_Rectangle]
        refine ⟨?_, ?_, ?_, ?_⟩
        · omega
        · have h1 : 2 * i + 2 ≤ 2 * (n / 2 - 1) + 1 := by omega
          have h2 : 2 * (n / 2 - 1) + 1 ≤ n - 1 := by
            obtain ⟨k, hk⟩ := hn
            subst hk
            have hk_pos : k ≥ 1 := by omega
            omega
          omega
        · omega
        · omega
      · rw [hc2, hcell2, mem_Rectangle]
        refine ⟨?_, ?_, ?_, ?_⟩
        · omega
        · have h1 : 2 * i + 3 ≤ 2 * (n / 2 - 1) + 2 := by omega
          have h2 : 2 * (n / 2 - 1) + 2 ≤ n := by
            obtain ⟨k, hk⟩ := hn
            subst hk
            have hk_pos : k ≥ 1 := by omega
            omega
          omega
        · omega
        · omega
    · -- d ∈ topDominos n
      simp only [topDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd
      obtain ⟨i, hi, hd_eq⟩ := hd
      intro c hc
      simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc
      have hcell1 : d.cell1 = (2 * i + 2, 3) := by rw [← hd_eq]
      have hcell2 : d.cell2 = (2 * i + 3, 3) := by rw [← hd_eq]
      rcases hc with hc1 | hc2
      · rw [hc1, hcell1, mem_Rectangle]
        refine ⟨?_, ?_, ?_, ?_⟩
        · omega
        · have h1 : 2 * i + 2 ≤ 2 * (n / 2 - 1) + 1 := by omega
          have h2 : 2 * (n / 2 - 1) + 1 ≤ n - 1 := by
            obtain ⟨k, hk⟩ := hn
            subst hk
            have hk_pos : k ≥ 1 := by omega
            omega
          omega
        · omega
        · omega
      · rw [hc2, hcell2, mem_Rectangle]
        refine ⟨?_, ?_, ?_, ?_⟩
        · omega
        · have h1 : 2 * i + 3 ≤ 2 * (n / 2 - 1) + 2 := by omega
          have h2 : 2 * (n / 2 - 1) + 2 ≤ n := by
            obtain ⟨k, hk⟩ := hn
            subst hk
            have hk_pos : k ≥ 1 := by omega
            omega
          omega
        · omega
        · omega
  covers_all := by
    ext c
    simp only [Finset.mem_biUnion]
    constructor
    · -- c in biUnion → c in Rectangle (from dominos_in_rect)
      rintro ⟨d, hd_mem, hc_in_d⟩
      simp only [Finset.mem_union, Finset.mem_singleton] at hd_mem
      rcases hd_mem with ((((hd | hd) | hd) | hd) | hd)
      · -- d ∈ basementDominos n
        simp only [basementDominos, Finset.mem_map, Finset.mem_range,
          ← Function.Embedding.toFun_eq_coe] at hd
        obtain ⟨i, hi, hd_eq⟩ := hd
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d
        have hcell1 : d.cell1 = (2 * i + 1, 1) := by rw [← hd_eq]
        have hcell2 : d.cell2 = (2 * i + 2, 1) := by rw [← hd_eq]
        rcases hc_in_d with hc1 | hc2
        · rw [hc1, hcell1, mem_Rectangle]
          refine ⟨?_, ?_, ?_, ?_⟩
          · omega
          · have h1 : 2 * i + 1 ≤ 2 * (n / 2) := by omega
            have h2 : 2 * (n / 2) ≤ n := by rw [mul_comm]; exact Nat.div_mul_le_self n 2
            omega
          · omega
          · omega
        · rw [hc2, hcell2, mem_Rectangle]
          refine ⟨?_, ?_, ?_, ?_⟩
          · omega
          · have h1 : 2 * i + 2 ≤ 2 * (n / 2) := by
              have : i + 1 ≤ n / 2 := hi
              omega
            have h2 : 2 * (n / 2) ≤ n := by rw [mul_comm]; exact Nat.div_mul_le_self n 2
            omega
          · omega
          · omega
      · -- d = leftWall
        subst hd
        simp only [leftWall, Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d
        rcases hc_in_d with rfl | rfl
        · rw [mem_Rectangle]; omega
        · rw [mem_Rectangle]; omega
      · -- d = rightWall n
        subst hd
        simp only [rightWall, Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d
        rcases hc_in_d with rfl | rfl
        · rw [mem_Rectangle]; omega
        · rw [mem_Rectangle]; omega
      · -- d ∈ middleDominos n
        simp only [middleDominos, Finset.mem_map, Finset.mem_range,
          ← Function.Embedding.toFun_eq_coe] at hd
        obtain ⟨i, hi, hd_eq⟩ := hd
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d
        have hcell1 : d.cell1 = (2 * i + 2, 2) := by rw [← hd_eq]
        have hcell2 : d.cell2 = (2 * i + 3, 2) := by rw [← hd_eq]
        rcases hc_in_d with hc1 | hc2
        · rw [hc1, hcell1, mem_Rectangle]
          refine ⟨?_, ?_, ?_, ?_⟩
          · omega
          · have h1 : 2 * i + 2 ≤ 2 * (n / 2 - 1) + 1 := by omega
            have h2 : 2 * (n / 2 - 1) + 1 ≤ n - 1 := by
              obtain ⟨k, hk⟩ := hn
              subst hk
              have hk_pos : k ≥ 1 := by omega
              omega
            omega
          · omega
          · omega
        · rw [hc2, hcell2, mem_Rectangle]
          refine ⟨?_, ?_, ?_, ?_⟩
          · omega
          · have h1 : 2 * i + 3 ≤ 2 * (n / 2 - 1) + 2 := by omega
            have h2 : 2 * (n / 2 - 1) + 2 ≤ n := by
              obtain ⟨k, hk⟩ := hn
              subst hk
              have hk_pos : k ≥ 1 := by omega
              omega
            omega
          · omega
          · omega
      · -- d ∈ topDominos n
        simp only [topDominos, Finset.mem_map, Finset.mem_range,
          ← Function.Embedding.toFun_eq_coe] at hd
        obtain ⟨i, hi, hd_eq⟩ := hd
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d
        have hcell1 : d.cell1 = (2 * i + 2, 3) := by rw [← hd_eq]
        have hcell2 : d.cell2 = (2 * i + 3, 3) := by rw [← hd_eq]
        rcases hc_in_d with hc1 | hc2
        · rw [hc1, hcell1, mem_Rectangle]
          refine ⟨?_, ?_, ?_, ?_⟩
          · omega
          · have h1 : 2 * i + 2 ≤ 2 * (n / 2 - 1) + 1 := by omega
            have h2 : 2 * (n / 2 - 1) + 1 ≤ n - 1 := by
              obtain ⟨k, hk⟩ := hn
              subst hk
              have hk_pos : k ≥ 1 := by omega
              omega
            omega
          · omega
          · omega
        · rw [hc2, hcell2, mem_Rectangle]
          refine ⟨?_, ?_, ?_, ?_⟩
          · omega
          · have h1 : 2 * i + 3 ≤ 2 * (n / 2 - 1) + 2 := by omega
            have h2 : 2 * (n / 2 - 1) + 2 ≤ n := by
              obtain ⟨k, hk⟩ := hn
              subst hk
              have hk_pos : k ≥ 1 := by omega
              omega
            omega
          · omega
          · omega
    · -- c in Rectangle → c in biUnion
      intro hc
      rw [mem_Rectangle] at hc
      obtain ⟨hcol_ge, hcol_le, hrow_ge, hrow_le⟩ := hc
      have hrow : c.2 = 1 ∨ c.2 = 2 ∨ c.2 = 3 := by omega
      rcases hrow with hrow1 | hrow2 | hrow3
      · -- c.2 = 1: covered by basementDominos
        -- Find i such that c.1 ∈ {2i+1, 2i+2}
        have hcol_range : ∃ i < n / 2, c.1 = 2 * i + 1 ∨ c.1 = 2 * i + 2 := by
          use (c.1 - 1) / 2
          constructor
          · obtain ⟨k, hk⟩ := hn; subst hk
            have h2 : c.1 - 1 < 2 * k := by omega
            have : (c.1 - 1) / 2 < k := Nat.div_lt_of_lt_mul h2
            have hn2 : (2 * k) / 2 = k := Nat.mul_div_cancel_left k (by omega : 0 < 2)
            omega
          · have hmod : (c.1 - 1) % 2 = 0 ∨ (c.1 - 1) % 2 = 1 := by omega
            rcases hmod with hmod0 | hmod1 <;> [left; right] <;> omega
        obtain ⟨i, hi, hcol_eq⟩ := hcol_range
        -- The basement domino at index i contains c
        use { cell1 := (2 * i + 1, 1), cell2 := (2 * i + 2, 1),
              distinct := by simp,
              adjacent := by right; exact ⟨rfl, Or.inl rfl⟩ }
        constructor
        · simp only [Finset.mem_union, Finset.mem_singleton]
          left; left; left; left
          simp only [basementDominos, Finset.mem_map, Finset.mem_range, ← Function.Embedding.toFun_eq_coe]
          exact ⟨i, hi, rfl⟩
        · simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton]
          rcases hcol_eq with hcol | hcol
          · left; ext <;> simp [hrow1, hcol]
          · right; ext <;> simp [hrow1, hcol]
      · -- c.2 = 2: covered by leftWall, rightWall, or middleDominos
        rcases Nat.eq_or_lt_of_le hcol_ge with hcol_eq1 | hcol_gt1
        · -- c.1 = 1: covered by leftWall
          use leftWall
          constructor
          · simp only [Finset.mem_union, Finset.mem_singleton]
            left; left; left; right; trivial
          · simp only [leftWall, Domino.cells, Finset.mem_insert, Finset.mem_singleton]
            left; ext <;> simp [hrow2, hcol_eq1]
        · rcases Nat.eq_or_lt_of_le hcol_le with heq | hcol_lt_n
          · -- c.1 = n: covered by rightWall
            use rightWall n
            constructor
            · simp only [Finset.mem_union, Finset.mem_singleton]
              left; left; right; trivial
            · simp only [rightWall, Domino.cells, Finset.mem_insert, Finset.mem_singleton]
              left; ext <;> simp [heq, hrow2]
          · -- 1 < c.1 < n: covered by middleDominos
            have hcol_ge2 : c.1 ≥ 2 := by omega
            have hcol_le_nm1 : c.1 ≤ n - 1 := by omega
            have hcol_range : ∃ i < n / 2 - 1, c.1 = 2 * i + 2 ∨ c.1 = 2 * i + 3 := by
              use (c.1 - 2) / 2
              constructor
              · obtain ⟨k, hk⟩ := hn; subst hk
                have h2 : c.1 - 2 < 2 * k - 2 := by omega
                have hk_pos : k ≥ 1 := by omega
                have h3 : c.1 - 2 < 2 * (k - 1) := by omega
                have : (c.1 - 2) / 2 < k - 1 := Nat.div_lt_of_lt_mul h3
                have hn2 : (2 * k) / 2 - 1 = k - 1 := by
                  rw [Nat.mul_div_cancel_left k (by omega : 0 < 2)]
                omega
              · have hmod : (c.1 - 2) % 2 = 0 ∨ (c.1 - 2) % 2 = 1 := by omega
                rcases hmod with hmod0 | hmod1 <;> [left; right] <;> omega
            obtain ⟨i, hi, hcol_eq⟩ := hcol_range
            use { cell1 := (2 * i + 2, 2), cell2 := (2 * i + 3, 2),
                  distinct := by simp,
                  adjacent := by right; exact ⟨rfl, Or.inl rfl⟩ }
            constructor
            · simp only [Finset.mem_union, Finset.mem_singleton]
              left; right
              simp only [middleDominos, Finset.mem_map, Finset.mem_range, ← Function.Embedding.toFun_eq_coe]
              exact ⟨i, hi, rfl⟩
            · simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton]
              rcases hcol_eq with hcol | hcol
              · left; ext <;> simp [hrow2, hcol]
              · right; ext <;> simp [hrow2, hcol]
      · -- c.2 = 3: covered by leftWall, rightWall, or topDominos
        rcases Nat.eq_or_lt_of_le hcol_ge with hcol_eq1 | hcol_gt1
        · -- c.1 = 1: covered by leftWall
          use leftWall
          constructor
          · simp only [Finset.mem_union, Finset.mem_singleton]
            left; left; left; right; trivial
          · simp only [leftWall, Domino.cells, Finset.mem_insert, Finset.mem_singleton]
            right; ext <;> simp [hrow3, hcol_eq1]
        · rcases Nat.eq_or_lt_of_le hcol_le with heq | hcol_lt_n
          · -- c.1 = n: covered by rightWall
            use rightWall n
            constructor
            · simp only [Finset.mem_union, Finset.mem_singleton]
              left; left; right; trivial
            · simp only [rightWall, Domino.cells, Finset.mem_insert, Finset.mem_singleton]
              right; ext <;> simp [heq, hrow3]
          · -- 1 < c.1 < n: covered by topDominos
            have hcol_ge2 : c.1 ≥ 2 := by omega
            have hcol_le_nm1 : c.1 ≤ n - 1 := by omega
            have hcol_range : ∃ i < n / 2 - 1, c.1 = 2 * i + 2 ∨ c.1 = 2 * i + 3 := by
              use (c.1 - 2) / 2
              constructor
              · obtain ⟨k, hk⟩ := hn; subst hk
                have h2 : c.1 - 2 < 2 * k - 2 := by omega
                have hk_pos : k ≥ 1 := by omega
                have h3 : c.1 - 2 < 2 * (k - 1) := by omega
                have : (c.1 - 2) / 2 < k - 1 := Nat.div_lt_of_lt_mul h3
                have hn2 : (2 * k) / 2 - 1 = k - 1 := by
                  rw [Nat.mul_div_cancel_left k (by omega : 0 < 2)]
                omega
              · have hmod : (c.1 - 2) % 2 = 0 ∨ (c.1 - 2) % 2 = 1 := by omega
                rcases hmod with hmod0 | hmod1 <;> [left; right] <;> omega
            obtain ⟨i, hi, hcol_eq⟩ := hcol_range
            use { cell1 := (2 * i + 2, 3), cell2 := (2 * i + 3, 3),
                  distinct := by simp,
                  adjacent := by right; exact ⟨rfl, Or.inl rfl⟩ }
            constructor
            · simp only [Finset.mem_union, Finset.mem_singleton]
              right
              simp only [topDominos, Finset.mem_map, Finset.mem_range, ← Function.Embedding.toFun_eq_coe]
              exact ⟨i, hi, rfl⟩
            · simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton]
              rcases hcol_eq with hcol | hcol
              · left; ext <;> simp [hrow3, hcol]
              · right; ext <;> simp [hrow3, hcol]
  pairwise_disjoint := by
    intro d₁ hd₁ d₂ hd₂ hne
    simp only [Finset.mem_union, Finset.mem_singleton] at hd₁ hd₂
    -- Case analysis on which component d₁ and d₂ come from
    -- Components: basementDominos, {leftWall}, {rightWall n}, middleDominos, topDominos
    rcases hd₁ with ((((hd₁_base | hd₁_left) | hd₁_right) | hd₁_mid) | hd₁_top) <;>
    rcases hd₂ with ((((hd₂_base | hd₂_left) | hd₂_right) | hd₂_mid) | hd₂_top)
    -- Case 1: basement vs basement
    · simp only [basementDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_base hd₂_base
      obtain ⟨i₁, _, rfl⟩ := hd₁_base
      obtain ⟨i₂, _, rfl⟩ := hd₂_base
      simp only [Domino.cells]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      have hne' : i₁ ≠ i₂ := by intro h; apply hne; ext <;> simp [h]
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 2: basement vs leftWall (row 1 vs rows 2,3)
    · simp only [basementDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_base
      obtain ⟨i₁, _, rfl⟩ := hd₁_base
      subst hd₂_left
      simp only [Domino.cells, leftWall]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 3: basement vs rightWall (row 1 vs rows 2,3)
    · simp only [basementDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_base
      obtain ⟨i₁, _, rfl⟩ := hd₁_base
      subst hd₂_right
      simp only [Domino.cells, rightWall]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 4: basement vs middleDominos (row 1 vs row 2)
    · simp only [basementDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_base
      simp only [middleDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₂_mid
      obtain ⟨i₁, _, rfl⟩ := hd₁_base
      obtain ⟨i₂, _, rfl⟩ := hd₂_mid
      simp only [Domino.cells]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 5: basement vs topDominos (row 1 vs row 3)
    · simp only [basementDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_base
      simp only [topDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₂_top
      obtain ⟨i₁, _, rfl⟩ := hd₁_base
      obtain ⟨i₂, _, rfl⟩ := hd₂_top
      simp only [Domino.cells]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 6: leftWall vs basement (symmetric to case 2)
    · simp only [basementDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₂_base
      obtain ⟨i₂, _, rfl⟩ := hd₂_base
      subst hd₁_left
      simp only [Domino.cells, leftWall]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 7: leftWall vs leftWall (same element, contradicts hne)
    · subst hd₁_left hd₂_left; exact (hne rfl).elim
    -- Case 8: leftWall vs rightWall (column 1 vs column n)
    · subst hd₁_left hd₂_right
      simp only [Domino.cells, leftWall, rightWall]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 9: leftWall vs middleDominos (column 1 vs columns 2+)
    · simp only [middleDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₂_mid
      obtain ⟨i₂, _, rfl⟩ := hd₂_mid
      subst hd₁_left
      simp only [Domino.cells, leftWall]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 10: leftWall vs topDominos (column 1 vs columns 2+)
    · simp only [topDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₂_top
      obtain ⟨i₂, _, rfl⟩ := hd₂_top
      subst hd₁_left
      simp only [Domino.cells, leftWall]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 11: rightWall vs basement
    · simp only [basementDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₂_base
      obtain ⟨i₂, _, rfl⟩ := hd₂_base
      subst hd₁_right
      simp only [Domino.cells, rightWall]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 12: rightWall vs leftWall
    · subst hd₁_right hd₂_left
      simp only [Domino.cells, leftWall, rightWall]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 13: rightWall vs rightWall
    · subst hd₁_right hd₂_right; exact (hne rfl).elim
    -- Case 14: rightWall vs middleDominos (column n vs columns ≤n-1)
    · simp only [middleDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₂_mid
      obtain ⟨i₂, hi₂, rfl⟩ := hd₂_mid
      subst hd₁_right
      simp only [Domino.cells, rightWall]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      obtain ⟨k, hk⟩ := hn; subst hk
      have hk_pos : k ≥ 1 := by omega
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 15: rightWall vs topDominos (column n vs columns ≤n-1)
    · simp only [topDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₂_top
      obtain ⟨i₂, hi₂, rfl⟩ := hd₂_top
      subst hd₁_right
      simp only [Domino.cells, rightWall]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      obtain ⟨k, hk⟩ := hn; subst hk
      have hk_pos : k ≥ 1 := by omega
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 16: middleDominos vs basement
    · simp only [basementDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₂_base
      simp only [middleDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_mid
      obtain ⟨i₁, _, rfl⟩ := hd₁_mid
      obtain ⟨i₂, _, rfl⟩ := hd₂_base
      simp only [Domino.cells]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 17: middleDominos vs leftWall
    · simp only [middleDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_mid
      obtain ⟨i₁, _, rfl⟩ := hd₁_mid
      subst hd₂_left
      simp only [Domino.cells, leftWall]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 18: middleDominos vs rightWall
    · simp only [middleDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_mid
      obtain ⟨i₁, hi₁, rfl⟩ := hd₁_mid
      subst hd₂_right
      simp only [Domino.cells, rightWall]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      obtain ⟨k, hk⟩ := hn; subst hk
      have hk_pos : k ≥ 1 := by omega
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 19: middleDominos vs middleDominos
    · simp only [middleDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_mid hd₂_mid
      obtain ⟨i₁, _, rfl⟩ := hd₁_mid
      obtain ⟨i₂, _, rfl⟩ := hd₂_mid
      simp only [Domino.cells]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      have hne' : i₁ ≠ i₂ := by intro h; apply hne; ext <;> simp [h]
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 20: middleDominos vs topDominos (row 2 vs row 3)
    · simp only [middleDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_mid
      simp only [topDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₂_top
      obtain ⟨i₁, _, rfl⟩ := hd₁_mid
      obtain ⟨i₂, _, rfl⟩ := hd₂_top
      simp only [Domino.cells]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 21: topDominos vs basement
    · simp only [basementDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₂_base
      simp only [topDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_top
      obtain ⟨i₁, _, rfl⟩ := hd₁_top
      obtain ⟨i₂, _, rfl⟩ := hd₂_base
      simp only [Domino.cells]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 22: topDominos vs leftWall
    · simp only [topDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_top
      obtain ⟨i₁, _, rfl⟩ := hd₁_top
      subst hd₂_left
      simp only [Domino.cells, leftWall]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 23: topDominos vs rightWall
    · simp only [topDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_top
      obtain ⟨i₁, hi₁, rfl⟩ := hd₁_top
      subst hd₂_right
      simp only [Domino.cells, rightWall]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      obtain ⟨k, hk⟩ := hn; subst hk
      have hk_pos : k ≥ 1 := by omega
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 24: topDominos vs middleDominos
    · simp only [topDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_top
      simp only [middleDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₂_mid
      obtain ⟨i₁, _, rfl⟩ := hd₁_top
      obtain ⟨i₂, _, rfl⟩ := hd₂_mid
      simp only [Domino.cells]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 25: topDominos vs topDominos
    · simp only [topDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_top hd₂_top
      obtain ⟨i₁, _, rfl⟩ := hd₁_top
      obtain ⟨i₂, _, rfl⟩ := hd₂_top
      simp only [Domino.cells]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      have hne' : i₁ ≠ i₂ := by intro h; apply hne; ext <;> simp [h]
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega


def basementDominosB (n : ℕ) : Finset Domino :=
  (Finset.range (n / 2)).map ⟨fun i =>
    { cell1 := (2 * i + 1, 3)
      cell2 := (2 * i + 2, 3)
      distinct := by simp only [ne_eq, Prod.mk.injEq, and_true]; omega
      adjacent := by right; exact ⟨rfl, Or.inl rfl⟩ }, by
    intro a b hab
    simp only [Domino.mk.injEq, Prod.mk.injEq] at hab
    omega⟩


def leftWallB : Domino where
  cell1 := (1, 2)
  cell2 := (1, 1)
  distinct := by simp only [ne_eq, Prod.mk.injEq, true_and]; omega
  adjacent := by left; exact ⟨rfl, Or.inr rfl⟩


def rightWallB (n : ℕ) : Domino where
  cell1 := (n, 2)
  cell2 := (n, 1)
  distinct := by simp only [ne_eq, Prod.mk.injEq, true_and]; omega
  adjacent := by left; exact ⟨rfl, Or.inr rfl⟩


def bottomDominosB (n : ℕ) : Finset Domino :=
  (Finset.range (n / 2 - 1)).map ⟨fun i =>
    { cell1 := (2 * i + 2, 1)
      cell2 := (2 * i + 3, 1)
      distinct := by simp only [ne_eq, Prod.mk.injEq, and_true]; omega
      adjacent := by right; exact ⟨rfl, Or.inl rfl⟩ }, by
    intro a b hab
    simp only [Domino.mk.injEq, Prod.mk.injEq] at hab
    omega⟩


def TilingB (n : ℕ) (hn : Even n) (hn_ge : n ≥ 2) : DominoTiling n 3 where
  dominos := basementDominosB n ∪ {leftWallB} ∪ {rightWallB n} ∪
             middleDominos n ∪ bottomDominosB n
  dominos_in_rect := by
    intro d hd c hc_in_d
    simp only [Finset.mem_union, Finset.mem_singleton] at hd
    rcases hd with ((((hd | hd) | hd) | hd) | hd)
    · -- d ∈ basementDominosB n (row 3)
      simp only [basementDominosB, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd
      obtain ⟨i, hi, hd_eq⟩ := hd
      simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d
      have hcell1 : d.cell1 = (2 * i + 1, 3) := by rw [← hd_eq]
      have hcell2 : d.cell2 = (2 * i + 2, 3) := by rw [← hd_eq]
      rcases hc_in_d with hc1 | hc2
      · rw [hc1, hcell1, mem_Rectangle]
        refine ⟨?_, ?_, ?_, ?_⟩
        · omega
        · have h1 : 2 * i + 1 ≤ 2 * (n / 2) := by omega
          have h2 : 2 * (n / 2) ≤ n := by rw [mul_comm]; exact Nat.div_mul_le_self n 2
          omega
        · omega
        · omega
      · rw [hc2, hcell2, mem_Rectangle]
        refine ⟨?_, ?_, ?_, ?_⟩
        · omega
        · have h1 : 2 * i + 2 ≤ 2 * (n / 2) := by
            have : i + 1 ≤ n / 2 := hi
            omega
          have h2 : 2 * (n / 2) ≤ n := by rw [mul_comm]; exact Nat.div_mul_le_self n 2
          omega
        · omega
        · omega
    · -- d = leftWallB (rows 1-2, column 1)
      subst hd
      simp only [leftWallB, Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d
      rcases hc_in_d with rfl | rfl
      · rw [mem_Rectangle]; omega
      · rw [mem_Rectangle]; omega
    · -- d = rightWallB n (rows 1-2, column n)
      subst hd
      simp only [rightWallB, Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d
      rcases hc_in_d with rfl | rfl
      · rw [mem_Rectangle]; omega
      · rw [mem_Rectangle]; omega
    · -- d ∈ middleDominos n (row 2)
      simp only [middleDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd
      obtain ⟨i, hi, hd_eq⟩ := hd
      simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d
      have hcell1 : d.cell1 = (2 * i + 2, 2) := by rw [← hd_eq]
      have hcell2 : d.cell2 = (2 * i + 3, 2) := by rw [← hd_eq]
      rcases hc_in_d with hc1 | hc2
      · rw [hc1, hcell1, mem_Rectangle]
        refine ⟨?_, ?_, ?_, ?_⟩
        · omega
        · have h1 : 2 * i + 2 ≤ 2 * (n / 2 - 1) + 1 := by omega
          have h2 : 2 * (n / 2 - 1) + 1 ≤ n - 1 := by
            obtain ⟨k, hk⟩ := hn
            subst hk
            have hk_pos : k ≥ 1 := by omega
            omega
          omega
        · omega
        · omega
      · rw [hc2, hcell2, mem_Rectangle]
        refine ⟨?_, ?_, ?_, ?_⟩
        · omega
        · have h1 : 2 * i + 3 ≤ 2 * (n / 2 - 1) + 2 := by omega
          have h2 : 2 * (n / 2 - 1) + 2 ≤ n := by
            obtain ⟨k, hk⟩ := hn
            subst hk
            have hk_pos : k ≥ 1 := by omega
            omega
          omega
        · omega
        · omega
    · -- d ∈ bottomDominosB n (row 1)
      simp only [bottomDominosB, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd
      obtain ⟨i, hi, hd_eq⟩ := hd
      simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d
      have hcell1 : d.cell1 = (2 * i + 2, 1) := by rw [← hd_eq]
      have hcell2 : d.cell2 = (2 * i + 3, 1) := by rw [← hd_eq]
      rcases hc_in_d with hc1 | hc2
      · rw [hc1, hcell1, mem_Rectangle]
        refine ⟨?_, ?_, ?_, ?_⟩
        · omega
        · have h1 : 2 * i + 2 ≤ 2 * (n / 2 - 1) + 1 := by omega
          have h2 : 2 * (n / 2 - 1) + 1 ≤ n - 1 := by
            obtain ⟨k, hk⟩ := hn
            subst hk
            have hk_pos : k ≥ 1 := by omega
            omega
          omega
        · omega
        · omega
      · rw [hc2, hcell2, mem_Rectangle]
        refine ⟨?_, ?_, ?_, ?_⟩
        · omega
        · have h1 : 2 * i + 3 ≤ 2 * (n / 2 - 1) + 2 := by omega
          have h2 : 2 * (n / 2 - 1) + 2 ≤ n := by
            obtain ⟨k, hk⟩ := hn
            subst hk
            have hk_pos : k ≥ 1 := by omega
            omega
          omega
        · omega
        · omega
  covers_all := by
    ext c
    simp only [Finset.mem_biUnion]
    constructor
    · -- c in biUnion → c in Rectangle (from dominos_in_rect)
      rintro ⟨d, hd_mem, hc_in_d⟩
      simp only [Finset.mem_union, Finset.mem_singleton] at hd_mem
      rcases hd_mem with ((((hd | hd) | hd) | hd) | hd)
      · -- d ∈ basementDominosB n
        simp only [basementDominosB, Finset.mem_map, Finset.mem_range,
          ← Function.Embedding.toFun_eq_coe] at hd
        obtain ⟨i, hi, hd_eq⟩ := hd
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d
        have hcell1 : d.cell1 = (2 * i + 1, 3) := by rw [← hd_eq]
        have hcell2 : d.cell2 = (2 * i + 2, 3) := by rw [← hd_eq]
        rcases hc_in_d with hc1 | hc2
        · rw [hc1, hcell1, mem_Rectangle]
          refine ⟨?_, ?_, ?_, ?_⟩
          · omega
          · have h1 : 2 * i + 1 ≤ 2 * (n / 2) := by omega
            have h2 : 2 * (n / 2) ≤ n := by rw [mul_comm]; exact Nat.div_mul_le_self n 2
            omega
          · omega
          · omega
        · rw [hc2, hcell2, mem_Rectangle]
          refine ⟨?_, ?_, ?_, ?_⟩
          · omega
          · have h1 : 2 * i + 2 ≤ 2 * (n / 2) := by
              have : i + 1 ≤ n / 2 := hi
              omega
            have h2 : 2 * (n / 2) ≤ n := by rw [mul_comm]; exact Nat.div_mul_le_self n 2
            omega
          · omega
          · omega
      · -- d = leftWallB
        subst hd
        simp only [leftWallB, Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d
        rcases hc_in_d with rfl | rfl
        · rw [mem_Rectangle]; omega
        · rw [mem_Rectangle]; omega
      · -- d = rightWallB n
        subst hd
        simp only [rightWallB, Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d
        rcases hc_in_d with rfl | rfl
        · rw [mem_Rectangle]; omega
        · rw [mem_Rectangle]; omega
      · -- d ∈ middleDominos n
        simp only [middleDominos, Finset.mem_map, Finset.mem_range,
          ← Function.Embedding.toFun_eq_coe] at hd
        obtain ⟨i, hi, hd_eq⟩ := hd
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d
        have hcell1 : d.cell1 = (2 * i + 2, 2) := by rw [← hd_eq]
        have hcell2 : d.cell2 = (2 * i + 3, 2) := by rw [← hd_eq]
        rcases hc_in_d with hc1 | hc2
        · rw [hc1, hcell1, mem_Rectangle]
          refine ⟨?_, ?_, ?_, ?_⟩
          · omega
          · have h1 : 2 * i + 2 ≤ 2 * (n / 2 - 1) + 1 := by omega
            have h2 : 2 * (n / 2 - 1) + 1 ≤ n - 1 := by
              obtain ⟨k, hk⟩ := hn
              subst hk
              have hk_pos : k ≥ 1 := by omega
              omega
            omega
          · omega
          · omega
        · rw [hc2, hcell2, mem_Rectangle]
          refine ⟨?_, ?_, ?_, ?_⟩
          · omega
          · have h1 : 2 * i + 3 ≤ 2 * (n / 2 - 1) + 2 := by omega
            have h2 : 2 * (n / 2 - 1) + 2 ≤ n := by
              obtain ⟨k, hk⟩ := hn
              subst hk
              have hk_pos : k ≥ 1 := by omega
              omega
            omega
          · omega
          · omega
      · -- d ∈ bottomDominosB n
        simp only [bottomDominosB, Finset.mem_map, Finset.mem_range,
          ← Function.Embedding.toFun_eq_coe] at hd
        obtain ⟨i, hi, hd_eq⟩ := hd
        simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc_in_d
        have hcell1 : d.cell1 = (2 * i + 2, 1) := by rw [← hd_eq]
        have hcell2 : d.cell2 = (2 * i + 3, 1) := by rw [← hd_eq]
        rcases hc_in_d with hc1 | hc2
        · rw [hc1, hcell1, mem_Rectangle]
          refine ⟨?_, ?_, ?_, ?_⟩
          · omega
          · have h1 : 2 * i + 2 ≤ 2 * (n / 2 - 1) + 1 := by omega
            have h2 : 2 * (n / 2 - 1) + 1 ≤ n - 1 := by
              obtain ⟨k, hk⟩ := hn
              subst hk
              have hk_pos : k ≥ 1 := by omega
              omega
            omega
          · omega
          · omega
        · rw [hc2, hcell2, mem_Rectangle]
          refine ⟨?_, ?_, ?_, ?_⟩
          · omega
          · have h1 : 2 * i + 3 ≤ 2 * (n / 2 - 1) + 2 := by omega
            have h2 : 2 * (n / 2 - 1) + 2 ≤ n := by
              obtain ⟨k, hk⟩ := hn
              subst hk
              have hk_pos : k ≥ 1 := by omega
              omega
            omega
          · omega
          · omega
    · -- c in Rectangle → c in biUnion
      intro hc
      rw [mem_Rectangle] at hc
      obtain ⟨hcol_ge, hcol_le, hrow_ge, hrow_le⟩ := hc
      have hrow : c.2 = 1 ∨ c.2 = 2 ∨ c.2 = 3 := by omega
      rcases hrow with hrow1 | hrow2 | hrow3
      · -- c.2 = 1: covered by leftWallB, rightWallB, or bottomDominosB
        rcases Nat.eq_or_lt_of_le hcol_ge with hcol_eq1 | hcol_gt1
        · -- c.1 = 1: covered by leftWallB
          use leftWallB
          constructor
          · simp only [Finset.mem_union, Finset.mem_singleton]
            left; left; left; right; trivial
          · simp only [leftWallB, Domino.cells, Finset.mem_insert, Finset.mem_singleton]
            right; ext <;> simp [hrow1, hcol_eq1]
        · rcases Nat.eq_or_lt_of_le hcol_le with heq | hcol_lt_n
          · -- c.1 = n: covered by rightWallB
            use rightWallB n
            constructor
            · simp only [Finset.mem_union, Finset.mem_singleton]
              left; left; right; trivial
            · simp only [rightWallB, Domino.cells, Finset.mem_insert, Finset.mem_singleton]
              right; ext <;> simp [heq, hrow1]
          · -- 1 < c.1 < n: covered by bottomDominosB
            have hcol_ge2 : c.1 ≥ 2 := by omega
            have hcol_le_nm1 : c.1 ≤ n - 1 := by omega
            have hcol_range : ∃ i < n / 2 - 1, c.1 = 2 * i + 2 ∨ c.1 = 2 * i + 3 := by
              use (c.1 - 2) / 2
              constructor
              · obtain ⟨k, hk⟩ := hn; subst hk
                have h2 : c.1 - 2 < 2 * k - 2 := by omega
                have hk_pos : k ≥ 1 := by omega
                have h3 : c.1 - 2 < 2 * (k - 1) := by omega
                have : (c.1 - 2) / 2 < k - 1 := Nat.div_lt_of_lt_mul h3
                have hn2 : (2 * k) / 2 - 1 = k - 1 := by
                  rw [Nat.mul_div_cancel_left k (by omega : 0 < 2)]
                omega
              · have hmod : (c.1 - 2) % 2 = 0 ∨ (c.1 - 2) % 2 = 1 := by omega
                rcases hmod with hmod0 | hmod1 <;> [left; right] <;> omega
            obtain ⟨i, hi, hcol_eq⟩ := hcol_range
            use { cell1 := (2 * i + 2, 1), cell2 := (2 * i + 3, 1),
                  distinct := by simp,
                  adjacent := by right; exact ⟨rfl, Or.inl rfl⟩ }
            constructor
            · simp only [Finset.mem_union, Finset.mem_singleton]
              right
              simp only [bottomDominosB, Finset.mem_map, Finset.mem_range, ← Function.Embedding.toFun_eq_coe]
              exact ⟨i, hi, rfl⟩
            · simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton]
              rcases hcol_eq with hcol | hcol
              · left; ext <;> simp [hrow1, hcol]
              · right; ext <;> simp [hrow1, hcol]
      · -- c.2 = 2: covered by leftWallB, rightWallB, or middleDominos
        rcases Nat.eq_or_lt_of_le hcol_ge with hcol_eq1 | hcol_gt1
        · -- c.1 = 1: covered by leftWallB
          use leftWallB
          constructor
          · simp only [Finset.mem_union, Finset.mem_singleton]
            left; left; left; right; trivial
          · simp only [leftWallB, Domino.cells, Finset.mem_insert, Finset.mem_singleton]
            left; ext <;> simp [hrow2, hcol_eq1]
        · rcases Nat.eq_or_lt_of_le hcol_le with heq | hcol_lt_n
          · -- c.1 = n: covered by rightWallB
            use rightWallB n
            constructor
            · simp only [Finset.mem_union, Finset.mem_singleton]
              left; left; right; trivial
            · simp only [rightWallB, Domino.cells, Finset.mem_insert, Finset.mem_singleton]
              left; ext <;> simp [heq, hrow2]
          · -- 1 < c.1 < n: covered by middleDominos
            have hcol_ge2 : c.1 ≥ 2 := by omega
            have hcol_le_nm1 : c.1 ≤ n - 1 := by omega
            have hcol_range : ∃ i < n / 2 - 1, c.1 = 2 * i + 2 ∨ c.1 = 2 * i + 3 := by
              use (c.1 - 2) / 2
              constructor
              · obtain ⟨k, hk⟩ := hn; subst hk
                have h2 : c.1 - 2 < 2 * k - 2 := by omega
                have hk_pos : k ≥ 1 := by omega
                have h3 : c.1 - 2 < 2 * (k - 1) := by omega
                have : (c.1 - 2) / 2 < k - 1 := Nat.div_lt_of_lt_mul h3
                have hn2 : (2 * k) / 2 - 1 = k - 1 := by
                  rw [Nat.mul_div_cancel_left k (by omega : 0 < 2)]
                omega
              · have hmod : (c.1 - 2) % 2 = 0 ∨ (c.1 - 2) % 2 = 1 := by omega
                rcases hmod with hmod0 | hmod1 <;> [left; right] <;> omega
            obtain ⟨i, hi, hcol_eq⟩ := hcol_range
            use { cell1 := (2 * i + 2, 2), cell2 := (2 * i + 3, 2),
                  distinct := by simp,
                  adjacent := by right; exact ⟨rfl, Or.inl rfl⟩ }
            constructor
            · simp only [Finset.mem_union, Finset.mem_singleton]
              left; right
              simp only [middleDominos, Finset.mem_map, Finset.mem_range, ← Function.Embedding.toFun_eq_coe]
              exact ⟨i, hi, rfl⟩
            · simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton]
              rcases hcol_eq with hcol | hcol
              · left; ext <;> simp [hrow2, hcol]
              · right; ext <;> simp [hrow2, hcol]
      · -- c.2 = 3: covered by basementDominosB
        have hcol_range : ∃ i < n / 2, c.1 = 2 * i + 1 ∨ c.1 = 2 * i + 2 := by
          use (c.1 - 1) / 2
          constructor
          · obtain ⟨k, hk⟩ := hn; subst hk
            have h2 : c.1 - 1 < 2 * k := by omega
            have : (c.1 - 1) / 2 < k := Nat.div_lt_of_lt_mul h2
            have hn2 : (2 * k) / 2 = k := Nat.mul_div_cancel_left k (by omega : 0 < 2)
            omega
          · have hmod : (c.1 - 1) % 2 = 0 ∨ (c.1 - 1) % 2 = 1 := by omega
            rcases hmod with hmod0 | hmod1 <;> [left; right] <;> omega
        obtain ⟨i, hi, hcol_eq⟩ := hcol_range
        use { cell1 := (2 * i + 1, 3), cell2 := (2 * i + 2, 3),
              distinct := by simp,
              adjacent := by right; exact ⟨rfl, Or.inl rfl⟩ }
        constructor
        · simp only [Finset.mem_union, Finset.mem_singleton]
          left; left; left; left
          simp only [basementDominosB, Finset.mem_map, Finset.mem_range, ← Function.Embedding.toFun_eq_coe]
          exact ⟨i, hi, rfl⟩
        · simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton]
          rcases hcol_eq with hcol | hcol
          · left; ext <;> simp [hrow3, hcol]
          · right; ext <;> simp [hrow3, hcol]
  pairwise_disjoint := by
    intro d₁ hd₁ d₂ hd₂ hne
    simp only [Finset.mem_union, Finset.mem_singleton] at hd₁ hd₂
    -- Components: basementDominosB, {leftWallB}, {rightWallB n}, middleDominos, bottomDominosB
    rcases hd₁ with ((((hd₁_base | hd₁_left) | hd₁_right) | hd₁_mid) | hd₁_bot) <;>
    rcases hd₂ with ((((hd₂_base | hd₂_left) | hd₂_right) | hd₂_mid) | hd₂_bot)
    -- Case 1: basementB vs basementB
    · simp only [basementDominosB, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_base hd₂_base
      obtain ⟨i₁, _, rfl⟩ := hd₁_base
      obtain ⟨i₂, _, rfl⟩ := hd₂_base
      simp only [Domino.cells]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      have hne' : i₁ ≠ i₂ := by intro h; apply hne; ext <;> simp [h]
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 2: basementB vs leftWallB (row 3 vs rows 1,2)
    · simp only [basementDominosB, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_base
      obtain ⟨i₁, _, rfl⟩ := hd₁_base
      subst hd₂_left
      simp only [Domino.cells, leftWallB]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 3: basementB vs rightWallB (row 3 vs rows 1,2)
    · simp only [basementDominosB, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_base
      obtain ⟨i₁, _, rfl⟩ := hd₁_base
      subst hd₂_right
      simp only [Domino.cells, rightWallB]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 4: basementB vs middleDominos (row 3 vs row 2)
    · simp only [basementDominosB, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_base
      simp only [middleDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₂_mid
      obtain ⟨i₁, _, rfl⟩ := hd₁_base
      obtain ⟨i₂, _, rfl⟩ := hd₂_mid
      simp only [Domino.cells]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 5: basementB vs bottomB (row 3 vs row 1)
    · simp only [basementDominosB, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_base
      simp only [bottomDominosB, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₂_bot
      obtain ⟨i₁, _, rfl⟩ := hd₁_base
      obtain ⟨i₂, _, rfl⟩ := hd₂_bot
      simp only [Domino.cells]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 6: leftWallB vs basementB
    · simp only [basementDominosB, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₂_base
      obtain ⟨i₂, _, rfl⟩ := hd₂_base
      subst hd₁_left
      simp only [Domino.cells, leftWallB]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 7: leftWallB vs leftWallB
    · subst hd₁_left hd₂_left; exact (hne rfl).elim
    -- Case 8: leftWallB vs rightWallB
    · subst hd₁_left hd₂_right
      simp only [Domino.cells, leftWallB, rightWallB]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 9: leftWallB vs middleDominos
    · simp only [middleDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₂_mid
      obtain ⟨i₂, _, rfl⟩ := hd₂_mid
      subst hd₁_left
      simp only [Domino.cells, leftWallB]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 10: leftWallB vs bottomB
    · simp only [bottomDominosB, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₂_bot
      obtain ⟨i₂, _, rfl⟩ := hd₂_bot
      subst hd₁_left
      simp only [Domino.cells, leftWallB]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 11: rightWallB vs basementB
    · simp only [basementDominosB, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₂_base
      obtain ⟨i₂, _, rfl⟩ := hd₂_base
      subst hd₁_right
      simp only [Domino.cells, rightWallB]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 12: rightWallB vs leftWallB
    · subst hd₁_right hd₂_left
      simp only [Domino.cells, leftWallB, rightWallB]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 13: rightWallB vs rightWallB
    · subst hd₁_right hd₂_right; exact (hne rfl).elim
    -- Case 14: rightWallB vs middleDominos
    · simp only [middleDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₂_mid
      obtain ⟨i₂, hi₂, rfl⟩ := hd₂_mid
      subst hd₁_right
      simp only [Domino.cells, rightWallB]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      obtain ⟨k, hk⟩ := hn; subst hk
      have hk_pos : k ≥ 1 := by omega
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 15: rightWallB vs bottomB
    · simp only [bottomDominosB, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₂_bot
      obtain ⟨i₂, hi₂, rfl⟩ := hd₂_bot
      subst hd₁_right
      simp only [Domino.cells, rightWallB]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      obtain ⟨k, hk⟩ := hn; subst hk
      have hk_pos : k ≥ 1 := by omega
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 16: middleDominos vs basementB
    · simp only [basementDominosB, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₂_base
      simp only [middleDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_mid
      obtain ⟨i₁, _, rfl⟩ := hd₁_mid
      obtain ⟨i₂, _, rfl⟩ := hd₂_base
      simp only [Domino.cells]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 17: middleDominos vs leftWallB
    · simp only [middleDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_mid
      obtain ⟨i₁, _, rfl⟩ := hd₁_mid
      subst hd₂_left
      simp only [Domino.cells, leftWallB]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 18: middleDominos vs rightWallB
    · simp only [middleDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_mid
      obtain ⟨i₁, hi₁, rfl⟩ := hd₁_mid
      subst hd₂_right
      simp only [Domino.cells, rightWallB]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      obtain ⟨k, hk⟩ := hn; subst hk
      have hk_pos : k ≥ 1 := by omega
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 19: middleDominos vs middleDominos
    · simp only [middleDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_mid hd₂_mid
      obtain ⟨i₁, _, rfl⟩ := hd₁_mid
      obtain ⟨i₂, _, rfl⟩ := hd₂_mid
      simp only [Domino.cells]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      have hne' : i₁ ≠ i₂ := by intro h; apply hne; ext <;> simp [h]
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 20: middleDominos vs bottomB (row 2 vs row 1)
    · simp only [middleDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_mid
      simp only [bottomDominosB, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₂_bot
      obtain ⟨i₁, _, rfl⟩ := hd₁_mid
      obtain ⟨i₂, _, rfl⟩ := hd₂_bot
      simp only [Domino.cells]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 21: bottomB vs basementB
    · simp only [basementDominosB, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₂_base
      simp only [bottomDominosB, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_bot
      obtain ⟨i₁, _, rfl⟩ := hd₁_bot
      obtain ⟨i₂, _, rfl⟩ := hd₂_base
      simp only [Domino.cells]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 22: bottomB vs leftWallB
    · simp only [bottomDominosB, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_bot
      obtain ⟨i₁, _, rfl⟩ := hd₁_bot
      subst hd₂_left
      simp only [Domino.cells, leftWallB]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 23: bottomB vs rightWallB
    · simp only [bottomDominosB, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_bot
      obtain ⟨i₁, hi₁, rfl⟩ := hd₁_bot
      subst hd₂_right
      simp only [Domino.cells, rightWallB]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      obtain ⟨k, hk⟩ := hn; subst hk
      have hk_pos : k ≥ 1 := by omega
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 24: bottomB vs middleDominos
    · simp only [bottomDominosB, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_bot
      simp only [middleDominos, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₂_mid
      obtain ⟨i₁, _, rfl⟩ := hd₁_bot
      obtain ⟨i₂, _, rfl⟩ := hd₂_mid
      simp only [Domino.cells]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega
    -- Case 25: bottomB vs bottomB
    · simp only [bottomDominosB, Finset.mem_map, Finset.mem_range,
        ← Function.Embedding.toFun_eq_coe] at hd₁_bot hd₂_bot
      obtain ⟨i₁, _, rfl⟩ := hd₁_bot
      obtain ⟨i₂, _, rfl⟩ := hd₂_bot
      simp only [Domino.cells]
      rw [Finset.disjoint_iff_ne]
      intro c hc1 c' hc2 heq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2
      have hne' : i₁ ≠ i₂ := by intro h; apply hne; ext <;> simp [h]
      rcases hc1 with rfl | rfl <;> rcases hc2 with rfl | rfl <;>
      simp only [Prod.mk.injEq] at heq <;> omega


def TilingC : DominoTiling 2 3 where
  dominos := {
    { cell1 := (1, 1), cell2 := (2, 1),
      distinct := by decide,
      adjacent := by right; exact ⟨rfl, Or.inl rfl⟩ },
    { cell1 := (1, 2), cell2 := (2, 2),
      distinct := by decide,
      adjacent := by right; exact ⟨rfl, Or.inl rfl⟩ },
    { cell1 := (1, 3), cell2 := (2, 3),
      distinct := by decide,
      adjacent := by right; exact ⟨rfl, Or.inl rfl⟩ }
  }
  dominos_in_rect := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl <;>
    · intro c hc
      simp only [Domino.cells, Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with rfl | rfl <;> rw [mem_Rectangle] <;> simp
  covers_all := by
    ext c
    simp only [Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton, Domino.cells]
    constructor
    · intro ⟨d, hd_mem, hc⟩
      rcases hd_mem with rfl | rfl | rfl <;>
        rcases hc with rfl | rfl <;> rw [mem_Rectangle] <;> decide
    · intro hc
      rw [mem_Rectangle] at hc
      have h1 : c.1 = 1 ∨ c.1 = 2 := by omega
      have h2 : c.2 = 1 ∨ c.2 = 2 ∨ c.2 = 3 := by omega
      obtain ⟨c1, c2⟩ := c
      simp only at h1 h2 hc
      rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl | rfl
      · use ⟨(1, 1), (2, 1), by decide, by right; exact ⟨rfl, Or.inl rfl⟩⟩
        constructor; left; rfl; simp
      · use ⟨(1, 2), (2, 2), by decide, by right; exact ⟨rfl, Or.inl rfl⟩⟩
        constructor; right; left; rfl; simp
      · use ⟨(1, 3), (2, 3), by decide, by right; exact ⟨rfl, Or.inl rfl⟩⟩
        constructor; right; right; rfl; simp
      · use ⟨(1, 1), (2, 1), by decide, by right; exact ⟨rfl, Or.inl rfl⟩⟩
        constructor; left; rfl; simp
      · use ⟨(1, 2), (2, 2), by decide, by right; exact ⟨rfl, Or.inl rfl⟩⟩
        constructor; right; left; rfl; simp
      · use ⟨(1, 3), (2, 3), by decide, by right; exact ⟨rfl, Or.inl rfl⟩⟩
        constructor; right; right; rfl; simp
  pairwise_disjoint := by
    intro d1 hd1 d2 hd2 hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd1 hd2
    rcases hd1 with rfl | rfl | rfl <;> rcases hd2 with rfl | rfl | rfl <;>
      try exact absurd rfl hne
    all_goals (simp only [Domino.cells]; rw [Finset.disjoint_iff_ne]; decide)


def reflectCell3 (c : Cell) : Cell := (c.1, 4 - c.2)


end DominoTilings
