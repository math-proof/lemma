/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.GroupTheory.Perm.Fin
import Def.Combinatorics.Enumerative.Stirling.Part4
import Lemma.Finset.Enumerative.Stirling
import Def.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part22
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

theorem zagMergeOrder_symm_apply {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) (x : Fin n) :
    (zagMergeOrder e π m).symm (e x) =
      (zagBlockSwap m.first m.middle m.third
        m.first_lt_middle m.middle_lt_third).symm x := by
  let B := zagBlockSwap m.first m.middle m.third
    m.first_lt_middle m.middle_lt_third
  change ((e * B)⁻¹) (e x) = B⁻¹ x
  rw [mul_inv_rev, Equiv.Perm.mul_apply]
  change B.symm (e.symm (e x)) = B.symm x
  rw [e.symm_apply_apply]

theorem zagMergeVertical_sameCycles {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) :
    let π' := zagMergeVertical e π m
    π'.SameCycle (e m.first) (e m.middle) ∧
      π'.SameCycle (e m.first) (e m.third) := by
  obtain ⟨hfm, hft, hmt⟩ := zagMarkedTriple_pairwise m
  exact zagTriangle_merge_sameCycles π hfm hft hmt

theorem zagMergeVertical_apply_point {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) :
    zagMergeVertical e π m (zagMergePoint e π m) = e m.third := by
  exact Equiv.apply_symm_apply _ _

theorem zagMergePoint_eq_middle_of_fixed {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π)
    (hfix : π.symm (e m.third) = e m.third) :
    zagMergePoint e π m = e m.middle := by
  have hfm : e m.first ≠ e m.middle :=
    e.injective.ne (ne_of_lt m.first_lt_middle)
  have hft : e m.first ≠ e m.third :=
    e.injective.ne (ne_of_lt (m.first_lt_middle.trans m.middle_lt_third))
  have hmt : e m.middle ≠ e m.third :=
    e.injective.ne (ne_of_lt m.middle_lt_third)
  rw [zagMergePoint, zagMergeVertical]
  change (zagTriangle (e m.first) (e m.middle) (e m.third))⁻¹
      (π.symm (e m.third)) = e m.middle
  rw [zagTriangle_inv hfm hft hmt, hfix,
    zagTriangle_apply_middle]

theorem zagMergePoint_eq_preimage_of_not_fixed {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π)
    (hfix : π.symm (e m.third) ≠ e m.third) :
    zagMergePoint e π m = π.symm (e m.third) := by
  let y := π.symm (e m.third)
  have hyc : π.SameCycle y (e m.third) := by
    have h := (Equiv.Perm.SameCycle.rfl : π.SameCycle y y).apply_left
    simpa [y] using h.symm
  obtain ⟨hfm_cycle, hft_cycle, hmt_cycle⟩ := zagMarkedTriple_pairwise m
  have hyf : y ≠ e m.first := fun hy => hft_cycle (by simpa [hy] using hyc)
  have hym : y ≠ e m.middle := fun hy => hmt_cycle (by simpa [hy] using hyc)
  have hyt : y ≠ e m.third := hfix
  have hfm : e m.first ≠ e m.middle :=
    e.injective.ne (ne_of_lt m.first_lt_middle)
  have hft : e m.first ≠ e m.third :=
    e.injective.ne (ne_of_lt (m.first_lt_middle.trans m.middle_lt_third))
  have hmt : e m.middle ≠ e m.third :=
    e.injective.ne (ne_of_lt m.middle_lt_third)
  rw [zagMergePoint, zagMergeVertical]
  change (zagTriangle (e m.first) (e m.middle) (e m.third))⁻¹ y = y
  rw [zagTriangle_inv hfm hft hmt,
    zagTriangle_apply_of_ne hyf hyt hym]

theorem zagMergePoint_nontrivialAntiExceedance {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) :
    zagNontrivialAntiExceedance (zagMergeOrder e π m)
      (zagMergeVertical e π m) (zagMergePoint e π m) := by
  let e' := zagMergeOrder e π m
  let π' := zagMergeVertical e π m
  let ε := zagMergePoint e π m
  let q := zagBlockMiddle m.first m.middle m.third
    m.first_lt_middle m.middle_lt_third
  have hq := zagBlockMiddle_bounds m.first m.middle m.third
    m.first_lt_middle m.middle_lt_third
  have hpos_first : e'.symm (e m.first) = m.first := by
    change (zagMergeOrder e π m).symm (e m.first) = m.first
    rw [zagMergeOrder_symm_apply,
      zagBlockSwap_symm_apply_left]
  have hpos_middle : e'.symm (e m.middle) = m.third := by
    change (zagMergeOrder e π m).symm (e m.middle) = m.third
    rw [zagMergeOrder_symm_apply,
      zagBlockSwap_symm_apply_middle]
  have hpos_third : e'.symm (e m.third) = q := by
    change (zagMergeOrder e π m).symm (e m.third) = q
    rw [zagMergeOrder_symm_apply,
      zagBlockSwap_symm_apply_right]
  have happ : π' ε = e m.third := by
    exact zagMergeVertical_apply_point e π m
  constructor
  · intro hexc
    simp only [zagExceedance] at hexc
    change e'.symm ε < e'.symm (π' ε) at hexc
    rw [happ, hpos_third] at hexc
    by_cases hfix : π.symm (e m.third) = e m.third
    · have hε := zagMergePoint_eq_middle_of_fixed e π m hfix
      change ε = e m.middle at hε
      rw [hε, hpos_middle] at hexc
      exact (not_lt_of_ge hq.2.le) hexc
    · let y := π.symm (e m.third)
      have hyc : π.SameCycle y (e m.third) := by
        have h := (Equiv.Perm.SameCycle.rfl : π.SameCycle y y).apply_left
        simpa [y] using h.symm
      have hmin := zagCycleMinPos_le e π hyc
      have hthird := (zag_mem_cycleMinima_iff e π m.third).mp m.third_mem
      rw [hthird] at hmin
      have hpos_ne : e.symm y ≠ m.third := by
        intro heq
        apply hfix
        apply e.symm.injective
        simpa [y] using heq
      have hlt : m.third < e.symm y := lt_of_le_of_ne hmin hpos_ne.symm
      have hpos_y : e'.symm y = e.symm y := by
        change (zagMergeOrder e π m).symm y = e.symm y
        have hs := zagMergeOrder_symm_apply e π m (e.symm y)
        simp only [e.apply_symm_apply] at hs
        rw [hs, zagBlockSwap_symm_apply_of_right _ _ _ _
          m.first_lt_middle m.middle_lt_third hlt]
      have hε := zagMergePoint_eq_preimage_of_not_fixed e π m hfix
      change ε = y at hε
      rw [hε, hpos_y] at hexc
      omega
  · intro htriv
    simp only [zagTrivialAntiExceedance] at htriv
    have hmin_eq : zagCycleMinPos e' π' ε = q := by
      calc
        zagCycleMinPos e' π' ε = e'.symm (e' (zagCycleMinPos e' π' ε)) := by
          rw [e'.symm_apply_apply]
        _ = e'.symm (π' ε) := by rw [htriv]
        _ = e'.symm (e m.third) := by rw [happ]
        _ = q := hpos_third
    obtain ⟨hfm, hft⟩ := zagMergeVertical_sameCycles e π m
    change π'.SameCycle (e m.first) (e m.middle) at hfm
    change π'.SameCycle (e m.first) (e m.third) at hft
    have htε : π'.SameCycle (e m.third) ε := by
      have h := (Equiv.Perm.SameCycle.rfl : π'.SameCycle ε ε).apply_left
      simpa [happ] using h
    have hfε : π'.SameCycle (e m.first) ε := hft.trans htε
    have hle := zagCycleMinPos_le e' π' hfε
    rw [hmin_eq, hpos_first] at hle
    exact (not_le_of_gt hq.1) hle

theorem zagMerge_cycleMinPos {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) :
    zagCycleMinPos (zagMergeOrder e π m) (zagMergeVertical e π m)
      (zagMergePoint e π m) = m.first := by
  let e' := zagMergeOrder e π m
  let π' := zagMergeVertical e π m
  let ε := zagMergePoint e π m
  have hpos_first : e'.symm (e m.first) = m.first := by
    change (zagMergeOrder e π m).symm (e m.first) = m.first
    rw [zagMergeOrder_symm_apply, zagBlockSwap_symm_apply_left]
  obtain ⟨hfm, hft, hmt⟩ := zagMarkedTriple_pairwise m
  obtain ⟨hmerge_middle, hmerge_third⟩ :=
    zagMergeVertical_sameCycles e π m
  change π'.SameCycle (e m.first) (e m.middle) at hmerge_middle
  change π'.SameCycle (e m.first) (e m.third) at hmerge_third
  have happ : π' ε = e m.third := zagMergeVertical_apply_point e π m
  have htε : π'.SameCycle (e m.third) ε := by
    have h := (Equiv.Perm.SameCycle.rfl : π'.SameCycle ε ε).apply_left
    simpa [happ] using h
  have hfε : π'.SameCycle (e m.first) ε := hmerge_third.trans htε
  apply le_antisymm
  · have hle := zagCycleMinPos_le e' π' hfε
    rwa [hpos_first] at hle
  · let d := zagCycleMinPos e' π' ε
    let z := e' d
    have hzε : π'.SameCycle z ε := by
      exact zagCycleMinPos_mem e' π' ε
    have hfz : π'.SameCycle (e m.first) z := hfε.trans hzε.symm
    have hcases : π.SameCycle (e m.first) z ∨
        π.SameCycle (e m.middle) z ∨ π.SameCycle (e m.third) z := by
      apply zagTriangle_merge_cases π hfm hft hmt
      simpa only [π', zagMergeVertical] using hfz
    have hfirst := (zag_mem_cycleMinima_iff e π m.first).mp m.first_mem
    have hmiddle := (zag_mem_cycleMinima_iff e π m.middle).mp m.middle_mem
    have hthird := (zag_mem_cycleMinima_iff e π m.third).mp m.third_mem
    have htarget : m.first ≤ e.symm z := by
      rcases hcases with hfz' | hmz' | htz'
      · have hle := zagCycleMinPos_le e π hfz'.symm
        rwa [hfirst] at hle
      · have hle := zagCycleMinPos_le e π hmz'.symm
        rw [hmiddle] at hle
        exact m.first_lt_middle.le.trans hle
      · have hle := zagCycleMinPos_le e π htz'.symm
        rw [hthird] at hle
        exact (m.first_lt_middle.trans m.middle_lt_third).le.trans hle
    have hswap : m.first ≤
        (zagBlockSwap m.first m.middle m.third
          m.first_lt_middle m.middle_lt_third).symm (e.symm z) :=
      (zagBlockSwap_symm_preserves_leftCut _ _ _ _
        m.first_lt_middle m.middle_lt_third).mpr htarget
    have horder := zagMergeOrder_symm_apply e π m (e.symm z)
    simp only [e.apply_symm_apply] at horder
    calc
      m.first ≤ e'.symm z := by
        change m.first ≤ (zagMergeOrder e π m).symm z
        rwa [horder]
      _ = d := by simp [z]

theorem zagMerge_cycleMinPos_before {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) (r : Fin n)
    (hr : r ∈ zagCycleMinima e π) (hrf : r < m.first) :
    r ∈ zagCycleMinima (zagMergeOrder e π m)
      (zagMergeVertical e π m) := by
  classical
  let e' := zagMergeOrder e π m
  let π' := zagMergeVertical e π m
  have her : e' r = e r := by
    simp only [e', zagMergeOrder, Equiv.Perm.mul_apply]
    congr 1
    apply Fin.ext
    simp [zagBlockSwap_val, zagBlockSwapNat,
      show (r : ℕ) ≤ (m.first : ℕ) from hrf.le]
  have hrf_cycle : ¬π.SameCycle (e r) (e m.first) :=
    zagCycleMinima_not_same_of_lt e π hr m.first_mem hrf
  have hrm_cycle : ¬π.SameCycle (e r) (e m.middle) :=
    zagCycleMinima_not_same_of_lt e π hr m.middle_mem
      (hrf.trans m.first_lt_middle)
  have hrt_cycle : ¬π.SameCycle (e r) (e m.third) :=
    zagCycleMinima_not_same_of_lt e π hr m.third_mem
      (hrf.trans (m.first_lt_middle.trans m.middle_lt_third))
  rw [zag_mem_cycleMinima_iff] at hr ⊢
  let d := zagCycleMinPos e' π' (e' r)
  have hdcycle : π.SameCycle (e r) (e' d) := by
    apply (zagSameCycle_mul_triangle_iff_of_disjoint π
      hrf_cycle hrm_cycle hrt_cycle).mp
    have hnew : π'.SameCycle (e r) (e' d) := by
      rw [← her]
      exact (zagCycleMinPos_mem e' π' (e' r)).symm
    simpa only [π', zagMergeVertical] using hnew
  have hpos : r ≤ e.symm (e' d) := by
    have hle := zagCycleMinPos_le e π hdcycle.symm
    rwa [hr] at hle
  have hrd : r ≤ d := by
    by_cases hdf : d < m.first
    · have hed : e' d = e d := by
        simp only [e', zagMergeOrder, Equiv.Perm.mul_apply]
        congr 1
        apply Fin.ext
        simp [zagBlockSwap_val, zagBlockSwapNat,
          show (d : ℕ) ≤ (m.first : ℕ) from hdf.le]
      rwa [hed, e.symm_apply_apply] at hpos
    · exact hrf.le.trans (le_of_not_gt hdf)
  have hdr : d ≤ r := by
    have hle := zagCycleMinPos_le e' π'
      (Equiv.Perm.SameCycle.rfl : π'.SameCycle (e' r) (e' r))
    simpa only [e'.symm_apply_apply] using hle
  exact le_antisymm hdr hrd

theorem zagMerge_cutHit {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) :
    let e' := zagMergeOrder e π m
    let π' := zagMergeVertical e π m
    let ε := zagMergePoint e π m
    zagCutHit e' π' ε =
      zagReturnTime π (e m.middle) + zagReturnTime π (e m.third) := by
  let e' := zagMergeOrder e π m
  let π' := zagMergeVertical e π m
  let ε := zagMergePoint e π m
  let a := e m.first
  let b := e m.middle
  let c := e m.third
  let Lb := zagReturnTime π b
  let Lc := zagReturnTime π c
  obtain ⟨hab, hac, hbc⟩ := zagMarkedTriple_pairwise m
  have hac' : π'.SameCycle a c := by
    exact (zagMergeVertical_sameCycles e π m).2
  have hac_ne : a ≠ c := fun h => hac (h.sameCycle π)
  have hsum : (π' ^ (Lb + Lc)) a = c := by
    have hp := zagTriangle_merge_pow_after_left π hab hac hbc
      (zagReturnTime_pos π c) (le_refl (zagReturnTime π c))
    simpa only [π', zagMergeVertical, a, b, c, Lb, Lc] using
      hp.trans (zagReturnTime_spec π c)
  have hno (r : ℕ) (hr0 : 0 < r) (hr : r < Lb + Lc) :
      (π' ^ r) a ≠ c := by
    by_cases hrb : r ≤ Lb
    · have hp := zagTriangle_merge_pow_left π hab hac hbc hr0 hrb
      intro hrc
      apply hbc
      refine ⟨(r : ℤ), ?_⟩
      rw [zpow_natCast]
      have hp' : (π' ^ r) a = (π ^ r) b := by
        simpa only [π', zagMergeVertical, a, b, c] using hp
      exact hp'.symm.trans hrc
    · let s := r - Lb
      have hs0 : 0 < s := by omega
      have hslt : s < Lc := by omega
      have hp := zagTriangle_merge_pow_after_left π hab hac hbc hs0 hslt.le
      have hpr : (π' ^ r) a = (π ^ s) c := by
        simpa only [π', zagMergeVertical, a, b, c, Lb, Lc, s,
          show Lb + (r - Lb) = r by omega] using hp
      intro hrc
      exact zagReturnTime_no_return π c hs0 hslt (hpr.symm.trans hrc)
  let H := zagCycleHit π' a c hac'
  have hHle : H ≤ Lb + Lc :=
    zagCycleHit_minimal π' a c hac' hsum
  have hleH : Lb + Lc ≤ H := by
    by_contra h
    have hHlt : H < Lb + Lc := by omega
    have hHpos := zagCycleHit_pos π' hac_ne hac'
    exact hno H hHpos hHlt (zagCycleHit_spec π' a c hac')
  have hH : H = Lb + Lc := le_antisymm hHle hleH
  change zagCutHit e' π' ε = Lb + Lc
  rw [zagCutHit]
  have hmin : zagCycleMinPos e' π' ε = m.first :=
    zagMerge_cycleMinPos e π m
  have hfirst : e' m.first = a := by
    change zagMergeOrder e π m m.first = e m.first
    simp [zagMergeOrder, Equiv.Perm.mul_apply, zagBlockSwap_apply_left]
  have happ : π' ε = c := zagMergeVertical_apply_point e π m
  have hstart : e' (zagCycleMinPos e' π' ε) = a := by
    rw [hmin, hfirst]
  calc
    zagCycleHit π' (e' (zagCycleMinPos e' π' ε)) (π' ε) _ = H := by
      congr 1
    _ = Lb + Lc := hH

theorem zagMerge_third_mem_cutCandidates {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) :
    let e' := zagMergeOrder e π m
    let π' := zagMergeVertical e π m
    let ε := zagMergePoint e π m
    m.third ∈ zagCutCandidates e' π' ε := by
  classical
  let e' := zagMergeOrder e π m
  let π' := zagMergeVertical e π m
  let ε := zagMergePoint e π m
  let q := zagBlockMiddle m.first m.middle m.third
    m.first_lt_middle m.middle_lt_third
  obtain ⟨hab, hac, hbc⟩ := zagMarkedTriple_pairwise m
  have hmin : zagCycleMinPos e' π' ε = m.first :=
    zagMerge_cycleMinPos e π m
  have happ : π' ε = e m.third := zagMergeVertical_apply_point e π m
  have hpos_image : e'.symm (π' ε) = q := by
    rw [happ]
    change (zagMergeOrder e π m).symm (e m.third) = q
    rw [zagMergeOrder_symm_apply, zagBlockSwap_symm_apply_right]
  have hfirst : e' m.first = e m.first := by
    change zagMergeOrder e π m m.first = e m.first
    simp [zagMergeOrder, Equiv.Perm.mul_apply, zagBlockSwap_apply_left]
  have hthird : e' m.third = e m.middle := by
    change zagMergeOrder e π m m.third = e m.middle
    simp [zagMergeOrder, Equiv.Perm.mul_apply, zagBlockSwap_apply_right]
  have hpow :
      (π' ^ zagReturnTime π (e m.middle)) (e m.first) = e m.middle := by
    have hp := zagTriangle_merge_pow_left π hab hac hbc
      (zagReturnTime_pos π (e m.middle))
      (le_refl (zagReturnTime π (e m.middle)))
    have hp' : (π' ^ zagReturnTime π (e m.middle)) (e m.first) =
        (π ^ zagReturnTime π (e m.middle)) (e m.middle) := by
      simpa only [π', zagMergeVertical] using hp
    exact hp'.trans
      (zagReturnTime_spec π (e m.middle))
  change m.third ∈ Finset.univ.filter fun i =>
    e'.symm (π' ε) < i ∧ ∃ t : ℕ,
      0 < t ∧ t < zagCutHit e' π' ε ∧
        (π' ^ t) (e' (zagCycleMinPos e' π' ε)) = e' i
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_, zagReturnTime π (e m.middle),
    zagReturnTime_pos π (e m.middle), ?_, ?_⟩
  · rw [hpos_image]
    exact (zagBlockMiddle_bounds m.first m.middle m.third
      m.first_lt_middle m.middle_lt_third).2
  · rw [zagMerge_cutHit]
    have hcpos := zagReturnTime_pos π (e m.third)
    omega
  · rw [hmin, hfirst, hthird]
    exact hpow

theorem zagMerge_cutCandidate_ge_third {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) {x : Fin n}
    (hx : x ∈ zagCutCandidates (zagMergeOrder e π m)
      (zagMergeVertical e π m) (zagMergePoint e π m)) :
    m.third ≤ x := by
  classical
  let e' := zagMergeOrder e π m
  let π' := zagMergeVertical e π m
  let ε := zagMergePoint e π m
  let q := zagBlockMiddle m.first m.middle m.third
    m.first_lt_middle m.middle_lt_third
  let Lb := zagReturnTime π (e m.middle)
  let Lc := zagReturnTime π (e m.third)
  obtain ⟨hab, hac, hbc⟩ := zagMarkedTriple_pairwise m
  have hmin : zagCycleMinPos e' π' ε = m.first :=
    zagMerge_cycleMinPos e π m
  have hfirst : e' m.first = e m.first := by
    change zagMergeOrder e π m m.first = e m.first
    simp [zagMergeOrder, Equiv.Perm.mul_apply, zagBlockSwap_apply_left]
  have hpos_image : e'.symm (π' ε) = q := by
    have happ : π' ε = e m.third := zagMergeVertical_apply_point e π m
    rw [happ]
    change (zagMergeOrder e π m).symm (e m.third) = q
    rw [zagMergeOrder_symm_apply, zagBlockSwap_symm_apply_right]
  change x ∈ Finset.univ.filter (fun i =>
    e'.symm (π' ε) < i ∧ ∃ t : ℕ,
      0 < t ∧ t < zagCutHit e' π' ε ∧
        (π' ^ t) (e' (zagCycleMinPos e' π' ε)) = e' i) at hx
  obtain ⟨hqx, t, ht0, htcut, hpath⟩ := (Finset.mem_filter.mp hx).2
  rw [hpos_image] at hqx
  have ht : t < Lb + Lc := by
    rw [zagMerge_cutHit] at htcut
    exact htcut
  rw [hmin, hfirst] at hpath
  have horder : e' x = e ((zagBlockSwap m.first m.middle m.third
      m.first_lt_middle m.middle_lt_third) x) := by
    simp [e', zagMergeOrder, Equiv.Perm.mul_apply]
  by_cases htb : t ≤ Lb
  · have hp := zagTriangle_merge_pow_left π hab hac hbc ht0 htb
    have hp' : (π' ^ t) (e m.first) = (π ^ t) (e m.middle) := by
      simpa only [π', zagMergeVertical] using hp
    have heq : (π ^ t) (e m.middle) = e' x := hp'.symm.trans hpath
    have hcycle : π.SameCycle (e m.middle) ((π ^ t) (e m.middle)) :=
      ⟨(t : ℤ), by rw [zpow_natCast]⟩
    have hle := zagCycleMinPos_le e π hcycle.symm
    have hmiddle := (zag_mem_cycleMinima_iff e π m.middle).mp m.middle_mem
    rw [hmiddle, heq, horder, e.symm_apply_apply] at hle
    exact zagBlockSwap_right_of_middle_le _ _ _ _
      m.first_lt_middle m.middle_lt_third hqx hle
  · let s := t - Lb
    have hs0 : 0 < s := by omega
    have hslt : s < Lc := by omega
    have hp := zagTriangle_merge_pow_after_left π hab hac hbc hs0 hslt.le
    have hp' : (π' ^ t) (e m.first) = (π ^ s) (e m.third) := by
      simpa only [π', zagMergeVertical, Lb, Lc, s,
        show Lb + (t - Lb) = t by omega] using hp
    have heq : (π ^ s) (e m.third) = e' x := hp'.symm.trans hpath
    have hcycle : π.SameCycle (e m.third) ((π ^ s) (e m.third)) :=
      ⟨(s : ℤ), by rw [zpow_natCast]⟩
    have hle := zagCycleMinPos_le e π hcycle.symm
    have hthird := (zag_mem_cycleMinima_iff e π m.third).mp m.third_mem
    rw [hthird, heq, horder, e.symm_apply_apply] at hle
    have hmiddle_le := m.middle_lt_third.le.trans hle
    exact zagBlockSwap_right_of_middle_le _ _ _ _
      m.first_lt_middle m.middle_lt_third hqx hmiddle_le

theorem zagMerge_cutPos {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) :
    let hε := zagMergePoint_nontrivialAntiExceedance e π m
    zagCutPos (zagMergeOrder e π m) (zagMergeVertical e π m)
      (zagMergePoint e π m) hε = m.third := by
  let e' := zagMergeOrder e π m
  let π' := zagMergeVertical e π m
  let ε := zagMergePoint e π m
  let hε := zagMergePoint_nontrivialAntiExceedance e π m
  apply le_antisymm
  · apply zagCutPos_min e' π' ε hε
    exact zagMerge_third_mem_cutCandidates e π m
  · apply zagMerge_cutCandidate_ge_third e π m
    exact zagCutPos_mem e' π' ε hε

theorem zagSlice_merge_order_from_marked {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) :
    let e' := zagMergeOrder e π m
    let π' := zagMergeVertical e π m
    let ε := zagMergePoint e π m
    let hε := zagMergePoint_nontrivialAntiExceedance e π m
    zagSliceOrder e' π' ε hε = e := by
  let e' := zagMergeOrder e π m
  let π' := zagMergeVertical e π m
  let ε := zagMergePoint e π m
  let hε := zagMergePoint_nontrivialAntiExceedance e π m
  have hmin : zagCycleMinPos e' π' ε = m.first :=
    zagMerge_cycleMinPos e π m
  have happ : π' ε = e m.third := zagMergeVertical_apply_point e π m
  have himage : e'.symm (π' ε) =
      zagBlockMiddle m.first m.middle m.third
        m.first_lt_middle m.middle_lt_third := by
    rw [happ]
    change (zagMergeOrder e π m).symm (e m.third) = _
    rw [zagMergeOrder_symm_apply, zagBlockSwap_symm_apply_right]
  have hcut : zagCutPos e' π' ε hε = m.third := zagMerge_cutPos e π m
  change e' * zagBlockSwap (zagCycleMinPos e' π' ε) (e'.symm (π' ε))
      (zagCutPos e' π' ε hε) _ _ = e
  simp only [hmin, himage, hcut]
  change (e * zagBlockSwap m.first m.middle m.third
      m.first_lt_middle m.middle_lt_third) *
    zagBlockSwap m.first
      (zagBlockMiddle m.first m.middle m.third
        m.first_lt_middle m.middle_lt_third) m.third _ _ = e
  rw [mul_assoc, zagBlockSwap_mul_reverse, mul_one]

theorem zagSlice_merge_vertical_from_marked {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) :
    let e' := zagMergeOrder e π m
    let π' := zagMergeVertical e π m
    let ε := zagMergePoint e π m
    let hε := zagMergePoint_nontrivialAntiExceedance e π m
    zagSliceVertical e' π' ε hε = π := by
  let e' := zagMergeOrder e π m
  let π' := zagMergeVertical e π m
  let ε := zagMergePoint e π m
  let hε := zagMergePoint_nontrivialAntiExceedance e π m
  have hmin : zagCycleMinPos e' π' ε = m.first :=
    zagMerge_cycleMinPos e π m
  have happ : π' ε = e m.third := zagMergeVertical_apply_point e π m
  have hcut : zagCutPos e' π' ε hε = m.third := zagMerge_cutPos e π m
  have hfirst : e' m.first = e m.first := by
    change zagMergeOrder e π m m.first = e m.first
    simp [zagMergeOrder, Equiv.Perm.mul_apply, zagBlockSwap_apply_left]
  have hthird : e' m.third = e m.middle := by
    change zagMergeOrder e π m m.third = e m.middle
    simp [zagMergeOrder, Equiv.Perm.mul_apply, zagBlockSwap_apply_right]
  have hfm : e m.first ≠ e m.middle :=
    e.injective.ne (ne_of_lt m.first_lt_middle)
  have hft : e m.first ≠ e m.third :=
    e.injective.ne (ne_of_lt (m.first_lt_middle.trans m.middle_lt_third))
  have hmt : e m.middle ≠ e m.third :=
    e.injective.ne (ne_of_lt m.middle_lt_third)
  change π' * zagTriangle (e' (zagCycleMinPos e' π' ε)) (π' ε)
      (e' (zagCutPos e' π' ε hε)) = π
  simp only [hmin, happ, hcut, hfirst, hthird]
  change (π * zagTriangle (e m.first) (e m.middle) (e m.third)) *
      zagTriangle (e m.first) (e m.third) (e m.middle) = π
  rw [mul_assoc, zagTriangle_mul_reverse hfm hft hmt, mul_one]

theorem zagMerge_residual_cycleMinPos {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π)
    (hres : zagNontrivialAntiExceedance e π (zagMergePoint e π m)) :
    zagCycleMinPos e π (zagMergePoint e π m) = m.third := by
  have hmiddle := (zag_mem_cycleMinima_iff e π m.middle).mp m.middle_mem
  have hthird := (zag_mem_cycleMinima_iff e π m.third).mp m.third_mem
  have hnotfixed : π.symm (e m.third) ≠ e m.third := by
    intro hfix
    have hε := zagMergePoint_eq_middle_of_fixed e π m hfix
    rw [hε] at hres
    by_cases hb : π (e m.middle) = e m.middle
    · apply hres.2
      simp only [zagTrivialAntiExceedance, hmiddle, hb]
    · apply hres.1
      simp only [zagExceedance, e.symm_apply_apply]
      have hsame : π.SameCycle (π (e m.middle)) (e m.middle) :=
        (Equiv.Perm.SameCycle.rfl :
          π.SameCycle (e m.middle) (e m.middle)).apply_left
      have hle := zagCycleMinPos_le e π hsame
      rw [hmiddle] at hle
      exact lt_of_le_of_ne hle fun heq => hb (e.symm.injective (by simpa using heq.symm))
  have hε := zagMergePoint_eq_preimage_of_not_fixed e π m hnotfixed
  have hsame : π.SameCycle (zagMergePoint e π m) (e m.third) := by
    rw [hε]
    exact (Equiv.Perm.SameCycle.rfl :
      π.SameCycle (e m.third) (e m.third)).symm_apply_left
  rw [zagCycleMinPos_eq_of_sameCycle e π hsame, hthird]

theorem zagSlice_merge_marked_from_marked {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) :
    let e' := zagMergeOrder e π m
    let π' := zagMergeVertical e π m
    let ε := zagMergePoint e π m
    let hε := zagMergePoint_nontrivialAntiExceedance e π m
    zagSliceMarked e' π' ε hε = m.toFinset := by
  let e' := zagMergeOrder e π m
  let π' := zagMergeVertical e π m
  let ε := zagMergePoint e π m
  let hε := zagMergePoint_nontrivialAntiExceedance e π m
  have hmin : zagCycleMinPos e' π' ε = m.first :=
    zagMerge_cycleMinPos e π m
  have happ : π' ε = e m.third := zagMergeVertical_apply_point e π m
  have himage : e'.symm (π' ε) =
      zagBlockMiddle m.first m.middle m.third
        m.first_lt_middle m.middle_lt_third := by
    rw [happ]
    change (zagMergeOrder e π m).symm (e m.third) = _
    rw [zagMergeOrder_symm_apply, zagBlockSwap_symm_apply_right]
  have hcut : zagCutPos e' π' ε hε = m.third := zagMerge_cutPos e π m
  have hmiddle_reverse :
      zagBlockMiddle m.first
        (zagBlockMiddle m.first m.middle m.third
          m.first_lt_middle m.middle_lt_third) m.third _ _ = m.middle :=
    zagBlockMiddle_reverse m.first m.middle m.third
      m.first_lt_middle m.middle_lt_third
  have horder : zagSliceOrder e' π' ε hε = e :=
    zagSlice_merge_order_from_marked e π m
  have hvertical : zagSliceVertical e' π' ε hε = π :=
    zagSlice_merge_vertical_from_marked e π m
  by_cases hres : zagNontrivialAntiExceedance
      (zagSliceOrder e' π' ε hε) (zagSliceVertical e' π' ε hε) ε
  · have hres' : zagNontrivialAntiExceedance e π ε := by
      simpa only [horder, hvertical] using hres
    have hresmin : zagCycleMinPos e π ε = m.third :=
      zagMerge_residual_cycleMinPos e π m hres'
    have hs := zagSliceMarked_eq_residual e' π' ε hε hres
    dsimp only at hs
    simpa only [hmin, himage, hcut, hmiddle_reverse, horder, hvertical,
      hresmin, ZagMarkedTriple.toFinset] using hs
  · have hs := zagSliceMarked_eq_terminal e' π' ε hε hres
    dsimp only at hs
    simpa only [hmin, himage, hcut, hmiddle_reverse,
      ZagMarkedTriple.toFinset] using hs

theorem zagResidual_middle_lt_image {n : ℕ}
    {e π : Equiv.Perm (Fin n)} (m : ZagMarkedTriple e π) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hthird : zagCycleMinPos e π ε = m.third) :
    m.middle < e.symm (π ε) := by
  have h := zagNTAE_min_lt_image e π hε
  rw [hthird] at h
  exact m.middle_lt_third.trans h

end MetaMathlibExt
