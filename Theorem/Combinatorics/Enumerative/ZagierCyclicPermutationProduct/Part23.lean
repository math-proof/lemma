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
import Def.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part23
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

theorem zagResidual_critical_pairwise {n : ℕ}
    {e π : Equiv.Perm (Fin n)} (m : ZagMarkedTriple e π) (ε : Fin n)
    (hthird : zagCycleMinPos e π ε = m.third) :
    ¬π.SameCycle (e m.first) (e m.middle) ∧
      ¬π.SameCycle (e m.first) (π ε) ∧
      ¬π.SameCycle (e m.middle) (π ε) := by
  have hfirst := (zag_mem_cycleMinima_iff e π m.first).mp m.first_mem
  have hmiddle := (zag_mem_cycleMinima_iff e π m.middle).mp m.middle_mem
  have himage : zagCycleMinPos e π (π ε) = m.third := by
    rw [zagCycleMinPos_eq_of_sameCycle e π
      ((Equiv.Perm.SameCycle.rfl : π.SameCycle ε ε).apply_left), hthird]
  constructor
  · exact (zagMarkedTriple_pairwise m).1
  constructor
  · intro hsame
    have hmin := zagCycleMinPos_eq_of_sameCycle e π hsame
    rw [hfirst, himage] at hmin
    exact (m.first_lt_middle.trans m.middle_lt_third).ne hmin
  · intro hsame
    have hmin := zagCycleMinPos_eq_of_sameCycle e π hsame
    rw [hmiddle, himage] at hmin
    exact m.middle_lt_third.ne hmin

theorem zagResidualMergeOrder_symm_apply {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) (ε x : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hthird : zagCycleMinPos e π ε = m.third) :
    (zagResidualMergeOrder e π m ε hε hthird).symm (e x) =
      (zagBlockSwap m.first m.middle (e.symm (π ε))
        m.first_lt_middle (zagResidual_middle_lt_image m ε hε hthird)).symm x := by
  let B := zagBlockSwap m.first m.middle (e.symm (π ε))
    m.first_lt_middle (zagResidual_middle_lt_image m ε hε hthird)
  change ((e * B)⁻¹) (e x) = B⁻¹ x
  rw [mul_inv_rev, Equiv.Perm.mul_apply]
  change B.symm (e.symm (e x)) = B.symm x
  rw [e.symm_apply_apply]

theorem zagResidualMergeVertical_apply_point {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hthird : zagCycleMinPos e π ε = m.third) :
    zagResidualMergeVertical e π m ε ε = π ε := by
  have hfirst := (zag_mem_cycleMinima_iff e π m.first).mp m.first_mem
  have hmiddle := (zag_mem_cycleMinima_iff e π m.middle).mp m.middle_mem
  have hεf : ε ≠ e m.first := by
    intro heq
    have hm : zagCycleMinPos e π ε = m.first := by simpa [heq] using hfirst
    rw [hm] at hthird
    exact (m.first_lt_middle.trans m.middle_lt_third).ne hthird
  have hεm : ε ≠ e m.middle := by
    intro heq
    have hm : zagCycleMinPos e π ε = m.middle := by simpa [heq] using hmiddle
    rw [hm] at hthird
    exact m.middle_lt_third.ne hthird
  have hεb : ε ≠ π ε := by
    intro heq
    have hlt := zagNTAE_image_lt e π hε
    rw [← heq] at hlt
    exact (lt_irrefl _ hlt).elim
  simp only [zagResidualMergeVertical, Equiv.Perm.mul_apply]
  rw [zagTriangle_apply_of_ne hεf hεm hεb]

theorem zagResidualMergePoint_nontrivialAntiExceedance {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hthird : zagCycleMinPos e π ε = m.third) :
    zagNontrivialAntiExceedance
      (zagResidualMergeOrder e π m ε hε hthird)
      (zagResidualMergeVertical e π m ε) ε := by
  let e' := zagResidualMergeOrder e π m ε hε hthird
  let π' := zagResidualMergeVertical e π m ε
  let l := e.symm (π ε)
  let q := zagBlockMiddle m.first m.middle l m.first_lt_middle
    (zagResidual_middle_lt_image m ε hε hthird)
  have hbounds := zagBlockMiddle_bounds m.first m.middle l
    m.first_lt_middle (zagResidual_middle_lt_image m ε hε hthird)
  have happ : π' ε = π ε :=
    zagResidualMergeVertical_apply_point e π m ε hε hthird
  have hpos_image : e'.symm (π ε) = q := by
    rw [← e.apply_symm_apply (π ε)]
    change (zagResidualMergeOrder e π m ε hε hthird).symm (e l) = q
    rw [zagResidualMergeOrder_symm_apply,
      zagBlockSwap_symm_apply_right]
  have hpos_eps : e'.symm ε = e.symm ε := by
    have hs := zagResidualMergeOrder_symm_apply e π m ε (e.symm ε) hε hthird
    simp only [e.apply_symm_apply] at hs
    have hlast : l < e.symm ε := zagNTAE_image_lt e π hε
    rw [hs, zagBlockSwap_symm_apply_of_right _ _ _ _
      m.first_lt_middle (zagResidual_middle_lt_image m ε hε hthird) hlast]
  constructor
  · intro hexc
    simp only [zagExceedance] at hexc
    change e'.symm ε < e'.symm (π' ε) at hexc
    rw [happ, hpos_image, hpos_eps] at hexc
    have hlast : l < e.symm ε := zagNTAE_image_lt e π hε
    exact (not_lt_of_ge (hbounds.2.le.trans hlast.le)) hexc
  · intro htriv
    simp only [zagTrivialAntiExceedance] at htriv
    obtain ⟨hfm, hfb, hmb⟩ := zagResidual_critical_pairwise m ε hthird
    have hmerge := zagTriangle_merge_sameCycles π hfm hfb hmb
    have hAimage : π'.SameCycle (e m.first) (π ε) := by
      exact hmerge.2
    have himageε : π'.SameCycle (π ε) ε := by
      have h := (Equiv.Perm.SameCycle.rfl : π'.SameCycle ε ε).apply_left
      simpa [happ] using h
    have hAε := hAimage.trans himageε
    have hle := zagCycleMinPos_le e' π' hAε
    have hpos_first : e'.symm (e m.first) = m.first := by
      change (zagResidualMergeOrder e π m ε hε hthird).symm
        (e m.first) = m.first
      rw [zagResidualMergeOrder_symm_apply,
        zagBlockSwap_symm_apply_left]
    have hmin_eq : zagCycleMinPos e' π' ε = q := by
      calc
        zagCycleMinPos e' π' ε = e'.symm (e' (zagCycleMinPos e' π' ε)) := by
          rw [e'.symm_apply_apply]
        _ = e'.symm (π' ε) := by rw [htriv]
        _ = e'.symm (π ε) := by rw [happ]
        _ = q := hpos_image
    rw [hmin_eq, hpos_first] at hle
    exact (not_le_of_gt hbounds.1) hle

theorem zagResidualMerge_cycleMinPos {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hthird : zagCycleMinPos e π ε = m.third) :
    zagCycleMinPos (zagResidualMergeOrder e π m ε hε hthird)
      (zagResidualMergeVertical e π m ε) ε = m.first := by
  let e' := zagResidualMergeOrder e π m ε hε hthird
  let π' := zagResidualMergeVertical e π m ε
  have hpos_first : e'.symm (e m.first) = m.first := by
    change (zagResidualMergeOrder e π m ε hε hthird).symm
      (e m.first) = m.first
    rw [zagResidualMergeOrder_symm_apply, zagBlockSwap_symm_apply_left]
  obtain ⟨hfm, hfb, hmb⟩ := zagResidual_critical_pairwise m ε hthird
  obtain ⟨hmerge_middle, hmerge_image⟩ :=
    zagTriangle_merge_sameCycles π hfm hfb hmb
  change π'.SameCycle (e m.first) (e m.middle) at hmerge_middle
  change π'.SameCycle (e m.first) (π ε) at hmerge_image
  have happ : π' ε = π ε :=
    zagResidualMergeVertical_apply_point e π m ε hε hthird
  have himageε : π'.SameCycle (π ε) ε := by
    have h := (Equiv.Perm.SameCycle.rfl : π'.SameCycle ε ε).apply_left
    simpa [happ] using h
  have hfε : π'.SameCycle (e m.first) ε := hmerge_image.trans himageε
  apply le_antisymm
  · have hle := zagCycleMinPos_le e' π' hfε
    rwa [hpos_first] at hle
  · let d := zagCycleMinPos e' π' ε
    let z := e' d
    have hzε : π'.SameCycle z ε := zagCycleMinPos_mem e' π' ε
    have hfz : π'.SameCycle (e m.first) z := hfε.trans hzε.symm
    have hcases : π.SameCycle (e m.first) z ∨
        π.SameCycle (e m.middle) z ∨ π.SameCycle (π ε) z := by
      apply zagTriangle_merge_cases π hfm hfb hmb
      simpa only [π', zagResidualMergeVertical] using hfz
    have hfirst := (zag_mem_cycleMinima_iff e π m.first).mp m.first_mem
    have hmiddle := (zag_mem_cycleMinima_iff e π m.middle).mp m.middle_mem
    have himage : zagCycleMinPos e π (π ε) = m.third := by
      rw [zagCycleMinPos_eq_of_sameCycle e π
        ((Equiv.Perm.SameCycle.rfl : π.SameCycle ε ε).apply_left), hthird]
    have htarget : m.first ≤ e.symm z := by
      rcases hcases with hfz' | hmz' | hbz'
      · have hle := zagCycleMinPos_le e π hfz'.symm
        rwa [hfirst] at hle
      · have hle := zagCycleMinPos_le e π hmz'.symm
        rw [hmiddle] at hle
        exact m.first_lt_middle.le.trans hle
      · have hle := zagCycleMinPos_le e π hbz'.symm
        rw [himage] at hle
        exact (m.first_lt_middle.trans m.middle_lt_third).le.trans hle
    have hswap : m.first ≤
        (zagBlockSwap m.first m.middle (e.symm (π ε))
          m.first_lt_middle (zagResidual_middle_lt_image m ε hε hthird)).symm
          (e.symm z) :=
      (zagBlockSwap_symm_preserves_leftCut _ _ _ _
        m.first_lt_middle (zagResidual_middle_lt_image m ε hε hthird)).mpr htarget
    have horder := zagResidualMergeOrder_symm_apply e π m ε (e.symm z) hε hthird
    simp only [e.apply_symm_apply] at horder
    calc
      m.first ≤ e'.symm z := by
        change m.first ≤
          (zagResidualMergeOrder e π m ε hε hthird).symm z
        rwa [horder]
      _ = d := by simp [z]

theorem zagResidualMerge_cycleMinPos_before {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) (ε r : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hthird : zagCycleMinPos e π ε = m.third)
    (hr : r ∈ zagCycleMinima e π) (hrf : r < m.first) :
    r ∈ zagCycleMinima (zagResidualMergeOrder e π m ε hε hthird)
      (zagResidualMergeVertical e π m ε) := by
  classical
  let e' := zagResidualMergeOrder e π m ε hε hthird
  let π' := zagResidualMergeVertical e π m ε
  have her : e' r = e r := by
    simp only [e', zagResidualMergeOrder, Equiv.Perm.mul_apply]
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
  have hrimage_cycle : ¬π.SameCycle (e r) (π ε) := by
    intro hsame
    apply hrt_cycle
    exact hsame.trans ((Equiv.Perm.SameCycle.rfl : π.SameCycle ε ε).apply_left |>.trans
      (by
        have hmem := zagCycleMinPos_mem e π ε
        rw [hthird] at hmem
        exact hmem.symm))
  rw [zag_mem_cycleMinima_iff] at hr ⊢
  let d := zagCycleMinPos e' π' (e' r)
  have hdcycle : π.SameCycle (e r) (e' d) := by
    apply (zagSameCycle_mul_triangle_iff_of_disjoint π
      hrf_cycle hrm_cycle hrimage_cycle).mp
    have hnew : π'.SameCycle (e r) (e' d) := by
      rw [← her]
      exact (zagCycleMinPos_mem e' π' (e' r)).symm
    simpa only [π', zagResidualMergeVertical] using hnew
  have hpos : r ≤ e.symm (e' d) := by
    have hle := zagCycleMinPos_le e π hdcycle.symm
    rwa [hr] at hle
  have hrd : r ≤ d := by
    by_cases hdf : d < m.first
    · have hed : e' d = e d := by
        simp only [e', zagResidualMergeOrder, Equiv.Perm.mul_apply]
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

theorem zagResidualMerge_cutHit {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hthird : zagCycleMinPos e π ε = m.third) :
    let e' := zagResidualMergeOrder e π m ε hε hthird
    let π' := zagResidualMergeVertical e π m ε
    zagCutHit e' π' ε =
      zagReturnTime π (e m.middle) + zagReturnTime π (π ε) := by
  let e' := zagResidualMergeOrder e π m ε hε hthird
  let π' := zagResidualMergeVertical e π m ε
  let a := e m.first
  let b := e m.middle
  let c := π ε
  let Lb := zagReturnTime π b
  let Lc := zagReturnTime π c
  obtain ⟨hab, hac, hbc⟩ := zagResidual_critical_pairwise m ε hthird
  have hac' : π'.SameCycle a c := by
    exact (zagTriangle_merge_sameCycles π hab hac hbc).2
  have hac_ne : a ≠ c := fun h => hac (h.sameCycle π)
  have hsum : (π' ^ (Lb + Lc)) a = c := by
    have hp := zagTriangle_merge_pow_after_left π hab hac hbc
      (zagReturnTime_pos π c) (le_refl (zagReturnTime π c))
    simpa only [π', zagResidualMergeVertical, a, b, c, Lb, Lc] using
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
        simpa only [π', zagResidualMergeVertical, a, b, c] using hp
      exact hp'.symm.trans hrc
    · let s := r - Lb
      have hs0 : 0 < s := by omega
      have hslt : s < Lc := by omega
      have hp := zagTriangle_merge_pow_after_left π hab hac hbc hs0 hslt.le
      have hpr : (π' ^ r) a = (π ^ s) c := by
        simpa only [π', zagResidualMergeVertical, a, b, c, Lb, Lc, s,
          show Lb + (r - Lb) = r by omega] using hp
      intro hrc
      exact zagReturnTime_no_return π c hs0 hslt (hpr.symm.trans hrc)
  let H := zagCycleHit π' a c hac'
  have hHle : H ≤ Lb + Lc := zagCycleHit_minimal π' a c hac' hsum
  have hleH : Lb + Lc ≤ H := by
    by_contra h
    have hHlt : H < Lb + Lc := by omega
    have hHpos := zagCycleHit_pos π' hac_ne hac'
    exact hno H hHpos hHlt (zagCycleHit_spec π' a c hac')
  have hH : H = Lb + Lc := le_antisymm hHle hleH
  change zagCutHit e' π' ε = Lb + Lc
  rw [zagCutHit]
  have hmin : zagCycleMinPos e' π' ε = m.first :=
    zagResidualMerge_cycleMinPos e π m ε hε hthird
  have hfirst : e' m.first = a := by
    change zagResidualMergeOrder e π m ε hε hthird m.first = e m.first
    simp [zagResidualMergeOrder, Equiv.Perm.mul_apply,
      zagBlockSwap_apply_left]
  have happ : π' ε = c :=
    zagResidualMergeVertical_apply_point e π m ε hε hthird
  have hstart : e' (zagCycleMinPos e' π' ε) = a := by rw [hmin, hfirst]
  calc
    zagCycleHit π' (e' (zagCycleMinPos e' π' ε)) (π' ε) _ = H := by
      congr 1
    _ = Lb + Lc := hH

theorem zagResidualMerge_last_mem_cutCandidates {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hthird : zagCycleMinPos e π ε = m.third) :
    let e' := zagResidualMergeOrder e π m ε hε hthird
    let π' := zagResidualMergeVertical e π m ε
    e.symm (π ε) ∈ zagCutCandidates e' π' ε := by
  classical
  let e' := zagResidualMergeOrder e π m ε hε hthird
  let π' := zagResidualMergeVertical e π m ε
  let l := e.symm (π ε)
  let q := zagBlockMiddle m.first m.middle l m.first_lt_middle
    (zagResidual_middle_lt_image m ε hε hthird)
  obtain ⟨hab, hac, hbc⟩ := zagResidual_critical_pairwise m ε hthird
  have hmin : zagCycleMinPos e' π' ε = m.first :=
    zagResidualMerge_cycleMinPos e π m ε hε hthird
  have happ : π' ε = π ε :=
    zagResidualMergeVertical_apply_point e π m ε hε hthird
  have hpos_image : e'.symm (π' ε) = q := by
    rw [happ, ← e.apply_symm_apply (π ε)]
    change (zagResidualMergeOrder e π m ε hε hthird).symm (e l) = q
    rw [zagResidualMergeOrder_symm_apply,
      zagBlockSwap_symm_apply_right]
  have hfirst : e' m.first = e m.first := by
    change zagResidualMergeOrder e π m ε hε hthird m.first = e m.first
    simp [zagResidualMergeOrder, Equiv.Perm.mul_apply,
      zagBlockSwap_apply_left]
  have hlast : e' l = e m.middle := by
    change e ((zagBlockSwap m.first m.middle (e.symm (π ε))
      m.first_lt_middle (zagResidual_middle_lt_image m ε hε hthird))
        (e.symm (π ε))) = e m.middle
    rw [zagBlockSwap_apply_right]
  have hpow :
      (π' ^ zagReturnTime π (e m.middle)) (e m.first) = e m.middle := by
    have hp := zagTriangle_merge_pow_left π hab hac hbc
      (zagReturnTime_pos π (e m.middle))
      (le_refl (zagReturnTime π (e m.middle)))
    have hp' : (π' ^ zagReturnTime π (e m.middle)) (e m.first) =
        (π ^ zagReturnTime π (e m.middle)) (e m.middle) := by
      simpa only [π', zagResidualMergeVertical] using hp
    exact hp'.trans (zagReturnTime_spec π (e m.middle))
  change l ∈ Finset.univ.filter fun i =>
    e'.symm (π' ε) < i ∧ ∃ t : ℕ,
      0 < t ∧ t < zagCutHit e' π' ε ∧
        (π' ^ t) (e' (zagCycleMinPos e' π' ε)) = e' i
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_, zagReturnTime π (e m.middle),
    zagReturnTime_pos π (e m.middle), ?_, ?_⟩
  · rw [hpos_image]
    exact (zagBlockMiddle_bounds m.first m.middle l m.first_lt_middle
      (zagResidual_middle_lt_image m ε hε hthird)).2
  · rw [zagResidualMerge_cutHit]
    have hcpos := zagReturnTime_pos π (π ε)
    omega
  · rw [hmin, hfirst, hlast]
    exact hpow

theorem zagResidualMerge_cutCandidate_ge_last {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hthird : zagCycleMinPos e π ε = m.third) {x : Fin n}
    (hx : x ∈ zagCutCandidates
      (zagResidualMergeOrder e π m ε hε hthird)
      (zagResidualMergeVertical e π m ε) ε) :
    e.symm (π ε) ≤ x := by
  classical
  let e' := zagResidualMergeOrder e π m ε hε hthird
  let π' := zagResidualMergeVertical e π m ε
  let l := e.symm (π ε)
  let q := zagBlockMiddle m.first m.middle l m.first_lt_middle
    (zagResidual_middle_lt_image m ε hε hthird)
  let Lb := zagReturnTime π (e m.middle)
  let Lc := zagReturnTime π (π ε)
  obtain ⟨hab, hac, hbc⟩ := zagResidual_critical_pairwise m ε hthird
  have hmin : zagCycleMinPos e' π' ε = m.first :=
    zagResidualMerge_cycleMinPos e π m ε hε hthird
  have hfirst : e' m.first = e m.first := by
    change zagResidualMergeOrder e π m ε hε hthird m.first = e m.first
    simp [zagResidualMergeOrder, Equiv.Perm.mul_apply,
      zagBlockSwap_apply_left]
  have hpos_image : e'.symm (π' ε) = q := by
    have happ : π' ε = π ε :=
      zagResidualMergeVertical_apply_point e π m ε hε hthird
    rw [happ, ← e.apply_symm_apply (π ε)]
    change (zagResidualMergeOrder e π m ε hε hthird).symm (e l) = q
    rw [zagResidualMergeOrder_symm_apply,
      zagBlockSwap_symm_apply_right]
  change x ∈ Finset.univ.filter (fun i =>
    e'.symm (π' ε) < i ∧ ∃ t : ℕ,
      0 < t ∧ t < zagCutHit e' π' ε ∧
        (π' ^ t) (e' (zagCycleMinPos e' π' ε)) = e' i) at hx
  obtain ⟨hqx, t, ht0, htcut, hpath⟩ := (Finset.mem_filter.mp hx).2
  rw [hpos_image] at hqx
  have ht : t < Lb + Lc := by
    rw [zagResidualMerge_cutHit] at htcut
    exact htcut
  rw [hmin, hfirst] at hpath
  have horder : e' x = e ((zagBlockSwap m.first m.middle l
      m.first_lt_middle (zagResidual_middle_lt_image m ε hε hthird)) x) := by
    change e ((zagBlockSwap m.first m.middle (e.symm (π ε))
      m.first_lt_middle (zagResidual_middle_lt_image m ε hε hthird)) x) =
        e ((zagBlockSwap m.first m.middle l m.first_lt_middle
          (zagResidual_middle_lt_image m ε hε hthird)) x)
    rfl
  by_cases htb : t ≤ Lb
  · have hp := zagTriangle_merge_pow_left π hab hac hbc ht0 htb
    have hp' : (π' ^ t) (e m.first) = (π ^ t) (e m.middle) := by
      simpa only [π', zagResidualMergeVertical] using hp
    have heq : (π ^ t) (e m.middle) = e' x := hp'.symm.trans hpath
    have hcycle : π.SameCycle (e m.middle) ((π ^ t) (e m.middle)) :=
      ⟨(t : ℤ), by rw [zpow_natCast]⟩
    have hle := zagCycleMinPos_le e π hcycle.symm
    have hmiddle := (zag_mem_cycleMinima_iff e π m.middle).mp m.middle_mem
    rw [hmiddle, heq, horder, e.symm_apply_apply] at hle
    exact zagBlockSwap_right_of_middle_le _ _ _ _
      m.first_lt_middle (zagResidual_middle_lt_image m ε hε hthird) hqx hle
  · let s := t - Lb
    have hs0 : 0 < s := by omega
    have hslt : s < Lc := by omega
    have hp := zagTriangle_merge_pow_after_left π hab hac hbc hs0 hslt.le
    have hp' : (π' ^ t) (e m.first) = (π ^ s) (π ε) := by
      simpa only [π', zagResidualMergeVertical, Lb, Lc, s,
        show Lb + (t - Lb) = t by omega] using hp
    have heq : (π ^ s) (π ε) = e' x := hp'.symm.trans hpath
    have hcycle : π.SameCycle (π ε) ((π ^ s) (π ε)) :=
      ⟨(s : ℤ), by rw [zpow_natCast]⟩
    have hle := zagCycleMinPos_le e π hcycle.symm
    have himage : zagCycleMinPos e π (π ε) = m.third := by
      rw [zagCycleMinPos_eq_of_sameCycle e π
        ((Equiv.Perm.SameCycle.rfl : π.SameCycle ε ε).apply_left), hthird]
    rw [himage, heq, horder, e.symm_apply_apply] at hle
    have hmiddle_le := m.middle_lt_third.le.trans hle
    exact zagBlockSwap_right_of_middle_le _ _ _ _
      m.first_lt_middle (zagResidual_middle_lt_image m ε hε hthird)
      hqx hmiddle_le

theorem zagResidualMerge_cutPos {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hthird : zagCycleMinPos e π ε = m.third) :
    let e' := zagResidualMergeOrder e π m ε hε hthird
    let π' := zagResidualMergeVertical e π m ε
    let hε' := zagResidualMergePoint_nontrivialAntiExceedance
      e π m ε hε hthird
    zagCutPos e' π' ε hε' = e.symm (π ε) := by
  let e' := zagResidualMergeOrder e π m ε hε hthird
  let π' := zagResidualMergeVertical e π m ε
  let hε' := zagResidualMergePoint_nontrivialAntiExceedance
    e π m ε hε hthird
  apply le_antisymm
  · apply zagCutPos_min e' π' ε hε'
    exact zagResidualMerge_last_mem_cutCandidates e π m ε hε hthird
  · apply zagResidualMerge_cutCandidate_ge_last e π m ε hε hthird
    exact zagCutPos_mem e' π' ε hε'

theorem zagResidualSlice_merge_order {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hthird : zagCycleMinPos e π ε = m.third) :
    let e' := zagResidualMergeOrder e π m ε hε hthird
    let π' := zagResidualMergeVertical e π m ε
    let hε' := zagResidualMergePoint_nontrivialAntiExceedance
      e π m ε hε hthird
    zagSliceOrder e' π' ε hε' = e := by
  let e' := zagResidualMergeOrder e π m ε hε hthird
  let π' := zagResidualMergeVertical e π m ε
  let l := e.symm (π ε)
  let q := zagBlockMiddle m.first m.middle l m.first_lt_middle
    (zagResidual_middle_lt_image m ε hε hthird)
  let hε' := zagResidualMergePoint_nontrivialAntiExceedance
    e π m ε hε hthird
  have hmin : zagCycleMinPos e' π' ε = m.first :=
    zagResidualMerge_cycleMinPos e π m ε hε hthird
  have happ : π' ε = π ε :=
    zagResidualMergeVertical_apply_point e π m ε hε hthird
  have himage : e'.symm (π' ε) = q := by
    rw [happ, ← e.apply_symm_apply (π ε)]
    change (zagResidualMergeOrder e π m ε hε hthird).symm (e l) = q
    rw [zagResidualMergeOrder_symm_apply,
      zagBlockSwap_symm_apply_right]
  have hcut : zagCutPos e' π' ε hε' = l :=
    zagResidualMerge_cutPos e π m ε hε hthird
  change e' * zagBlockSwap (zagCycleMinPos e' π' ε) (e'.symm (π' ε))
      (zagCutPos e' π' ε hε') _ _ = e
  simp only [hmin, himage, hcut]
  change (e * zagBlockSwap m.first m.middle (e.symm (π ε))
      m.first_lt_middle (zagResidual_middle_lt_image m ε hε hthird)) *
    zagBlockSwap m.first
      (zagBlockMiddle m.first m.middle (e.symm (π ε))
        m.first_lt_middle (zagResidual_middle_lt_image m ε hε hthird))
      (e.symm (π ε)) _ _ = e
  rw [mul_assoc, zagBlockSwap_mul_reverse, mul_one]

theorem zagResidualSlice_merge_vertical {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hthird : zagCycleMinPos e π ε = m.third) :
    let e' := zagResidualMergeOrder e π m ε hε hthird
    let π' := zagResidualMergeVertical e π m ε
    let hε' := zagResidualMergePoint_nontrivialAntiExceedance
      e π m ε hε hthird
    zagSliceVertical e' π' ε hε' = π := by
  let e' := zagResidualMergeOrder e π m ε hε hthird
  let π' := zagResidualMergeVertical e π m ε
  let l := e.symm (π ε)
  let hε' := zagResidualMergePoint_nontrivialAntiExceedance
    e π m ε hε hthird
  have hmin : zagCycleMinPos e' π' ε = m.first :=
    zagResidualMerge_cycleMinPos e π m ε hε hthird
  have happ : π' ε = π ε :=
    zagResidualMergeVertical_apply_point e π m ε hε hthird
  have hcut : zagCutPos e' π' ε hε' = l :=
    zagResidualMerge_cutPos e π m ε hε hthird
  have hfirst : e' m.first = e m.first := by
    change zagResidualMergeOrder e π m ε hε hthird m.first = e m.first
    simp [zagResidualMergeOrder, Equiv.Perm.mul_apply,
      zagBlockSwap_apply_left]
  have hlast : e' l = e m.middle := by
    change e ((zagBlockSwap m.first m.middle (e.symm (π ε))
      m.first_lt_middle (zagResidual_middle_lt_image m ε hε hthird))
        (e.symm (π ε))) = e m.middle
    rw [zagBlockSwap_apply_right]
  obtain ⟨hfm, hfb, hmb⟩ := zagResidual_critical_pairwise m ε hthird
  have hfm_ne : e m.first ≠ e m.middle := fun h => hfm (h.sameCycle π)
  have hfb_ne : e m.first ≠ π ε := fun h => hfb (h.sameCycle π)
  have hmb_ne : e m.middle ≠ π ε := fun h => hmb (h.sameCycle π)
  change π' * zagTriangle (e' (zagCycleMinPos e' π' ε)) (π' ε)
      (e' (zagCutPos e' π' ε hε')) = π
  simp only [hmin, happ, hcut, hfirst, hlast]
  change (π * zagTriangle (e m.first) (e m.middle) (π ε)) *
      zagTriangle (e m.first) (π ε) (e m.middle) = π
  rw [mul_assoc, zagTriangle_mul_reverse hfm_ne hfb_ne hmb_ne, mul_one]

theorem zagResidualSlice_merge_marked {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hthird : zagCycleMinPos e π ε = m.third) :
    let e' := zagResidualMergeOrder e π m ε hε hthird
    let π' := zagResidualMergeVertical e π m ε
    let hε' := zagResidualMergePoint_nontrivialAntiExceedance
      e π m ε hε hthird
    zagSliceMarked e' π' ε hε' = m.toFinset := by
  let e' := zagResidualMergeOrder e π m ε hε hthird
  let π' := zagResidualMergeVertical e π m ε
  let l := e.symm (π ε)
  let q := zagBlockMiddle m.first m.middle l m.first_lt_middle
    (zagResidual_middle_lt_image m ε hε hthird)
  let hε' := zagResidualMergePoint_nontrivialAntiExceedance
    e π m ε hε hthird
  have hmin : zagCycleMinPos e' π' ε = m.first :=
    zagResidualMerge_cycleMinPos e π m ε hε hthird
  have happ : π' ε = π ε :=
    zagResidualMergeVertical_apply_point e π m ε hε hthird
  have himage : e'.symm (π' ε) = q := by
    rw [happ, ← e.apply_symm_apply (π ε)]
    change (zagResidualMergeOrder e π m ε hε hthird).symm (e l) = q
    rw [zagResidualMergeOrder_symm_apply,
      zagBlockSwap_symm_apply_right]
  have hcut : zagCutPos e' π' ε hε' = l :=
    zagResidualMerge_cutPos e π m ε hε hthird
  have hmiddle_reverse :
      zagBlockMiddle m.first
        (zagBlockMiddle m.first m.middle l m.first_lt_middle
          (zagResidual_middle_lt_image m ε hε hthird)) l _ _ = m.middle :=
    zagBlockMiddle_reverse m.first m.middle l m.first_lt_middle
      (zagResidual_middle_lt_image m ε hε hthird)
  have horder : zagSliceOrder e' π' ε hε' = e :=
    zagResidualSlice_merge_order e π m ε hε hthird
  have hvertical : zagSliceVertical e' π' ε hε' = π :=
    zagResidualSlice_merge_vertical e π m ε hε hthird
  have hres : zagNontrivialAntiExceedance
      (zagSliceOrder e' π' ε hε') (zagSliceVertical e' π' ε hε') ε := by
    simpa only [horder, hvertical] using hε
  have hs := zagSliceMarked_eq_residual e' π' ε hε' hres
  dsimp only at hs
  simpa only [hmin, himage, hcut, q, l, hmiddle_reverse, horder, hvertical,
    hthird, ZagMarkedTriple.toFinset] using hs

theorem zagCycleMinimum_not_nontrivialAntiExceedance {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (i : Fin n)
    (hi : i ∈ zagCycleMinima e π) :
    ¬zagNontrivialAntiExceedance e π (e i) := by
  intro hε
  have hmin := (zag_mem_cycleMinima_iff e π i).mp hi
  by_cases hfix : π (e i) = e i
  · apply hε.2
    simp only [zagTrivialAntiExceedance, hmin, hfix]
  · apply hε.1
    simp only [zagExceedance, e.symm_apply_apply]
    have hsame : π.SameCycle (π (e i)) (e i) :=
      (Equiv.Perm.SameCycle.rfl : π.SameCycle (e i) (e i)).apply_left
    have hle := zagCycleMinPos_le e π hsame
    rw [hmin] at hle
    exact lt_of_le_of_ne hle fun heq =>
      hfix (e.symm.injective (by simpa using heq.symm))

theorem zagMergePoint_not_nontrivialAntiExceedance {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (m : ZagMarkedTriple e π) :
    ¬zagNontrivialAntiExceedance e π (zagMergePoint e π m) := by
  by_cases hfix : π.symm (e m.third) = e m.third
  · have hpoint := zagMergePoint_eq_middle_of_fixed e π m hfix
    rw [hpoint]
    exact zagCycleMinimum_not_nontrivialAntiExceedance e π m.middle m.middle_mem
  · intro hε
    have hpoint := zagMergePoint_eq_preimage_of_not_fixed e π m hfix
    apply hε.2
    simp only [zagTrivialAntiExceedance]
    have hsame : π.SameCycle (zagMergePoint e π m) (e m.third) := by
      rw [hpoint]
      exact (Equiv.Perm.SameCycle.rfl :
        π.SameCycle (e m.third) (e m.third)).symm_apply_left
    have hmin := zagCycleMinPos_eq_of_sameCycle e π hsame
    have hthird := (zag_mem_cycleMinima_iff e π m.third).mp m.third_mem
    rw [hmin, hthird, hpoint, π.apply_symm_apply]

end MetaMathlibExt
