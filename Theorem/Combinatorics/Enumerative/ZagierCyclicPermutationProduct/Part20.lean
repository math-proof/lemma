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
import Def.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part20
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

theorem zagSliceVertical_eq {n : ℕ}
    (D e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hπ : π = zagVertical D e) :
    zagSliceVertical e π ε hε = zagVertical D (zagSliceOrder e π ε hε) := by
  let i := zagCycleMinPos e π ε
  let j := e.symm (π ε)
  let l := zagCutPos e π ε hε
  let hij : i < j := zagNTAE_min_lt_image e π hε
  let hjl : j < l := zagImage_lt_cutPos e π ε hε
  calc
    zagSliceVertical e π ε hε =
        π * zagTriangle (e i) (e j) (e l) := by
      simp only [zagSliceVertical, i, j, l, e.apply_symm_apply]
    _ = zagVertical D e * zagTriangle (e i) (e j) (e l) := by rw [hπ]
    _ = zagVertical D (e * zagBlockSwap i j l hij hjl) := by
      rw [zagVertical_blockSwap]
    _ = zagVertical D (zagSliceOrder e π ε hε) := by
      rfl

theorem zagSliceOrder_apply_zero {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε) :
    let z : Fin n := ⟨0, lt_of_le_of_lt (Nat.zero_le _) ε.isLt⟩
    zagSliceOrder e π ε hε z = e z := by
  dsimp only
  have hz : (⟨0, lt_of_le_of_lt (Nat.zero_le _) ε.isLt⟩ : Fin n) ≤
      zagCycleMinPos e π ε := by
    rw [Fin.le_iff_val_le_val]
    exact Nat.zero_le _
  simp [zagSliceOrder, Equiv.Perm.mul_apply, zagBlockSwap,
    zagBlockSwapNat, hz]

theorem zagSliceOrder_apply_left {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε) :
    zagSliceOrder e π ε hε (zagCycleMinPos e π ε) =
      e (zagCycleMinPos e π ε) := by
  exact congrArg e (zagBlockSwap_apply_left _ _ _ _ _)

theorem zagSliceOrder_apply_middle {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε) :
    let i := zagCycleMinPos e π ε
    let j := e.symm (π ε)
    let l := zagCutPos e π ε hε
    let hij := zagNTAE_min_lt_image e π hε
    let hjl := zagImage_lt_cutPos e π ε hε
    zagSliceOrder e π ε hε (zagBlockMiddle i j l hij hjl) = e l := by
  dsimp only
  exact congrArg e (zagBlockSwap_apply_middle _ _ _ _ _)

theorem zagSliceOrder_apply_right {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε) :
    zagSliceOrder e π ε hε (zagCutPos e π ε hε) = π ε := by
  calc
    zagSliceOrder e π ε hε (zagCutPos e π ε hε) =
        e (e.symm (π ε)) :=
      congrArg e (zagBlockSwap_apply_right _ _ _ _ _)
    _ = π ε := e.apply_symm_apply _

theorem zagSliceVertical_count {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε) :
    cycleQuotientCount (zagSliceVertical e π ε hε) =
      cycleQuotientCount π + 2 :=
  zagNTAE_triangle_count e π ε hε

theorem zagSliceVertical_pairwise {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε) :
    let π' := zagSliceVertical e π ε hε
    let a := e (zagCycleMinPos e π ε)
    let b := π ε
    let c := e (zagCutPos e π ε hε)
    ¬π'.SameCycle a b ∧ ¬π'.SameCycle a c ∧
      ¬π'.SameCycle b c := by
  let a := e (zagCycleMinPos e π ε)
  let b := π ε
  let c := e (zagCutPos e π ε hε)
  have habpos : e.symm a < e.symm b := by
    simpa [a, b] using zagNTAE_min_lt_image e π hε
  have hbcpos : e.symm b < e.symm c := by
    simpa [b, c] using zagImage_lt_cutPos e π ε hε
  have hac_ne : a ≠ c := fun h => by
    have := congrArg e.symm h
    omega
  have hab_ne : a ≠ b := fun h => by
    have := congrArg e.symm h
    omega
  have hac : π.SameCycle a c := by
    obtain ⟨t, _, _, ht⟩ := zagCutPos_path e π ε hε
    exact ⟨(t : ℤ), by simpa [a, c] using ht⟩
  simpa only [zagSliceVertical, a, b, c] using
    zagTriangle_split_pairwise π hac_ne hac hab_ne
      (by simpa [a, b, c] using zagCutAfterSwap_same_image e π ε hε)

theorem zagSliceVertical_sameCycle_refines {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε) {x y : Fin n}
    (hxy : (zagSliceVertical e π ε hε).SameCycle x y) :
    π.SameCycle x y := by
  let a := e (zagCycleMinPos e π ε)
  let b := π ε
  let c := e (zagCutPos e π ε hε)
  have hac : π.SameCycle a c := by
    obtain ⟨t, _, _, ht⟩ := zagCutPos_path e π ε hε
    exact ⟨(t : ℤ), by simpa [a, c] using ht⟩
  have hab : (π * Equiv.swap a c).SameCycle a b := by
    simpa [a, b, c] using zagCutAfterSwap_same_image e π ε hε
  exact zagSameCycle_mul_triangle_refines π hac hab (by
    simpa only [zagSliceVertical, a, b, c] using hxy)

theorem zagSlice_cycleMinPos_left {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε) :
    zagCycleMinPos (zagSliceOrder e π ε hε)
        (zagSliceVertical e π ε hε)
        (e (zagCycleMinPos e π ε)) =
      zagCycleMinPos e π ε := by
  let i := zagCycleMinPos e π ε
  let j := e.symm (π ε)
  let l := zagCutPos e π ε hε
  let hij : i < j := zagNTAE_min_lt_image e π hε
  let hjl : j < l := zagImage_lt_cutPos e π ε hε
  let B := zagBlockSwap i j l hij hjl
  let e' := zagSliceOrder e π ε hε
  let π' := zagSliceVertical e π ε hε
  let a := e i
  let m := zagCycleMinPos e' π' a
  have heim : e.symm (e' m) = B m := by
    simp only [e', zagSliceOrder, B, i, j, l,
      Equiv.Perm.mul_apply, e.symm_apply_apply]
  have hma : π'.SameCycle (e' m) a := zagCycleMinPos_mem e' π' a
  have hma_old : π.SameCycle (e' m) a :=
    zagSliceVertical_sameCycle_refines e π ε hε hma
  have hmina : zagCycleMinPos e π a = i := by
    exact (zagCycleMinPos_eq_of_sameCycle e π
      (zagCycleMinPos_mem e π ε)).trans rfl
  have himage : i ≤ e.symm (e' m) := by
    simpa only [hmina] using zagCycleMinPos_le e π hma_old
  have him : i ≤ m := by
    apply (zagBlockSwap_preserves_leftCut i j l m hij hjl).mp
    simpa [B, heim] using himage
  have hei : e' i = a := by
    simpa [e', a, i] using zagSliceOrder_apply_left e π ε hε
  have hmi : m ≤ i := by
    have hle := zagCycleMinPos_le e' π'
      (Equiv.Perm.SameCycle.rfl : π'.SameCycle a a)
    have hinv : e'.symm a = i := by
      apply e'.injective
      simp [hei]
    simpa [m, hinv] using hle
  exact le_antisymm hmi him

theorem zagSlice_cycleMinPos_before {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε r : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hr : r ∈ zagCycleMinima e π)
    (hri : r < zagCycleMinPos e π ε) :
    r ∈ zagCycleMinima (zagSliceOrder e π ε hε)
      (zagSliceVertical e π ε hε) := by
  classical
  let i := zagCycleMinPos e π ε
  let j := e.symm (π ε)
  let l := zagCutPos e π ε hε
  let hij : i < j := zagNTAE_min_lt_image e π hε
  let hjl : j < l := zagImage_lt_cutPos e π ε hε
  let e' := zagSliceOrder e π ε hε
  let π' := zagSliceVertical e π ε hε
  have her : e' r = e r := by
    simp only [e', zagSliceOrder, Equiv.Perm.mul_apply]
    congr 1
    apply Fin.ext
    simp [zagBlockSwap_val, zagBlockSwapNat,
      show (r : ℕ) ≤ (zagCycleMinPos e π ε : ℕ) from hri.le]
  rw [zag_mem_cycleMinima_iff] at hr ⊢
  let m := zagCycleMinPos e' π' (e' r)
  have hmcycle : π.SameCycle (e' m) (e r) := by
    apply zagSliceVertical_sameCycle_refines e π ε hε
    rw [← her]
    exact zagCycleMinPos_mem e' π' (e' r)
  have hpos : r ≤ e.symm (e' m) := by
    have hle := zagCycleMinPos_le e π hmcycle
    rwa [hr] at hle
  have hrm : r ≤ m := by
    by_cases hmi : m < i
    · have hem : e' m = e m := by
        simp only [e', zagSliceOrder, Equiv.Perm.mul_apply]
        congr 1
        apply Fin.ext
        simp [zagBlockSwap_val, zagBlockSwapNat,
          show (m : ℕ) ≤ (zagCycleMinPos e π ε : ℕ) from hmi.le]
      rwa [hem, e.symm_apply_apply] at hpos
    · exact hri.le.trans (le_of_not_gt hmi)
  have hmr : m ≤ r := by
    have hle := zagCycleMinPos_le e' π'
      (Equiv.Perm.SameCycle.rfl : π'.SameCycle (e' r) (e' r))
    simpa only [e'.symm_apply_apply] using hle
  exact le_antisymm hmr hrm

theorem zagSlice_cycleMinPos_middle {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε) :
    let i := zagCycleMinPos e π ε
    let j := e.symm (π ε)
    let l := zagCutPos e π ε hε
    let hij := zagNTAE_min_lt_image e π hε
    let hjl := zagImage_lt_cutPos e π ε hε
    zagCycleMinPos (zagSliceOrder e π ε hε)
        (zagSliceVertical e π ε hε) (e l) =
      zagBlockMiddle i j l hij hjl := by
  classical
  dsimp only
  let i := zagCycleMinPos e π ε
  let j := e.symm (π ε)
  let l := zagCutPos e π ε hε
  let hij : i < j := zagNTAE_min_lt_image e π hε
  let hjl : j < l := zagImage_lt_cutPos e π ε hε
  let B := zagBlockSwap i j l hij hjl
  let q := zagBlockMiddle i j l hij hjl
  let e' := zagSliceOrder e π ε hε
  let π' := zagSliceVertical e π ε hε
  let a := e i
  let b := π ε
  let c := e l
  let h := π * Equiv.swap a c
  let m := zagCycleMinPos e' π' c
  have hac_ne : a ≠ c := fun hac => by
    have := congrArg e.symm hac
    simp only [a, c, e.symm_apply_apply] at this
    omega
  obtain ⟨t, ht0, htH, htc⟩ := zagCutPos_path e π ε hε
  have hac : π.SameCycle a c :=
    ⟨(t : ℤ), by simpa [a, c, i, l] using htc⟩
  have hab : h.SameCycle a b := by
    simpa [h, a, b, c, i, l] using zagCutAfterSwap_same_image e π ε hε
  have hma : π'.SameCycle (e' m) c := zagCycleMinPos_mem e' π' c
  have hmc : h.SameCycle (e' m) c := by
    apply zagSameCycle_mul_swap_refines h hab
    simpa only [π', zagSliceVertical, h, a, b, c, i, l,
      zagTriangle, mul_assoc] using hma
  obtain ⟨r, hr0, hrT, hrx⟩ :=
    zagMulSwap_sameCycle_right_arc π hac_ne hac hmc.symm
  have hTlt : zagCycleHit π a c hac < zagCutHit e π ε := by
    have hTle := zagCycleHit_minimal π a c hac (by
      simpa [a, c, i, l] using htc)
    omega
  have hrH : r < zagCutHit e π ε := lt_of_le_of_lt hrT hTlt
  let p := e.symm (e' m)
  have hpB : p = B m := by
    simp only [p, e', zagSliceOrder, B, i, j, l,
      Equiv.Perm.mul_apply, e.symm_apply_apply]
  have hnot_ac : ¬h.SameCycle a c := by
    exact zagMulSwap_not_sameCycle π hac_ne hac
  have hp_ne : p ≠ i := by
    intro hpi
    have hem : e' m = a := by
      apply e.symm.injective
      simp [p, a, hpi]
    exact hnot_ac (by simpa [hem] using hmc)
  have hmina : zagCycleMinPos e π a = i := by
    exact (zagCycleMinPos_eq_of_sameCycle e π
      (zagCycleMinPos_mem e π ε)).trans rfl
  have hminc : zagCycleMinPos e π c = i := by
    exact (zagCycleMinPos_eq_of_sameCycle e π hac).symm.trans hmina
  have hip_le : i ≤ p := by
    have hold : π.SameCycle (e' m) c :=
      zagSliceVertical_sameCycle_refines e π ε hε hma
    simpa only [hminc, p] using zagCycleMinPos_le e π hold
  have hip : i < p := lt_of_le_of_ne hip_le (Ne.symm hp_ne)
  have hp_side : p ≤ j ∨ l ≤ p := by
    by_cases hpj : p ≤ j
    · exact Or.inl hpj
    · right
      apply zagCutPos_min e π ε hε
      rw [zagCutCandidates, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, lt_of_not_ge hpj, r, hr0, hrH, ?_⟩
      calc
        (π ^ r) (e (zagCycleMinPos e π ε)) = (π ^ r) a := by
          simp only [a, i]
        _ = e' m := hrx
        _ = e p := by simp only [p, e.apply_symm_apply]
  have hqm : q ≤ m := by
    have hq := zagBlockMiddle_le_unswap i j l p hij hjl hip hp_side
    have hm : B.symm p = m := by
      apply B.injective
      simp [hpB]
    simpa [q, B, hm] using hq
  have heq : e' q = c := by
    simpa [e', q, c, i, j, l] using
      zagSliceOrder_apply_middle e π ε hε
  have hmq : m ≤ q := by
    have hle := zagCycleMinPos_le e' π'
      (Equiv.Perm.SameCycle.rfl : π'.SameCycle c c)
    have hinv : e'.symm c = q := by
      apply e'.injective
      simp [heq]
    simpa [m, hinv] using hle
  exact le_antisymm hmq hqm

theorem zagSlice_residual_ne_cut {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hres : zagNontrivialAntiExceedance
      (zagSliceOrder e π ε hε) (zagSliceVertical e π ε hε) ε) :
    e (zagCutPos e π ε hε) ≠ ε := by
  let i := zagCycleMinPos e π ε
  let j := e.symm (π ε)
  let l := zagCutPos e π ε hε
  let hij : i < j := zagNTAE_min_lt_image e π hε
  let hjl : j < l := zagImage_lt_cutPos e π ε hε
  let q := zagBlockMiddle i j l hij hjl
  let e' := zagSliceOrder e π ε hε
  let π' := zagSliceVertical e π ε hε
  let c := e l
  intro hcε
  have heq : e' q = ε := by
    rw [← hcε]
    simpa [e', q, c, i, j, l] using
      zagSliceOrder_apply_middle e π ε hε
  have hmin : zagCycleMinPos e' π' ε = q := by
    rw [← hcε]
    simpa [e', π', q, c, i, j, l] using
      zagSlice_cycleMinPos_middle e π ε hε
  by_cases hfix : π' ε = ε
  · apply hres.2
    change π' ε = e' (zagCycleMinPos e' π' ε)
    rw [hfix, hmin, heq]
  · apply hres.1
    simp only [zagExceedance]
    have hsame : π'.SameCycle (π' ε) ε :=
      (Equiv.Perm.SameCycle.rfl : π'.SameCycle ε ε).apply_left
    have hle : q ≤ e'.symm (π' ε) := by
      simpa only [hmin] using zagCycleMinPos_le e' π' hsame
    have hne : e'.symm (π' ε) ≠ q := fun he => by
      apply hfix
      calc
        π' ε = e' (e'.symm (π' ε)) := (e'.apply_symm_apply _).symm
        _ = e' q := by rw [he]
        _ = ε := heq
    have heps : e'.symm ε = q := by
      apply e'.injective
      simp [heq]
    rw [heps]
    exact lt_of_le_of_ne hle hne.symm

theorem zagSlice_residual_apply {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hres : zagNontrivialAntiExceedance
      (zagSliceOrder e π ε hε) (zagSliceVertical e π ε hε) ε) :
    zagSliceVertical e π ε hε ε = π ε := by
  let a := e (zagCycleMinPos e π ε)
  let b := π ε
  let c := e (zagCutPos e π ε hε)
  have hae : a ≠ ε := fun hae => by
    have hp := congrArg e.symm hae
    have h1 := zagNTAE_min_lt_image e π hε
    have h2 := zagNTAE_image_lt e π hε
    simp only [a, e.symm_apply_apply] at hp
    omega
  have hbe : b ≠ ε := fun hbe => by
    have hp := congrArg e.symm hbe
    have h2 := zagNTAE_image_lt e π hε
    simp only [b] at hp
    omega
  have hce : c ≠ ε := zagSlice_residual_ne_cut e π ε hε hres
  change π (zagTriangle a b c ε) = π ε
  simp only [zagTriangle, Equiv.Perm.mul_apply,
    Equiv.swap_apply_of_ne_of_ne hae.symm hbe.symm,
    Equiv.swap_apply_of_ne_of_ne hae.symm hce.symm]

theorem zagSlice_residual_min_gt_middle {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hres : zagNontrivialAntiExceedance
      (zagSliceOrder e π ε hε) (zagSliceVertical e π ε hε) ε) :
    let i := zagCycleMinPos e π ε
    let j := e.symm (π ε)
    let l := zagCutPos e π ε hε
    let hij := zagNTAE_min_lt_image e π hε
    let hjl := zagImage_lt_cutPos e π ε hε
    zagBlockMiddle i j l hij hjl <
      zagCycleMinPos (zagSliceOrder e π ε hε)
        (zagSliceVertical e π ε hε) ε := by
  classical
  dsimp only
  let i := zagCycleMinPos e π ε
  let j := e.symm (π ε)
  let l := zagCutPos e π ε hε
  let hij : i < j := zagNTAE_min_lt_image e π hε
  let hjl : j < l := zagImage_lt_cutPos e π ε hε
  let B := zagBlockSwap i j l hij hjl
  let q := zagBlockMiddle i j l hij hjl
  let e' := zagSliceOrder e π ε hε
  let g := zagSliceVertical e π ε hε
  let a := e i
  let b := π ε
  let c := e l
  let hab : π.SameCycle a b := (zagCycleMinPos_mem e π ε).apply_right
  obtain ⟨t, ht0, htCut, htc⟩ := zagCutPos_path e π ε hε
  let hac : π.SameCycle a c := ⟨(t : ℤ), by simpa [a, c, i, l] using htc⟩
  let T := zagCycleHit π a c hac
  let H := zagCycleHit π a b hab
  let h := π * Equiv.swap a c
  let habh : h.SameCycle a b := by
    simpa [h, a, b, c, i, l] using zagCutAfterSwap_same_image e π ε hε
  let d := zagCycleMinPos e' g ε
  let x := e' d
  have hH : H = zagCutHit e π ε := by
    rfl
  have hTlt : T < H := by
    have hTle := zagCycleHit_minimal π a c hac (by
      simpa [a, c, i, l] using htc)
    rw [hH]
    omega
  have hg_apply : g ε = b := by
    simpa [g, b] using zagSlice_residual_apply e π ε hε hres
  have hxd : g.SameCycle x ε := zagCycleMinPos_mem e' g ε
  have hbx : g.SameCycle b x := by
    have hbε : g.SameCycle b ε := by
      have hs := (Equiv.Perm.SameCycle.rfl : g.SameCycle ε ε).apply_right
      simpa [hg_apply] using hs.symm
    exact hbε.trans hxd.symm
  have hg_form : g = h * Equiv.swap a b := by
    simp only [g, zagSliceVertical, h, a, b, c, i, l,
      zagTriangle, mul_assoc]
  have hbx' : (h * Equiv.swap a b).SameCycle b x := by
    simpa only [← hg_form] using hbx
  have hab_ne : a ≠ b := fun hab_eq => by
    have hp := congrArg e.symm hab_eq
    simp only [a, b, i, e.symm_apply_apply] at hp
    omega
  obtain ⟨s, hs0, hsU, hsx⟩ :=
    zagMulSwap_sameCycle_right_arc h hab_ne habh hbx'
  have hHTpos : 0 < H - T := by omega
  have hhpow : (h ^ (H - T)) a = b := by
    rw [zagFirstSwap_pow_between π hab hac hTlt hHTpos le_rfl]
    have hadd : T + (H - T) = H := by omega
    rw [hadd, zagCycleHit_spec π a b hab]
  have hUle : zagCycleHit h a b habh ≤ H - T :=
    zagCycleHit_minimal h a b habh hhpow
  have hsle : s ≤ H - T := hsU.trans hUle
  have hsx_old : (π ^ (T + s)) a = x := by
    have hp := zagFirstSwap_pow_between π hab hac hTlt hs0 hsle
    exact hp.symm.trans hsx
  let p := e.symm x
  have hpB : p = B d := by
    simp only [p, x, e', zagSliceOrder, B, i, j, l,
      Equiv.Perm.mul_apply, e.symm_apply_apply]
  obtain ⟨hgab, hgac, hgbc⟩ := zagSliceVertical_pairwise e π ε hε
  have hxa : x ≠ a := fun hxa => hgab (by simpa [hxa] using hbx.symm)
  have hxc : x ≠ c := fun hxc => hgbc (by simpa [hxc] using hbx)
  have hxeps_old : π.SameCycle x ε :=
    zagSliceVertical_sameCycle_refines e π ε hε hxd
  have hminx : zagCycleMinPos e π x = i := by
    exact (zagCycleMinPos_eq_of_sameCycle e π hxeps_old).trans rfl
  have hip_le : i ≤ p := by
    simpa only [hminx, p] using zagCycleMinPos_le e π hxeps_old
  have hip : i < p := by
    apply lt_of_le_of_ne hip_le
    intro hip
    apply hxa
    apply e.symm.injective
    simp [p, a, hip]
  have hp_side : p ≤ j ∨ l ≤ p := by
    by_cases hpj : p ≤ j
    · exact Or.inl hpj
    · right
      have hrs_le : T + s ≤ H := by omega
      have hrs_ne : T + s ≠ H := by
        intro hrs
        have hxb : x = b := by
          rw [← hsx_old, hrs, zagCycleHit_spec π a b hab]
        have hpj_eq : p = j := by
          simp [p, j, b, hxb]
        exact hpj hpj_eq.le
      apply zagCutPos_min e π ε hε
      rw [zagCutCandidates, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, lt_of_not_ge hpj, T + s, by omega, ?_, ?_⟩
      · rw [← hH]
        exact lt_of_le_of_ne hrs_le hrs_ne
      · calc
          (π ^ (T + s)) (e (zagCycleMinPos e π ε)) =
              (π ^ (T + s)) a := by simp only [a, i]
          _ = x := hsx_old
          _ = e p := by simp only [p, e.apply_symm_apply]
  have hqd : q ≤ d := by
    have hq := zagBlockMiddle_le_unswap i j l p hij hjl hip hp_side
    have hd : B.symm p = d := by
      apply B.injective
      simp [hpB]
    simpa [q, B, hd] using hq
  have hqd_ne : q ≠ d := fun hqd_eq => by
    apply hxc
    have heq : e' q = c := by
      simpa [e', q, c, i, j, l] using
        zagSliceOrder_apply_middle e π ε hε
    simpa [x, hqd_eq] using heq
  exact lt_of_le_of_ne hqd hqd_ne

theorem zagSlice_terminal_cycleMinPos_right {n : ℕ}
    (e π : Equiv.Perm (Fin n)) (ε : Fin n)
    (hε : zagNontrivialAntiExceedance e π ε)
    (hterm : ¬zagNontrivialAntiExceedance
      (zagSliceOrder e π ε hε) (zagSliceVertical e π ε hε) ε) :
    zagCycleMinPos (zagSliceOrder e π ε hε)
        (zagSliceVertical e π ε hε) (π ε) =
      zagCutPos e π ε hε := by
  classical
  let i := zagCycleMinPos e π ε
  let j := e.symm (π ε)
  let l := zagCutPos e π ε hε
  let hij : i < j := zagNTAE_min_lt_image e π hε
  let hjl : j < l := zagImage_lt_cutPos e π ε hε
  let B := zagBlockSwap i j l hij hjl
  let e' := zagSliceOrder e π ε hε
  let g := zagSliceVertical e π ε hε
  let a := e i
  let b := π ε
  let c := e l
  let d := zagCycleMinPos e' g b
  have heb : e' l = b := by
    simpa [e', l, b] using zagSliceOrder_apply_right e π ε hε
  have hbinv : e'.symm b = l := by
    apply e'.injective
    simp [heb]
  have hdl : d ≤ l := by
    have hle := zagCycleMinPos_le e' g
      (Equiv.Perm.SameCycle.rfl : g.SameCycle b b)
    simpa [d, hbinv] using hle
  apply le_antisymm hdl
  by_contra hnle
  have hdl' : d < l := lt_of_not_ge hnle
  by_cases hcε : c = ε
  · have hab_ne : a ≠ b := fun hab => by
      have hp := congrArg e.symm hab
      simp only [a, b, i, e.symm_apply_apply] at hp
      omega
    have hac_ne : a ≠ c := fun hac => by
      have hp := congrArg e.symm hac
      simp only [a, c, i, l, e.symm_apply_apply] at hp
      omega
    have hbc_ne : b ≠ c := fun hbc => by
      have hp := congrArg e.symm hbc
      simp only [b, c, l, e.symm_apply_apply] at hp
      omega
    have hgb : g b = b := by
      change π (zagTriangle a b c b) = b
      have htri : zagTriangle a b c b = c := by
        simp [zagTriangle, Equiv.Perm.mul_apply]
      rw [htri, hcε]
    have hdb : e' d = b :=
      (zagCycleMinPos_mem e' g b).eq_of_right hgb
    have : d = l := by
      apply e'.injective
      simpa [heb] using hdb
    omega
  · have hae : a ≠ ε := fun hae => by
      have hp := congrArg e.symm hae
      have h1 := zagNTAE_min_lt_image e π hε
      have h2 := zagNTAE_image_lt e π hε
      simp only [a, i, e.symm_apply_apply] at hp
      omega
    have hbe : b ≠ ε := fun hbe => by
      have hp := congrArg e.symm hbe
      have h2 := zagNTAE_image_lt e π hε
      simp only [b] at hp
      omega
    have hge : g ε = b := by
      change π (zagTriangle a b c ε) = π ε
      simp only [zagTriangle, Equiv.Perm.mul_apply,
        Equiv.swap_apply_of_ne_of_ne hae.symm hbe.symm,
        Equiv.swap_apply_of_ne_of_ne hae.symm (Ne.symm hcε)]
    have hl_eps_le : l ≤ e.symm ε := by
      apply zagCutPos_min e π ε hε
      rw [zagCutCandidates, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, zagNTAE_image_lt e π hε,
        zagCutHit e π ε - 1, ?_, ?_, ?_⟩
      · have := zagCutHit_two_le e π hε
        omega
      · have := zagCutHit_two_le e π hε
        omega
      · simpa using zagCutHit_pred e π hε
    have hl_eps : l < e.symm ε := by
      apply lt_of_le_of_ne hl_eps_le
      intro heq
      apply hcε
      apply e.symm.injective
      simpa [c, l] using heq
    have heps : e'.symm ε = e.symm ε := by
      have hB := zagBlockSwap_symm_apply_of_right i j l (e.symm ε)
        hij hjl hl_eps
      change (e * B)⁻¹ ε = e.symm ε
      rw [mul_inv_rev, Equiv.Perm.mul_apply]
      exact hB
    have hanti : ¬zagExceedance e' g ε := by
      simp only [zagExceedance, hge, hbinv, heps]
      omega
    have hnontriv : ¬zagTrivialAntiExceedance e' g ε := by
      have hεb : g.SameCycle ε b := by
        have hs := (Equiv.Perm.SameCycle.rfl : g.SameCycle ε ε).apply_right
        simpa [hge] using hs
      have hmineps : zagCycleMinPos e' g ε = d :=
        zagCycleMinPos_eq_of_sameCycle e' g hεb
      simp only [zagTrivialAntiExceedance, hge]
      intro hbd
      have : l = d := by
        apply e'.injective
        calc
          e' l = b := heb
          _ = e' (zagCycleMinPos e' g ε) := hbd
          _ = e' d := by rw [hmineps]
      omega
    exact hterm ⟨hanti, hnontriv⟩

end MetaMathlibExt
