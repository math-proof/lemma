/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.BallSphere
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.UniformSpace.HeineCantor
import Def.Topology.Homotopy.BorsukUlam.Part5


namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

open Metric

/-- Inside cofacets preserve the sign set. -/
theorem bu_inside_sign {n : ℕ} {σ : Finset (Fin n → ℤ)} {t v : Fin n → ℤ}
    (htσ : t ∈ σ) (hSeq : bu_tkS σ = bu_tkSgn t)
    (hchain : bu_tkChain (insert v σ)) (htop : ∀ z ∈ σ, bu_tkLe z t)
    (hvt : bu_tkLe v t) :
    bu_tkS (insert v σ) = bu_tkS σ := by
  have hall : ∀ z ∈ insert v σ, bu_tkLe z t := by
    intro z hz
    rw [Finset.mem_insert] at hz
    rcases hz with hzv | hz
    · rw [hzv]
      exact hvt
    · exact htop z hz
  have h := bu_tkS_of_top hchain (Finset.mem_insert_of_mem htσ) hall
  rw [h, hSeq]

/-- Every comparable extension comes from an inside point. -/
theorem bu_ext_inside {n m : ℕ} {σ : Finset (Fin n → ℤ)} {b t : Fin n → ℤ}
    (hchainσ : bu_tkChain σ) (hbot : ∀ z ∈ σ, bu_tkLe b z)
    (htop : ∀ z ∈ σ, bu_tkLe z t) (hbt : bu_tkLe b t)
    (hSeq : bu_tkS σ = bu_tkSgn t) (hsub : σ ⊆ bu_tkBox n m)
    (hbσ : b ∈ σ) (htσ : t ∈ σ)
    {M : Finset (Fin n)}
    (hM : M ∈ bu_tkExt (σ.image (bu_tkMv b)) (bu_tkMv b t)) :
    bu_tkPt b t M ∈ bu_tkBox n m ∧ bu_tkPt b t M ∉ σ ∧
      bu_tkChain (insert (bu_tkPt b t M) σ) ∧
      bu_tkS (insert (bu_tkPt b t M) σ) = bu_tkS σ := by
  rw [bu_mem_tkExt] at hM
  obtain ⟨hMX, hMnot, hMcomp⟩ := hM
  have hMXs : M ⊆ bu_tkMv b t := Finset.mem_powerset.mp hMX
  have hPtm := bu_tkPt_mem_of_mem hbt hMXs
  have hPt1 : bu_tkLe b (bu_tkPt b t M) := hPtm.1
  have hPt2 : bu_tkLe (bu_tkPt b t M) t := hPtm.2.1
  have hPtMv : bu_tkMv b (bu_tkPt b t M) = M := hPtm.2.2
  have hPtbox : bu_tkPt b t M ∈ bu_tkBox n m := by
    have hbbox : b ∈ bu_tkBox n m := hsub hbσ
    have htbox : t ∈ bu_tkBox n m := hsub htσ
    rw [bu_mem_tkBox] at hbbox htbox ⊢
    intro i
    by_cases hMi : i ∈ M
    · have e : (bu_tkPt b t M) i = t i := by simp [bu_tkPt, hMi]
      rw [e]
      exact htbox i
    · have e : (bu_tkPt b t M) i = b i := by simp [bu_tkPt, hMi]
      rw [e]
      exact hbbox i
  have hPtnot : bu_tkPt b t M ∉ σ := by
    intro hcon
    have hmem : bu_tkMv b (bu_tkPt b t M) ∈ σ.image (bu_tkMv b) :=
      Finset.mem_image.mpr ⟨bu_tkPt b t M, hcon, rfl⟩
    rw [hPtMv] at hmem
    exact hMnot hmem
  have hcompPt : ∀ y ∈ σ, bu_tkLe (bu_tkPt b t M) y ∨ bu_tkLe y (bu_tkPt b t M) := by
    intro y hy
    have hMy : bu_tkMv b y ∈ σ.image (bu_tkMv b) :=
      Finset.mem_image.mpr ⟨y, hy, rfl⟩
    rcases hMcomp _ hMy with h | h
    · rw [← hPtMv] at h
      exact Or.inr ((bu_tkMv_le_iff hbt (hbot y hy) (htop y hy) hPt1 hPt2).mpr h)
    · rw [← hPtMv] at h
      exact Or.inl ((bu_tkMv_le_iff hbt hPt1 hPt2 (hbot y hy) (htop y hy)).mpr h)
  have hPtchain : bu_tkChain (insert (bu_tkPt b t M) σ) := by
    refine ⟨⟨b, Finset.mem_insert_of_mem hbσ⟩, ?_⟩
    intro x hx y hy
    rw [Finset.mem_insert] at hx hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · exact Or.inl (bu_tkLe_refl _)
    · exact hcompPt y hy
    · have hsym := hcompPt x hx
      rcases hsym with h | h
      · exact Or.inr h
      · exact Or.inl h
    · exact hchainσ.2 x hx y hy
  have hS : bu_tkS (insert (bu_tkPt b t M) σ) = bu_tkS σ := by
    have hall : ∀ z ∈ insert (bu_tkPt b t M) σ, bu_tkLe z t := by
      intro z hz
      rw [Finset.mem_insert] at hz
      rcases hz with hzv | hz
      · rw [hzv]
        exact hPt2
      · exact htop z hz
    have h := bu_tkS_of_top hPtchain (Finset.mem_insert_of_mem htσ) hall
    rw [h, hSeq]
  exact ⟨hPtbox, hPtnot, hPtchain, hS⟩

/-- Below cofacets sit over the boundary difference. -/
theorem bu_below_mem {n : ℕ} {σ : Finset (Fin n → ℤ)} {b t v : Fin n → ℤ}
    (hbt : bu_tkLe b t) (htσ : t ∈ σ)
    (hchain : bu_tkChain (insert v σ)) (hvb : bu_tkLe v b) (hne : v ≠ b) :
    (bu_tkMv v b).Nonempty ∧
      bu_tkMv v b ⊆ (Finset.univ.filter fun i => t i ≠ 0) \ bu_tkMv b t := by
  have hvt : bu_tkLe v t := by
    have hcomp : bu_tkLe v t ∨ bu_tkLe t v :=
      hchain.2 v (Finset.mem_insert_self v σ) t (Finset.mem_insert_of_mem htσ)
    exact bu_tkLe_trans_of_comparable hvb hbt hcomp
  have hnorm := bu_tkMv_normal_a hvt hvb hbt
  have hne_mem : (bu_tkMv v b).Nonempty := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, Ne.symm hi⟩⟩
  refine ⟨hne_mem, ?_⟩
  intro i hi
  have hbi : b i ≠ v i := by
    have hm := hi
    rw [bu_tkMv, Finset.mem_filter] at hm
    exact hm.2
  have hbit : b i = t i := by
    have e : (bu_tkPt v t (bu_tkMv v b)) i = t i := by simp [bu_tkPt, hi]
    rw [hnorm.2]
    exact e
  have ht0 : t i ≠ 0 := by
    have h1 := hvb i
    rcases h1 with c1 | ⟨s1, e1⟩ | ⟨s1, e1⟩
    · exact absurd c1 hbi
    · omega
    · omega
  refine Finset.mem_sdiff.mpr
    ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ i, ht0⟩, ?_⟩
  intro hcon
  rw [bu_tkMv, Finset.mem_filter] at hcon
  exact hcon.2 hbit.symm

/-- Above cofacets grow the sign set through fresh coordinates. -/
theorem bu_above_E {n : ℕ} {σ : Finset (Fin n → ℤ)} {b t v : Fin n → ℤ}
    (hbt : bu_tkLe b t) (htop : ∀ z ∈ σ, bu_tkLe z t)
    (hbσ : b ∈ σ) (hchain : bu_tkChain (insert v σ))
    (htv : bu_tkLe t v) (hne : v ≠ t) :
    (bu_tkMv t v).Nonempty ∧ (∀ i ∈ bu_tkMv t v, i ∉ bu_tkMv b t) ∧
      (∀ i ∉ bu_tkMv t v, v i = t i) ∧ bu_tkS (insert v σ) = bu_tkSgn v := by
  have hbv : bu_tkLe b v := by
    have hcomp : bu_tkLe b v ∨ bu_tkLe v b :=
      hchain.2 b (Finset.mem_insert_of_mem hbσ) v (Finset.mem_insert_self v σ)
    exact bu_tkLe_trans_of_comparable hbt htv hcomp
  have hnorm := bu_tkMv_normal_a hbv hbt htv
  have hXE : ∀ i ∈ bu_tkMv b t, i ∉ bu_tkMv t v := by
    intro i hiX
    have htiv : t i = v i := by
      have e : (bu_tkPt b v (bu_tkMv b t)) i = v i := by simp [bu_tkPt, hiX]
      rw [← hnorm.2] at e
      exact e
    intro hcon
    have hm := hcon
    rw [bu_tkMv, Finset.mem_filter] at hm
    exact hm.2 htiv.symm
  have hEX : ∀ i ∈ bu_tkMv t v, i ∉ bu_tkMv b t := fun i hiE hiX => hXE i hiX hiE
  have hneE : (bu_tkMv t v).Nonempty := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  have hoff : ∀ i ∉ bu_tkMv t v, v i = t i := fun i hi => bu_tkMv_eq_off i hi
  have hS : bu_tkS (insert v σ) = bu_tkSgn v := by
    have hall : ∀ z ∈ insert v σ, bu_tkLe z v := by
      intro z hz
      rw [Finset.mem_insert] at hz
      rcases hz with hzv | hz
      · rw [hzv]
        exact bu_tkLe_refl v
      · have hzt := htop z hz
        have hcomp := hchain.2 z (Finset.mem_insert_of_mem hz) v
          (Finset.mem_insert_self v σ)
        exact bu_tkLe_trans_of_comparable hzt htv hcomp
    exact bu_tkS_of_top hchain (Finset.mem_insert_self v σ) hall
  exact ⟨hneE, hEX, hoff, hS⟩

/-- The push is fresh (outside every chain it tops). -/
theorem bu_push_notmem {n : ℕ} {σ : Finset (Fin n → ℤ)} {t : Fin n → ℤ}
    {c : Fin n} {s : ℤ} (htop : ∀ z ∈ σ, bu_tkLe z t)
    (hH : bu_tkH t < bu_tkH (bu_tkPush t c s)) :
    bu_tkPush t c s ∉ σ := by
  intro hcon
  have hle := bu_tkLe_height (htop _ hcon)
  omega

/-- The push keeps the chain sign set. -/
theorem bu_push_S {n : ℕ} {σ : Finset (Fin n → ℤ)} {t : Fin n → ℤ}
    {c : Fin n} {s : ℤ}
    (hSeq : bu_tkS σ = bu_tkSgn t)
    (hchain : bu_tkChain (insert (bu_tkPush t c s) σ))
    (hle : ∀ z ∈ σ, bu_tkLe z (bu_tkPush t c s))
    (htc : t c ≠ 0) (hs : s = 1 ∨ s = -1)
    (hsign : (s = 1 → 0 ≤ t c) ∧ (s = -1 → t c ≤ 0)) :
    bu_tkS (insert (bu_tkPush t c s) σ) = bu_tkS σ := by
  have hall : ∀ z ∈ insert (bu_tkPush t c s) σ, bu_tkLe z (bu_tkPush t c s) := by
    intro z hz
    rw [Finset.mem_insert] at hz
    rcases hz with hzv | hz
    · rw [hzv]
      exact bu_tkLe_refl _
    · exact hle z hz
  have h := bu_tkS_of_top hchain (Finset.mem_insert_self _ _) hall
  have hsgn := bu_push_sgn hs hsign htc
  rw [h, hsgn, hSeq]

/-! ## Tight cofacet count -/

theorem bu_tight_cofacet_count {n m : ℕ} (hm : 1 ≤ m)
    {σ : Finset (Fin n → ℤ)} (hsub : σ ⊆ bu_tkBox n m) (hchainσ : bu_tkChain σ)
    (hc : σ.card = (bu_tkS σ).card) :
    (bu_tkBdry m σ → (bu_tkUp m σ).card = 1) ∧
    (¬ bu_tkBdry m σ → (bu_tkUp m σ).card = 2) := by
  obtain ⟨b, hbσ, t, htσ, hbot, htop, hSeq, _hC, hsubX, _h1, _h2, _hLoose,
    hTight⟩ := bu_chain_card_bound hchainσ
  have hbt : bu_tkLe b t := htop b hbσ
  have hzn : ∀ z ∈ σ, bu_tkMv b z ⊆ bu_tkMv b t ∧ z = bu_tkPt b t (bu_tkMv b z) :=
    fun z hz => bu_tkMv_normal_a hbt (hbot z hz) (htop z hz)
  have hMvbb : bu_tkMv b b = ∅ := by
    rw [bu_tkMv]
    exact Finset.filter_false_of_mem (fun x _ h => h rfl)
  have hempty : (∅ : Finset (Fin n)) ∈ σ.image (bu_tkMv b) := by
    have hmem : bu_tkMv b b ∈ σ.image (bu_tkMv b) :=
      Finset.mem_image.mpr ⟨b, hbσ, rfl⟩
    rw [hMvbb] at hmem
    exact hmem
  have hXmem : bu_tkMv b t ∈ σ.image (bu_tkMv b) :=
    Finset.mem_image.mpr ⟨t, htσ, rfl⟩
  have hcompC : ∀ A ∈ σ.image (bu_tkMv b), ∀ B ∈ σ.image (bu_tkMv b),
      A ⊆ B ∨ B ⊆ A := by
    intro A hA B hB
    rw [Finset.mem_image] at hA hB
    obtain ⟨z, hz, rfl⟩ := hA
    obtain ⟨w, hw, rfl⟩ := hB
    rcases hchainσ.2 z hz w hw with h | h
    · exact Or.inl ((bu_tkMv_le_iff hbt (hbot z hz) (htop z hz)
        (hbot w hw) (htop w hw)).mp h)
    · exact Or.inr ((bu_tkMv_le_iff hbt (hbot w hw) (htop w hw)
        (hbot z hz) (htop z hz)).mp h)
  have hgap := bu_gap_lemma hsubX hempty hXmem hcompC
  have hPtinj : Set.InjOn (bu_tkPt b t)
      (↑(bu_tkExt (σ.image (bu_tkMv b)) (bu_tkMv b t)) : Set (Finset (Fin n))) := by
    intro M1 h1m M2 h2m he
    have m1 : M1 ∈ bu_tkExt (σ.image (bu_tkMv b)) (bu_tkMv b t) :=
      Finset.mem_coe.mp h1m
    have m2 : M2 ∈ bu_tkExt (σ.image (bu_tkMv b)) (bu_tkMv b t) :=
      Finset.mem_coe.mp h2m
    rw [bu_mem_tkExt] at m1 m2
    have s1 : M1 ⊆ bu_tkMv b t := Finset.mem_powerset.mp m1.1
    have s2 : M2 ⊆ bu_tkMv b t := Finset.mem_powerset.mp m2.1
    have e1 : bu_tkMv b (bu_tkPt b t M1) = M1 := (bu_tkPt_mem_of_mem hbt s1).2.2
    have e2 : bu_tkMv b (bu_tkPt b t M2) = M2 := (bu_tkPt_mem_of_mem hbt s2).2.2
    rw [← e1, ← e2, he]
  rcases hTight hc with hA | hB
  · obtain ⟨hXT, hCX⟩ := hA
    have hExt2 : (bu_tkExt (σ.image (bu_tkMv b)) (bu_tkMv b t)).card = 2 :=
      hgap.2.2 hCX
    have hUp : bu_tkUp m σ =
        (bu_tkExt (σ.image (bu_tkMv b)) (bu_tkMv b t)).image (bu_tkPt b t) := by
      ext v
      rw [bu_mem_tkUp, Finset.mem_image]
      constructor
      · rintro ⟨hvbox, hvnot, hvchain, hvsub⟩
        have htri := bu_cofacet_pos hbσ htσ hvchain hvnot
        rcases htri with ⟨hbv, hvt⟩ | ⟨hvb, hne⟩ | ⟨htv, hne⟩
        · have hmem := bu_inside_mem_ext hbt hbot htop hvchain hbv hvt hvnot
          have ev : v = bu_tkPt b t (bu_tkMv b v) :=
            (bu_tkMv_normal_a hbt hbv hvt).2
          exact ⟨bu_tkMv b v, hmem, ev.symm⟩
        · have hD := bu_below_mem hbt htσ hvchain hvb hne
          have hDe : bu_tkMv v b = ∅ := by
            rw [Finset.eq_empty_iff_forall_notMem]
            intro i hi
            have h2 := hD.2 hi
            rw [Finset.mem_sdiff] at h2
            obtain ⟨hiT, hiX⟩ := h2
            rw [hXT] at hiX
            exact hiX hiT
          rw [hDe] at hD
          exact (Finset.not_nonempty_empty hD.1).elim
        · have hE := bu_above_E hbt htop hbσ hvchain htv hne
          obtain ⟨i, hiE⟩ := hE.1
          have hiX : i ∉ bu_tkMv b t := hE.2.1 i hiE
          rw [hXT] at hiX
          have hti0 : t i = 0 := by
            by_contra hcon
            exact hiX (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hcon⟩)
          have hvi0 : v i ≠ 0 := by
            have hm := hiE
            rw [bu_tkMv, Finset.mem_filter] at hm
            rw [← hti0]
            exact hm.2
          have hnew : (decide (0 < v i), i) ∈ bu_tkSgn v :=
            bu_mem_tkSgn.mpr ⟨hvi0, rfl⟩
          have hnot : (decide (0 < v i), i) ∉ bu_tkSgn t := by
            intro hcon
            rw [bu_mem_tkSgn] at hcon
            exact hcon.1 hti0
          have hsub2 : bu_tkSgn v ⊆ bu_tkSgn t := by
            rw [← hE.2.2.2, ← hSeq]
            exact hvsub
          exact (hnot (hsub2 hnew)).elim
      · rintro ⟨M, hM, rfl⟩
        have h := bu_ext_inside hchainσ hbot htop hbt hSeq hsub hbσ htσ hM
        exact ⟨h.1, h.2.1, h.2.2.1, le_of_eq h.2.2.2⟩
    have hcard2 : (bu_tkUp m σ).card = 2 := by
      rw [hUp, Finset.card_image_of_injOn hPtinj, hExt2]
    have hnbd : ¬ bu_tkBdry m σ := by
      intro hbd
      obtain ⟨i, hi⟩ := hbd b hbσ
      have hiN : (b i).natAbs = m := by
        rw [Int.abs_eq_natAbs] at hi
        exact_mod_cast hi
      by_cases hiX : i ∈ bu_tkMv b t
      · have hne : t i ≠ b i := by
          have h := hiX
          rw [bu_tkMv, Finset.mem_filter] at h
          exact h.2
        have hlt : (b i).natAbs < (t i).natAbs := bu_tkMv_natAbs_lt hbt i hne
        have hle : (t i).natAbs ≤ m := (bu_mem_tkBox_natAbs.mp (hsub htσ)) i
        omega
      · rw [hXT] at hiX
        have hbi0 : b i = 0 := by
          by_contra hcon
          exact hiX (Finset.mem_filter.mpr ⟨Finset.mem_univ i,
            bu_tkMv_support_mono hbt i hcon⟩)
        have h0 : ((0 : ℤ)).natAbs = 0 := rfl
        rw [hbi0, h0] at hiN
        omega
    exact ⟨fun hbd => absurd hbd hnbd, fun _ => hcard2⟩
  · obtain ⟨c, hT, hcX, hCX⟩ := hB
    have hTX : Finset.univ.filter (fun i => t i ≠ 0) \ bu_tkMv b t = {c} := by
      ext i
      rw [hT, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨h1 | h1, h2⟩
        · exact h1
        · exact absurd h1 h2
      · intro h
        rw [h]
        exact ⟨Or.inl rfl, hcX⟩
    have hcT : t c ≠ 0 := by
      have hmem : c ∈ Finset.univ.filter (fun i => t i ≠ 0) := by
        rw [hT]
        exact Finset.mem_insert_self c _
      exact (Finset.mem_filter.mp hmem).2
    have hcb : t c = b c := bu_tkMv_eq_off c hcX
    have hbc_ne : b c ≠ 0 := by
      rw [← hcb]
      exact hcT
    have hPull_le : bu_tkLe (bu_tkPull b c) b := (bu_tkPull_le hbc_ne).1
    have hPull_box : bu_tkPull b c ∈ bu_tkBox n m :=
      bu_tkPull_mem_box (hsub hbσ) hbc_ne
    have hPull_H := bu_pull_height hbc_ne
    have hPullnot : bu_tkPull b c ∉ σ := by
      intro hcon
      have hle := bu_tkLe_height (hbot _ hcon)
      omega
    have hPullchain : bu_tkChain (insert (bu_tkPull b c) σ) := by
      refine ⟨⟨b, Finset.mem_insert_of_mem hbσ⟩, ?_⟩
      intro x hx y hy
      rw [Finset.mem_insert] at hx hy
      rcases hx with rfl | hx' <;> rcases hy with rfl | hy'
      · exact Or.inl (bu_tkLe_refl _)
      · exact Or.inl (bu_pull_le_chain hbt hzn hcX hbc_ne y hy')
      · have h := bu_pull_le_chain hbt hzn hcX hbc_ne x hx'
        exact Or.inr h
      · exact hchainσ.2 x hx' y hy'
    have hPullS : bu_tkS (insert (bu_tkPull b c) σ) = bu_tkS σ := by
      have hpt : bu_tkLe (bu_tkPull b c) t := by
        have hcomp := hPullchain.2 _ (Finset.mem_insert_self _ _) _
          (Finset.mem_insert_of_mem htσ)
        exact bu_tkLe_trans_of_comparable hPull_le hbt hcomp
      have hall : ∀ z ∈ insert (bu_tkPull b c) σ, bu_tkLe z t := by
        intro z hz
        rw [Finset.mem_insert] at hz
        rcases hz with hzv | hz
        · rw [hzv]
          exact hpt
        · exact htop z hz
      have h := bu_tkS_of_top hPullchain (Finset.mem_insert_of_mem htσ) hall
      rw [h, hSeq]
    have hPullUp : bu_tkPull b c ∈ bu_tkUp m σ := by
      rw [bu_mem_tkUp]
      exact ⟨hPull_box, hPullnot, hPullchain, le_of_eq hPullS⟩
    set s0 := (if 0 < t c then (1 : ℤ) else -1) with hs0def
    have hs0 : s0 = 1 ∨ s0 = -1 := by
      rw [hs0def]
      by_cases hpos : 0 < t c
      · left
        simp [hpos]
      · right
        simp [hpos]
    have hsign : (s0 = 1 → 0 ≤ t c) ∧ (s0 = -1 → t c ≤ 0) := by
      constructor
      · intro h
        by_contra hcon
        have hval : s0 = -1 := by
          rw [hs0def]
          simp [show ¬ (0 : ℤ) < t c by omega]
        omega
      · intro h
        by_contra hcon
        have hval : s0 = 1 := by
          rw [hs0def]
          simp [show (0 : ℤ) < t c by omega]
        omega
    have hPush_le : ∀ z ∈ σ, bu_tkLe z (bu_tkPush t c s0) :=
      fun z hz => bu_push_le_chain hs0 hsign htop hzn hcX hcb z hz
    have hPushchain : bu_tkChain (insert (bu_tkPush t c s0) σ) := by
      refine ⟨⟨t, Finset.mem_insert_of_mem htσ⟩, ?_⟩
      intro x hx y hy
      rw [Finset.mem_insert] at hx hy
      rcases hx with rfl | hx' <;> rcases hy with rfl | hy'
      · exact Or.inl (bu_tkLe_refl _)
      · exact Or.inr (hPush_le y hy')
      · have h := hPush_le x hx'
        exact Or.inl h
      · exact hchainσ.2 x hx' y hy'
    have hPushH := bu_push_height hs0 hsign
    have hPushnot := bu_push_notmem htop hPushH
    have hPushS := bu_push_S hSeq hPushchain hPush_le hcT hs0 hsign
    have hPushbox : bu_tkPush t c s0 ∈ bu_tkBox n m ↔ (b c).natAbs < m := by
      have hbox_t : ∀ i, i ≠ c → (bu_tkPush t c s0 i).natAbs ≤ m := by
        intro i hic
        have e : (bu_tkPush t c s0) i = t i := by simp [bu_tkPush, hic]
        rw [e]
        exact (bu_mem_tkBox_natAbs.mp (hsub htσ)) i
      have hcc : (bu_tkPush t c s0 c).natAbs = (b c).natAbs + 1 := by
        rw [bu_push_abs hs0 hsign, hcb]
      constructor
      · intro h
        have h1 := (bu_mem_tkBox_natAbs.mp h) c
        rw [hcc] at h1
        omega
      · intro h
        rw [bu_mem_tkBox_natAbs]
        intro i
        by_cases hic : i = c
        · rw [hic, hcc]
          omega
        · exact hbox_t i hic
    have hbdy : bu_tkBdry m σ ↔ (b c).natAbs = m := by
      constructor
      · intro hbd
        obtain ⟨i, hi⟩ := hbd b hbσ
        have hiN : (b i).natAbs = m := by
          rw [Int.abs_eq_natAbs] at hi
          exact_mod_cast hi
        by_cases hic : i = c
        · rw [hic] at hiN
          exact hiN
        · exfalso
          by_cases hiX : i ∈ bu_tkMv b t
          · have hne : t i ≠ b i := by
              have h := hiX
              rw [bu_tkMv, Finset.mem_filter] at h
              exact h.2
            have hlt := bu_tkMv_natAbs_lt hbt i hne
            have hle := (bu_mem_tkBox_natAbs.mp (hsub htσ)) i
            omega
          · have hiT : i ∉ Finset.univ.filter (fun i => t i ≠ 0) := by
              intro hcon
              rw [hT] at hcon
              rw [Finset.mem_insert] at hcon
              rcases hcon with h | h
              · exact hic h
              · exact hiX h
            have hbi0 : b i = 0 := by
              by_contra hcon
              exact hiT (Finset.mem_filter.mpr ⟨Finset.mem_univ i,
                bu_tkMv_support_mono hbt i hcon⟩)
            have h0 : ((0 : ℤ)).natAbs = 0 := rfl
            rw [hbi0, h0] at hiN
            omega
      · intro hceq z hz
        have hzc : z c = b c := by
          have hsubz : bu_tkMv b z ⊆ bu_tkMv b t :=
            hsubX _ (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
          have hcMz : c ∉ bu_tkMv b z := fun hcon => hcX (hsubz hcon)
          have hznz := (hzn z hz).2
          have e2 : (bu_tkPt b t (bu_tkMv b z)) c = b c := by
            simp [bu_tkPt, hcMz]
          rw [hznz]
          exact e2
        have hmabs : |z c| = (m : ℤ) := by
          rw [hzc, Int.abs_eq_natAbs, hceq]
        exact ⟨c, hmabs⟩
    have hclass : ∀ v ∈ bu_tkUp m σ,
        v = bu_tkPull b c ∨ v = bu_tkPush t c s0 := by
      intro v hv
      rw [bu_mem_tkUp] at hv
      obtain ⟨hvbox, hvnot, hvchain, hvsub⟩ := hv
      have htri := bu_cofacet_pos hbσ htσ hvchain hvnot
      rcases htri with ⟨hbv, hvt⟩ | ⟨hvb, hne⟩ | ⟨htv, hne⟩
      · have hmem := bu_inside_mem_ext hbt hbot htop hvchain hbv hvt hvnot
        rw [hgap.2.1 hCX] at hmem
        exact absurd hmem (Finset.notMem_empty _)
      · have hD := bu_below_mem hbt htσ hvchain hvb hne
        have hDsub : bu_tkMv v b ⊆ {c} := by
          intro x hx
          have h := hD.2 hx
          rw [hTX] at h
          exact h
        have hD1 := bu_eq_singleton_of_sub hDsub hD.1
        exact Or.inl (bu_below_eq_pull hvb hD1)
      · have hE := bu_above_E hbt htop hbσ hvchain htv hne
        have hET : ∀ i ∈ bu_tkMv t v,
            i ∈ Finset.univ.filter (fun i => t i ≠ 0) := by
          intro i hiE
          by_contra hcon
          have hti0 : t i = 0 := by
            by_contra hcon2
            exact hcon (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hcon2⟩)
          have hvi0 : v i ≠ 0 := by
            have hm := hiE
            rw [bu_tkMv, Finset.mem_filter] at hm
            rw [← hti0]
            exact hm.2
          have hnew : (decide (0 < v i), i) ∈ bu_tkSgn v :=
            bu_mem_tkSgn.mpr ⟨hvi0, rfl⟩
          have hnot : (decide (0 < v i), i) ∉ bu_tkSgn t := by
            intro hcon3
            rw [bu_mem_tkSgn] at hcon3
            exact hcon3.1 hti0
          have hsub2 : bu_tkSgn v ⊆ bu_tkSgn t := by
            rw [← hE.2.2.2, ← hSeq]
            exact hvsub
          exact hnot (hsub2 hnew)
        have hEsub : bu_tkMv t v ⊆ {c} := by
          intro i hiE
          have hiT := hET i hiE
          rw [hT] at hiT
          rw [Finset.mem_insert] at hiT
          rcases hiT with h | h
          · exact Finset.mem_singleton.mpr h
          · exact absurd h (hE.2.1 i hiE)
        have hE1 := bu_eq_singleton_of_sub hEsub hE.1
        have hveq := bu_above_eq_push hcT htv hE1
        rw [hs0def]
        exact Or.inr hveq
    constructor
    · intro hbd
      have hbm : (b c).natAbs = m := hbdy.mp hbd
      have hPushOut : bu_tkPush t c s0 ∉ bu_tkBox n m := by
        intro hcon
        have h1 := (bu_mem_tkBox_natAbs.mp hcon) c
        rw [bu_push_abs hs0 hsign, hcb] at h1
        omega
      have hUpEq : bu_tkUp m σ = {bu_tkPull b c} := by
        ext v
        rw [Finset.mem_singleton]
        constructor
        · intro hv
          rcases hclass v hv with h | h
          · exact h
          · exfalso
            have hvb : bu_tkPush t c s0 ∈ bu_tkBox n m := by
              rw [← h]
              exact (bu_mem_tkUp.mp hv).1
            exact hPushOut hvb
        · intro hv
          rw [hv]
          exact hPullUp
      rw [hUpEq, Finset.card_singleton]
    · intro hnbd
      have hPushIn : bu_tkPush t c s0 ∈ bu_tkBox n m := by
        rw [hPushbox]
        have hbm : (b c).natAbs ≠ m := fun h => hnbd (hbdy.mpr h)
        have hle : (b c).natAbs ≤ m := (bu_mem_tkBox_natAbs.mp (hsub hbσ)) c
        omega
      have hPushUp : bu_tkPush t c s0 ∈ bu_tkUp m σ := by
        rw [bu_mem_tkUp]
        exact ⟨hPushIn, hPushnot, hPushchain, le_of_eq hPushS⟩
      have hUpEq : bu_tkUp m σ = {bu_tkPull b c, bu_tkPush t c s0} := by
        ext v
        rw [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro hv
          rcases hclass v hv with h | h
          · exact Or.inl h
          · exact Or.inr h
        · rintro (h | h)
          · rw [h]
            exact hPullUp
          · rw [h]
            exact hPushUp
      have hne : bu_tkPull b c ≠ bu_tkPush t c s0 := by
        intro hcon
        have h1 := bu_pull_height hbc_ne
        have h2 := bu_push_height hs0 hsign
        have h3 := bu_tkLe_height hbt
        rw [hcon] at h1
        omega
      rw [hUpEq, Finset.card_pair_eq_two_iff.mpr hne]

/-! ## Loose-chain facts -/

theorem bu_loose_not_bdry {n m : ℕ} (hm : 1 ≤ m)
    {σ : Finset (Fin n → ℤ)} (hsub : σ ⊆ bu_tkBox n m) (hchainσ : bu_tkChain σ)
    (hc : σ.card = (bu_tkS σ).card + 1) : ¬ bu_tkBdry m σ := by
  obtain ⟨b, hbσ, t, htσ, _hbot, htop, _hSeq, _hC, _hsubX, _h1, _h2, hLoose,
    _hTight⟩ := bu_chain_card_bound hchainσ
  obtain ⟨hXT, _hCX⟩ := hLoose hc
  have hbt : bu_tkLe b t := htop b hbσ
  intro hbd
  obtain ⟨i, hi⟩ := hbd b hbσ
  have hiN : (b i).natAbs = m := by
    rw [Int.abs_eq_natAbs] at hi
    exact_mod_cast hi
  by_cases hiX : i ∈ bu_tkMv b t
  · have hne : t i ≠ b i := by
      have h := hiX
      rw [bu_tkMv, Finset.mem_filter] at h
      exact h.2
    have hlt : (b i).natAbs < (t i).natAbs := bu_tkMv_natAbs_lt hbt i hne
    have hle : (t i).natAbs ≤ m := (bu_mem_tkBox_natAbs.mp (hsub htσ)) i
    omega
  · rw [hXT] at hiX
    have hbi0 : b i = 0 := by
      by_contra hcon
      exact hiX (Finset.mem_filter.mpr ⟨Finset.mem_univ i,
        bu_tkMv_support_mono hbt i hcon⟩)
    have h0 : ((0 : ℤ)).natAbs = 0 := rfl
    rw [hbi0, h0] at hiN
    omega

theorem bu_loose_strict_growth {n m : ℕ}
    {σ : Finset (Fin n → ℤ)} (_hchainσ : bu_tkChain σ)
    (hc : σ.card = (bu_tkS σ).card + 1)
    {v : Fin n → ℤ} (_hvbox : v ∈ bu_tkBox n m) (hvnot : v ∉ σ)
    (hchain : bu_tkChain (insert v σ)) :
    bu_tkS σ ⊂ bu_tkS (insert v σ) := by
  have hsub : bu_tkS σ ⊆ bu_tkS (insert v σ) :=
    Finset.sup_mono (Finset.subset_insert v σ)
  obtain ⟨_b, _hb, _t, _ht, _hbot, _htop, _hSeq, _hC, _hsubX, h1, h2, _hLoose,
    _hTight⟩ := bu_chain_card_bound hchain
  have hcardI : (insert v σ).card = σ.card + 1 :=
    Finset.card_insert_of_notMem hvnot
  have hlt : (bu_tkS σ).card < (bu_tkS (insert v σ)).card := by omega
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨hsub, ?_⟩
  intro hcon
  rw [hcon] at hlt
  exact lt_irrefl _ hlt

/-! ## Happy-chain trichotomy -/

theorem bu_happy_card {n m : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
    {σ : Finset (Fin n → ℤ)} (h : bu_tkHappy m L σ) :
    σ.card = (bu_tkS σ).card ∨ σ.card = (bu_tkS σ).card + 1 := by
  obtain ⟨_hsub, hchain, hcover⟩ := h
  obtain ⟨_b, _hb, _t, _ht, _hbot, _htop, _hSeq, _hC, _hsubX, h1, h2, _hLoose,
    _hTight⟩ := bu_chain_card_bound hchain
  have hle : (bu_tkS σ).card ≤ σ.card :=
    calc (bu_tkS σ).card ≤ (σ.image L).card := Finset.card_le_card hcover
      _ ≤ σ.card := Finset.card_image_le
  omega

theorem bu_happy_empty_iff {n : ℕ}
    {σ : Finset (Fin n → ℤ)} (hchainσ : bu_tkChain σ) :
    bu_tkS σ = ∅ ↔ σ = {0} := by
  constructor
  · intro hS
    obtain ⟨_b, _hbσ, t, htσ, _hbot, htop, hSeq, _hC, _hsubX, _h1, _h2, _hLoose,
      _hTight⟩ := bu_chain_card_bound hchainσ
    have ht0 : t = 0 := by
      by_contra hcon
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hcon
      have hi0 : t i ≠ 0 := hi
      have hmem : (decide (0 < t i), i) ∈ bu_tkSgn t :=
        bu_mem_tkSgn.mpr ⟨hi0, rfl⟩
      rw [← hSeq] at hmem
      rw [hS] at hmem
      exact Finset.notMem_empty _ hmem
    have hz0 : ∀ z ∈ σ, z = 0 := by
      intro z hz
      funext i
      have hle := htop z hz i
      rw [ht0] at hle
      have h0 : (0 : Fin n → ℤ) i = 0 := rfl
      rw [h0] at hle
      rcases hle with h | ⟨s, e⟩ | ⟨s, e⟩ <;> omega
    ext z
    constructor
    · intro hz
      rw [hz0 z hz]
      exact Finset.mem_singleton_self 0
    · intro hz
      rw [Finset.mem_singleton] at hz
      rw [hz, ← ht0]
      exact htσ
  · intro hσ
    rw [hσ, bu_tkS, Finset.sup_singleton, bu_tkSgn_zero]

theorem bu_zero_happy {n m : ℕ} {L : (Fin n → ℤ) → Bool × Fin n} :
    bu_tkHappy m L ({0} : Finset (Fin n → ℤ)) ∧
      ({0} : Finset (Fin n → ℤ)).card = (bu_tkS ({0} : Finset (Fin n → ℤ))).card + 1 := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro z hz
    rw [Finset.mem_singleton] at hz
    rw [hz]
    exact bu_zero_mem_tkBox
  · refine ⟨Finset.singleton_nonempty 0, ?_⟩
    intro z hz w hw
    rw [Finset.mem_singleton] at hz hw
    rw [hz, hw]
    exact Or.inl (bu_tkLe_refl 0)
  · rw [bu_tkS, Finset.sup_singleton, bu_tkSgn_zero]
    exact Finset.empty_subset _
  · rw [bu_tkS, Finset.sup_singleton, bu_tkSgn_zero]
    rfl

end MathlibExt.Topology.Homotopy.BorsukUlamWanted
