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
import Def.Topology.Homotopy.BorsukUlam.Part9


namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

open Metric

/-- Loose chains covered by `S` have no up-neighbors (signs would grow). -/
theorem bu_up_loose_eq {n m : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
    {σ : Finset (Fin n → ℤ)} (hσ : bu_tkHappy m L σ)
    (hc : σ.card = (bu_tkS σ).card + 1) (himg : σ.image L = bu_tkS σ) :
    bu_upFin m L σ = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro x hx
  obtain ⟨v, hvF, rfl⟩ := Finset.mem_image.mp hx
  rw [Finset.mem_filter] at hvF
  obtain ⟨hvbox, hvnot, hchainv, hcover⟩ := hvF
  have hlt : (bu_tkS σ).card < (bu_tkS (insert v σ)).card :=
    Finset.card_lt_card
      (bu_loose_strict_growth hσ.2.1 hc hvbox hvnot hchainv)
  have hle : (bu_tkS (insert v σ)).card ≤ (bu_tkS σ).card := by
    rw [himg] at hcover
    exact Finset.card_le_card hcover
  omega

/-! ## Loose upward extensions gaining a new sign -/

theorem bu_loose_upL_card {n m : ℕ} (hm : 1 ≤ m)
    {σ : Finset (Fin n → ℤ)} (hsub : σ ⊆ bu_tkBox n m) (hchainσ : bu_tkChain σ)
    (hc : σ.card = (bu_tkS σ).card + 1)
    {ℓ : Bool × Fin n} (hℓ : ℓ ∉ bu_tkS σ) (hℓn : bu_tkNeg ℓ ∉ bu_tkS σ) :
    (bu_tkUpL m σ ℓ).card = 1 := by
  obtain ⟨β, j⟩ := ℓ
  obtain ⟨b, hbσ, t, htσ, hbot, htop, hSeq, _hC, hsubX, _h1, _h2, hLoose,
    _hTight⟩ := bu_chain_card_bound hchainσ
  obtain ⟨hXT, hCX⟩ := hLoose hc
  have hbt : bu_tkLe b t := htop b hbσ
  have hzn : ∀ z ∈ σ, bu_tkMv b z ⊆ bu_tkMv b t ∧ z = bu_tkPt b t (bu_tkMv b z) :=
    fun z hz => bu_tkMv_normal_a hbt (hbot z hz) (htop z hz)
  have htj : t j = 0 := by
    by_contra hcon
    have hmem : (decide (0 < t j), j) ∈ bu_tkSgn t :=
      bu_mem_tkSgn.mpr ⟨hcon, rfl⟩
    rw [← hSeq] at hmem
    by_cases hβ : decide (0 < t j) = β
    · have he : (decide (0 < t j), j) = (β, j) := Prod.ext_iff.mpr ⟨hβ, rfl⟩
      rw [he] at hmem
      exact hℓ hmem
    · have hnegb : decide (0 < t j) = !β := by
        cases β <;> cases hd : decide (0 < t j)
        · exact (hβ hd).elim
        · rfl
        · rfl
        · exact (hβ hd).elim
      have he : (decide (0 < t j), j) = bu_tkNeg (β, j) := by
        rw [bu_tkNeg]
        exact Prod.ext_iff.mpr ⟨hnegb, rfl⟩
      rw [he] at hmem
      exact hℓn hmem
  have hjT : j ∉ Finset.univ.filter (fun i => t i ≠ 0) := by
    intro h
    rw [Finset.mem_filter] at h
    exact h.2 htj
  have hjX : j ∉ bu_tkMv b t := by
    rw [hXT]
    exact hjT
  have hjt : t j = b j := bu_tkMv_eq_off j hjX
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
  have hExtEmpty : bu_tkExt (σ.image (bu_tkMv b)) (bu_tkMv b t) = ∅ :=
    hgap.2.1 hCX
  set s0 : ℤ := (if β then 1 else -1) with hs0def
  have hs0 : s0 = 1 ∨ s0 = -1 := by
    rw [hs0def]
    by_cases hβ : β <;> simp [hβ]
  have hsign : (s0 = 1 → 0 ≤ t j) ∧ (s0 = -1 → t j ≤ 0) := by
    constructor <;> intro _ <;> omega
  have hs0dec : decide (0 < s0) = β := by
    rw [hs0def]
    cases β <;> simp
  have hPush_le : ∀ z ∈ σ, bu_tkLe z (bu_tkPush t j s0) :=
    fun z hz => bu_push_le_chain hs0 hsign htop hzn hjX hjt z hz
  have hPushchain : bu_tkChain (insert (bu_tkPush t j s0) σ) := by
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
  have hPushbox : bu_tkPush t j s0 ∈ bu_tkBox n m := by
    rw [bu_mem_tkBox]
    intro i
    by_cases hic : i = j
    · rw [hic]
      have e : (bu_tkPush t j s0) j = s0 := by simp [bu_tkPush, htj]
      rw [e]
      have habs : |s0| = 1 := by
        rw [hs0def]
        cases β <;> simp
      rw [habs]
      exact_mod_cast hm
    · have e : (bu_tkPush t j s0) i = t i := by simp [bu_tkPush, hic]
      rw [e]
      exact (bu_mem_tkBox.mp (hsub htσ)) i
  have hPushSgn : bu_tkSgn (bu_tkPush t j s0) = insert (β, j) (bu_tkSgn t) := by
    ext ⟨b', i⟩
    simp only [bu_mem_tkSgn]
    by_cases hic : i = j
    · rw [hic]
      have e : (bu_tkPush t j s0) j = s0 := by simp [bu_tkPush, htj]
      rw [e]
      constructor
      · rintro ⟨_, hβ'⟩
        rw [hs0dec] at hβ'
        rw [Finset.mem_insert]
        left
        exact Prod.ext_iff.mpr ⟨hβ', rfl⟩
      · intro h
        rw [Finset.mem_insert] at h
        rcases h with h | h
        · have h1 : b' = β := congrArg Prod.fst h
          have h2 : j = j := congrArg Prod.snd h
          refine ⟨by rw [hs0def]; cases β <;> simp, ?_⟩
          rw [h1, hs0dec]
        · rw [bu_mem_tkSgn] at h
          exact absurd h.1 (by rw [htj]; simp)
    · have e : (bu_tkPush t j s0) i = t i := by simp [bu_tkPush, hic]
      rw [e]
      constructor
      · rintro ⟨hne, hβ'⟩
        rw [Finset.mem_insert]
        right
        exact bu_mem_tkSgn.mpr ⟨hne, hβ'⟩
      · intro h
        rw [Finset.mem_insert] at h
        rcases h with h | h
        · have h2 : i = j := congrArg Prod.snd h
          exact absurd h2 hic
        · exact bu_mem_tkSgn.mp h
  have hPushS : bu_tkS (insert (bu_tkPush t j s0) σ) = insert (β, j) (bu_tkS σ) := by
    have hall : ∀ z ∈ insert (bu_tkPush t j s0) σ, bu_tkLe z (bu_tkPush t j s0) := by
      intro z hz
      rw [Finset.mem_insert] at hz
      rcases hz with hzv | hz
      · rw [hzv]
        exact bu_tkLe_refl _
      · exact hPush_le z hz
    have h := bu_tkS_of_top hPushchain (Finset.mem_insert_self _ _) hall
    rw [h, hPushSgn, hSeq]
  have hv0mem : bu_tkPush t j s0 ∈ bu_tkUpL m σ (β, j) := by
    rw [bu_mem_tkUpL]
    exact ⟨hPushbox, hPushnot, hPushchain, hPushS⟩
  have hUpEq : bu_tkUpL m σ (β, j) = {bu_tkPush t j s0} := by
    ext v
    rw [Finset.mem_singleton]
    constructor
    · intro hv
      rw [bu_mem_tkUpL] at hv
      obtain ⟨hvbox, hvnot, hvchain, hvS⟩ := hv
      have htri := bu_cofacet_pos hbσ htσ hvchain hvnot
      rcases htri with ⟨hbv, hvt⟩ | ⟨hvb, hne⟩ | ⟨htv, hne⟩
      · have hmem := bu_inside_mem_ext hbt hbot htop hvchain hbv hvt hvnot
        rw [hExtEmpty] at hmem
        exact (Finset.notMem_empty _ hmem).elim
      · have hcomp : bu_tkLe v t ∨ bu_tkLe t v :=
          hvchain.2 v (Finset.mem_insert_self v σ) t
            (Finset.mem_insert_of_mem htσ)
        have hvt' : bu_tkLe v t := bu_tkLe_trans_of_comparable hvb hbt hcomp
        have hall : ∀ z ∈ insert v σ, bu_tkLe z t := by
          intro z hz
          rw [Finset.mem_insert] at hz
          rcases hz with hzv | hz
          · rw [hzv]
            exact hvt'
          · exact htop z hz
        have hSame : bu_tkS (insert v σ) = bu_tkS σ := by
          have h := bu_tkS_of_top hvchain (Finset.mem_insert_of_mem htσ) hall
          rw [h, hSeq]
        have hcon : (β, j) ∈ bu_tkS σ := by
          rw [← hSame, hvS]
          exact Finset.mem_insert_self (β, j) _
        exact absurd hcon hℓ
      · have hE := bu_above_E hbt htop hbσ hvchain htv hne
        obtain ⟨hneE, hEX, hoff, hSv⟩ := hE
        have hSgv : bu_tkSgn v = insert (β, j) (bu_tkSgn t) := by
          rw [← hSv, hvS, hSeq]
        have hEsub : bu_tkMv t v ⊆ {j} := by
          intro i hiE
          have hiX : i ∉ bu_tkMv b t := hEX i hiE
          rw [hXT] at hiX
          have hti0 : t i = 0 := by
            by_contra hcon
            exact hiX (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hcon⟩)
          have hvi : v i ≠ t i := by
            have hm := hiE
            rw [bu_tkMv, Finset.mem_filter] at hm
            exact hm.2
          have hvi0 : v i ≠ 0 := by
            rw [← hti0]
            exact hvi
          have hnew : (decide (0 < v i), i) ∈ bu_tkSgn v :=
            bu_mem_tkSgn.mpr ⟨hvi0, rfl⟩
          rw [hSgv] at hnew
          rw [Finset.mem_insert] at hnew
          rcases hnew with h | h
          · have hi : i = j := congrArg Prod.snd h
            exact Finset.mem_singleton.mpr hi
          · rw [bu_mem_tkSgn] at h
            exact absurd h.1 (by rw [hti0]; simp)
        have hE1 := bu_eq_singleton_of_sub hEsub hneE
        have hvj : v j = s0 := by
          have hjE : j ∈ bu_tkMv t v := by
            rw [hE1]
            exact Finset.mem_singleton_self j
          have hne_j : v j ≠ t j := by
            have hm := hjE
            rw [bu_tkMv, Finset.mem_filter] at hm
            exact hm.2
          have hdec : decide (0 < v j) = β := by
            have hmemj : (β, j) ∈ bu_tkSgn v := by
              rw [hSgv]
              exact Finset.mem_insert_self (β, j) _
            rw [bu_mem_tkSgn] at hmemj
            exact hmemj.2.symm
          have h1 := htv j
          rcases h1 with c1 | ⟨s1, e1⟩ | ⟨s1, e1⟩
          · exact absurd c1 hne_j
          · have hpos : 0 < v j := by omega
            have hβt : β = true := by
              rw [← hdec]
              exact decide_eq_true hpos
            have hs : s0 = 1 := by simp [hs0def, hβt]
            rw [hs]
            omega
          · have hβf : β = false := by
              rw [← hdec]
              exact decide_eq_false (by omega : ¬ 0 < v j)
            have hs : s0 = -1 := by simp [hs0def, hβf]
            rw [hs]
            omega
        funext i
        by_cases hic : i = j
        · rw [hic, hvj]
          have e : bu_tkPush t j s0 j = s0 := by simp [bu_tkPush, htj]
          exact e.symm
        · have hvi : v i = t i := hoff i (by
            rw [hE1]
            simp [hic])
          have hpi : bu_tkPush t j s0 i = t i := by simp [bu_tkPush, hic]
          rw [hvi, hpi]
    · intro hv
      rw [hv]
      exact hv0mem
  rw [hUpEq, Finset.card_singleton]

/-- For loose chains with a new label, up-neighbors gain exactly `ℓ`. -/
theorem bu_upFin_loose_new_card {n m : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
    {σ : Finset (Fin n → ℤ)} {ℓ : Bool × Fin n}
    (hchainσ : bu_tkChain σ) (hc : σ.card = (bu_tkS σ).card + 1)
    (himg : σ.image L = insert ℓ (bu_tkS σ)) (hℓ : ℓ ∉ bu_tkS σ) :
    (bu_upFin m L σ).card = (bu_tkUpL m σ ℓ).card := by
  have hfilter : ((bu_tkBox n m).filter fun v =>
      v ∉ σ ∧ bu_tkChain (insert v σ) ∧ bu_tkS (insert v σ) ⊆ σ.image L) =
      ((bu_tkBox n m).filter fun v =>
        v ∉ σ ∧ bu_tkChain (insert v σ) ∧
          bu_tkS (insert v σ) = insert ℓ (bu_tkS σ)) := by
    ext v
    rw [Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨hvbox, hvnot, hchain, hcover⟩
      refine ⟨hvbox, hvnot, hchain, ?_⟩
      rw [himg] at hcover
      have hstrict := bu_loose_strict_growth hchainσ hc hvbox hvnot hchain
      have hsub1 : bu_tkS σ ⊆ bu_tkS (insert v σ) :=
        Finset.sup_mono (Finset.subset_insert v σ)
      have hlt : (bu_tkS σ).card < (bu_tkS (insert v σ)).card :=
        Finset.card_lt_card hstrict
      have hle : (bu_tkS (insert v σ)).card ≤ (insert ℓ (bu_tkS σ)).card :=
        Finset.card_le_card hcover
      have hinter : (insert ℓ (bu_tkS σ)).card = (bu_tkS σ).card + 1 :=
        Finset.card_insert_of_notMem hℓ
      have heq : (bu_tkS (insert v σ)).card = (insert ℓ (bu_tkS σ)).card := by
        omega
      exact Finset.eq_of_subset_of_card_le hcover (le_of_eq heq.symm)
    · rintro ⟨hvbox, hvnot, hchain, heq⟩
      refine ⟨hvbox, hvnot, hchain, ?_⟩
      rw [heq, himg]
  have hinj : Set.InjOn (fun v => insert v σ)
      (↑((bu_tkBox n m).filter fun v =>
        v ∉ σ ∧ bu_tkChain (insert v σ) ∧
          bu_tkS (insert v σ) = insert ℓ (bu_tkS σ)) :
        Set (Fin n → ℤ)) := by
    intro v₁ hv₁ v₂ hv₂ he
    have h₁ : v₁ ∉ σ := (Finset.mem_filter.mp (Finset.mem_coe.mp hv₁)).2.1
    exact bu_insert_inj_of_notMem h₁ he
  rw [bu_upFin, hfilter, bu_tkUpL, Finset.card_image_of_injOn hinj]

/-- The vertex `{0}` has degree one. -/
theorem bu_degree_singleton {n m : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
    {hm : 1 ≤ m}
    (hanti : ∀ z ∈ bu_tkBox n m, (∃ i, |z i| = (m : ℤ)) → L (-z) = bu_tkNeg (L z))
    {σ : bu_tkV n m} (hval : σ.val = ({0} : Finset (Fin n → ℤ))) :
    (bu_tkG n m L hm).degree σ = 1 := by
  have hS : bu_tkS ({0} : Finset (Fin n → ℤ)) = ∅ := by
    rw [bu_tkS, Finset.sup_singleton, bu_tkSgn_zero]
  have hσ : bu_tkHappy m L σ.val := by
    rw [hval]
    exact bu_zero_happy.1
  have hdeg := bu_degree_eq (hm := hm) hanti hσ
  have hup : (bu_upFin m L σ.val).card = 1 := by
    have hc0 : ({0} : Finset (Fin n → ℤ)).card =
        (bu_tkS ({0} : Finset (Fin n → ℤ))).card + 1 :=
      (bu_zero_happy (n := n) (m := m) (L := L)).2
    have hchain0 : bu_tkChain ({0} : Finset (Fin n → ℤ)) :=
      (bu_zero_happy (n := n) (m := m) (L := L)).1.2.1
    have himg0 : (({0} : Finset (Fin n → ℤ)).image L) =
        insert (L 0) (bu_tkS ({0} : Finset (Fin n → ℤ))) := by
      rw [hS]
      ext y
      simp
    have hℓ0 : (L 0) ∉ bu_tkS ({0} : Finset (Fin n → ℤ)) := by
      rw [hS]
      exact Finset.notMem_empty _
    have hℓn0 : bu_tkNeg (L 0) ∉ bu_tkS ({0} : Finset (Fin n → ℤ)) := by
      rw [hS]
      exact Finset.notMem_empty _
    have hsub0 : ({0} : Finset (Fin n → ℤ)) ⊆ bu_tkBox n m := by
      intro z hz
      rw [Finset.mem_singleton] at hz
      rw [hz]
      exact bu_zero_mem_tkBox
    calc (bu_upFin m L σ.val).card = (bu_upFin m L {0}).card := by rw [hval]
      _ = (bu_tkUpL m {0} (L 0)).card := by
          exact bu_upFin_loose_new_card hchain0 hc0 himg0 hℓ0
      _ = 1 := bu_loose_upL_card hm hsub0 hchain0 hc0 hℓ0 hℓn0
  have hdown : (bu_downFin L σ.val).card = 0 := by
    rw [hval, bu_down_singleton, Finset.card_empty]
  have hanti0 : (bu_antiFin m σ.val).card = 0 := by
    rw [hval]
    exact bu_anti_card_neg (bu_singleton_not_bdry hm)
  rw [hdeg, hup, hdown, hanti0]

/-- Happy vertices other than `{0}` have degree two (tight case). -/
theorem bu_degree_tight {n m : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
    {hm : 1 ≤ m}
    (hanti : ∀ z ∈ bu_tkBox n m, (∃ i, |z i| = (m : ℤ)) → L (-z) = bu_tkNeg (L z))
    {σ : bu_tkV n m} (hσ : bu_tkHappy m L σ.val)
    (hc : σ.val.card = (bu_tkS σ.val).card) :
    (bu_tkG n m L hm).degree σ = 2 := by
  have himg := bu_happy_tight_image hσ hc
  have hup : (bu_upFin m L σ.val).card = (bu_tkUp m σ.val).card :=
    bu_upFin_tight_card himg
  have hdown : (bu_downFin L σ.val).card = 0 := by
    rw [bu_down_tight hσ.2.1 hc, Finset.card_empty]
  have hcount := bu_tight_cofacet_count hm hσ.1 hσ.2.1 hc
  rw [bu_degree_eq (hm := hm) hanti hσ, hup, hdown]
  by_cases hb : bu_tkBdry m σ.val
  · rw [bu_anti_card_pos hb, hcount.1 hb]
  · rw [bu_anti_card_neg hb, hcount.2 hb]

/-- Happy loose vertices covered by `S` have degree two. -/
theorem bu_degree_loose_eq {n m : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
    {hm : 1 ≤ m}
    (hanti : ∀ z ∈ bu_tkBox n m, (∃ i, |z i| = (m : ℤ)) → L (-z) = bu_tkNeg (L z))
    {σ : bu_tkV n m} (hσ : bu_tkHappy m L σ.val)
    (hc : σ.val.card = (bu_tkS σ.val).card + 1)
    (himg : σ.val.image L = bu_tkS σ.val) (hne : σ.val ≠ ({0} : Finset (Fin n → ℤ))) :
    (bu_tkG n m L hm).degree σ = 2 := by
  have hup0 : (bu_upFin m L σ.val).card = 0 := by
    rw [bu_up_loose_eq hσ hc himg, Finset.card_empty]
  have hSne : bu_tkS σ.val ≠ ∅ := by
    intro hcon
    exact hne ((bu_happy_empty_iff hσ.2.1).mp hcon)
  have hSpos : 1 ≤ (bu_tkS σ.val).card := Finset.card_pos.mpr
    (Finset.nonempty_iff_ne_empty.mpr hSne)
  have h2 : 2 ≤ σ.val.card := by omega
  have hdown2 : (bu_downFin L σ.val).card = 2 := by
    rw [bu_downFin_card_of_two_le h2, bu_label_removal_two hc himg]
  have hnb : ¬ bu_tkBdry m σ.val := bu_loose_not_bdry hm hσ.1 hσ.2.1 hc
  rw [bu_degree_eq (hm := hm) hanti hσ, hup0, hdown2, bu_anti_card_neg hnb]

/-- Happy loose vertices with a new label have degree two (unless `{0}`). -/
theorem bu_degree_loose_new {n m : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
    {hm : 1 ≤ m}
    (hanti : ∀ z ∈ bu_tkBox n m, (∃ i, |z i| = (m : ℤ)) → L (-z) = bu_tkNeg (L z))
    (hN : bu_tkNoCompl m L)
    {σ : bu_tkV n m} (hσ : bu_tkHappy m L σ.val)
    (hc : σ.val.card = (bu_tkS σ.val).card + 1)
    {ℓ : Bool × Fin n} (hℓnot : ℓ ∉ bu_tkS σ.val)
    (himg : σ.val.image L = insert ℓ (bu_tkS σ.val))
    (hne : σ.val ≠ ({0} : Finset (Fin n → ℤ))) :
    (bu_tkG n m L hm).degree σ = 2 := by
  obtain ⟨hℓn, _⟩ := bu_happy_loose_neg hσ hN hℓnot himg
  have hup1 : (bu_upFin m L σ.val).card = 1 := by
    rw [bu_upFin_loose_new_card hσ.2.1 hc himg hℓnot,
      bu_loose_upL_card hm hσ.1 hσ.2.1 hc hℓnot hℓn]
  have h1pos : 1 ≤ σ.val.card := Finset.card_pos.mpr hσ.2.1.1
  have h2 : 2 ≤ σ.val.card := by
    by_contra hcon
    have h1 : σ.val.card = 1 := by omega
    have hScard : (bu_tkS σ.val).card = 0 := by omega
    have hS : bu_tkS σ.val = ∅ := Finset.card_eq_zero.mp hScard
    exact hne ((bu_happy_empty_iff hσ.2.1).mp hS)
  have hdown1 : (bu_downFin L σ.val).card = 1 := by
    rw [bu_downFin_card_of_two_le h2, (bu_label_removal_one hc hℓnot himg).2]
  have hnb : ¬ bu_tkBdry m σ.val := bu_loose_not_bdry hm hσ.1 hσ.2.1 hc
  rw [bu_degree_eq (hm := hm) hanti hσ, hup1, hdown1, bu_anti_card_neg hnb]

/-- Full degree classification: happy non-singletons have degree two. -/
theorem bu_degree_happy_two {n m : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
    {hm : 1 ≤ m}
    (hanti : ∀ z ∈ bu_tkBox n m, (∃ i, |z i| = (m : ℤ)) → L (-z) = bu_tkNeg (L z))
    (hN : bu_tkNoCompl m L)
    {σ : bu_tkV n m} (hσ : bu_tkHappy m L σ.val)
    (hne : σ.val ≠ ({0} : Finset (Fin n → ℤ))) :
    (bu_tkG n m L hm).degree σ = 2 := by
  rcases bu_happy_card hσ with hc | hc
  · exact bu_degree_tight hanti hσ hc
  · rcases bu_label_image_cases hσ.2.2 hc with himg | ⟨ℓ, hℓnot, himg⟩
    · exact bu_degree_loose_eq hanti hσ hc himg hne
    · exact bu_degree_loose_new hanti hN hσ hc hℓnot himg hne

/-- Odd degrees mark exactly the `{0}` vertex. -/
theorem bu_degree_odd_iff {n m : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
    {hm : 1 ≤ m}
    (hanti : ∀ z ∈ bu_tkBox n m, (∃ i, |z i| = (m : ℤ)) → L (-z) = bu_tkNeg (L z))
    (hN : bu_tkNoCompl m L) {σ : bu_tkV n m} :
    Odd ((bu_tkG n m L hm).degree σ) ↔ σ.val = ({0} : Finset (Fin n → ℤ)) := by
  constructor
  · intro hodd
    by_contra hne
    by_cases hσ : bu_tkHappy m L σ.val
    · have h2 := bu_degree_happy_two (hm := hm) hanti hN hσ hne
      rw [h2] at hodd
      exact (by simp : ¬ Odd 2) hodd
    · have h0 := bu_degree_not_happy (hm := hm) hσ
      rw [h0] at hodd
      exact (by simp : ¬ Odd 0) hodd
  · intro hval
    rw [bu_degree_singleton hanti hval]
    exact odd_one

end MathlibExt.Topology.Homotopy.BorsukUlamWanted
