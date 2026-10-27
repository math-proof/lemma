import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Topology.Homotopy.BorsukUlam.Part11
open Metric
open MathlibExt.Topology.Homotopy.BorsukUlamWanted


namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_mem_tkBox](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_mem_tkBox {n m : ℕ} {z : Fin n → ℤ} :
  z ∈ bu_tkBox n m ↔ ∀ i, |z i| ≤ (m : ℤ) := by
  rw [bu_tkBox, Fintype.mem_piFinset]
  constructor
  · intro h i
    have hi := h i
    rw [Finset.mem_Icc] at hi
    rwa [abs_le]
  · intro h i
    rw [Finset.mem_Icc, ← abs_le]
    exact h i

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_zero_mem_tkBox](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_zero_mem_tkBox {n m : ℕ} : (0 : Fin n → ℤ) ∈ bu_tkBox n m := by
  rw [bu_mem_tkBox]
  intro i
  simp

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_neg_mem_tkBox](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_neg_mem_tkBox {n m : ℕ} {z : Fin n → ℤ} (hz : z ∈ bu_tkBox n m) :
  -z ∈ bu_tkBox n m := by
  rw [bu_mem_tkBox] at hz ⊢
  intro i
  rw [Pi.neg_apply, abs_neg]
  exact hz i

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_mem_tkSgn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_mem_tkSgn {n : ℕ} {z : Fin n → ℤ} {l : Bool × Fin n} :
  l ∈ bu_tkSgn z ↔ z l.2 ≠ 0 ∧ l.1 = decide (0 < z l.2) := by
  rw [bu_tkSgn, Finset.mem_image]
  constructor
  · rintro ⟨j, hjmem, hjl⟩
    rw [Finset.mem_filter] at hjmem
    obtain ⟨_, hj0⟩ := hjmem
    rw [← hjl]
    exact ⟨hj0, rfl⟩
  · rintro ⟨hz, hb⟩
    exact ⟨l.2, Finset.mem_filter.mpr ⟨Finset.mem_univ l.2, hz⟩,
      Prod.ext_iff.mpr ⟨hb.symm, rfl⟩⟩

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_tkNeg_invol](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_tkNeg_invol {n : ℕ} : Function.Involutive (@bu_tkNeg n) := by
  intro l
  obtain ⟨b, i⟩ := l
  cases b <;> rfl

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_tkNeg_inj](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_tkNeg_inj {n : ℕ} : Function.Injective (@bu_tkNeg n) :=
  bu_tkNeg_invol.injective

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_decide_neg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_decide_neg {a : ℤ} (ha : a ≠ 0) :
  decide (0 < -a) = !decide (0 < a) := by
  by_cases h : 0 < a
  · simp [h]; omega
  · simp [h]; omega

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_tkSgn_neg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_tkSgn_neg {n : ℕ} (z : Fin n → ℤ) :
  bu_tkSgn (-z) = (bu_tkSgn z).image bu_tkNeg := by
  ext ⟨b, i⟩
  rw [bu_mem_tkSgn, Finset.mem_image]
  constructor
  · intro h
    have h' : -z i ≠ 0 ∧ b = decide (0 < -z i) := h
    obtain ⟨hz, hb⟩ := h'
    have hz0 : z i ≠ 0 := by simpa using hz
    refine ⟨(!b, i), bu_mem_tkSgn.mpr ⟨hz0, ?_⟩, ?_⟩
    · change (!b) = decide (0 < z i)
      have hb2 : (!b) = !(decide (0 < -z i)) := congrArg Bool.not hb
      rw [hb2, bu_decide_neg hz0, Bool.not_not]
    · change ((!(!b)), i) = (b, i)
      rw [Bool.not_not]
  · rintro ⟨⟨b', j⟩, hmem, heq⟩
    have hmem' : z j ≠ 0 ∧ b' = decide (0 < z j) := bu_mem_tkSgn.mp hmem
    obtain ⟨hz0, hb'⟩ := hmem'
    have h1 : (!b') = b := congrArg Prod.fst heq
    have h2 : j = i := congrArg Prod.snd heq
    rw [h2] at hz0 hb'
    refine ⟨by simpa using hz0, ?_⟩
    change b = decide (0 < -z i)
    rw [← h1, hb', bu_decide_neg hz0]

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_tkLe_neg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_tkLe_neg {n : ℕ} {z w : Fin n → ℤ} :
  bu_tkLe (-z) (-w) ↔ bu_tkLe z w := by
  simp only [bu_tkLe, Pi.neg_apply]
  constructor
  · intro h i
    obtain hcon | ⟨h0, hw⟩ | ⟨h0, hw⟩ := h i
    · exact Or.inl (by omega)
    · exact Or.inr (Or.inr ⟨by omega, by omega⟩)
    · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
  · intro h i
    obtain hcon | ⟨h0, hw⟩ | ⟨h0, hw⟩ := h i
    · exact Or.inl (by omega)
    · exact Or.inr (Or.inr ⟨by omega, by omega⟩)
    · exact Or.inr (Or.inl ⟨by omega, by omega⟩)

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_tkSgn_consistent](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_tkSgn_consistent {n : ℕ} {z : Fin n → ℤ} {b : Bool} {i : Fin n}
  (h : (b, i) ∈ bu_tkSgn z) : (!b, i) ∉ bu_tkSgn z := by
  have h' : z i ≠ 0 ∧ b = decide (0 < z i) := bu_mem_tkSgn.mp h
  obtain ⟨hz, hb⟩ := h'
  intro hcon
  have hcon' : z i ≠ 0 ∧ (!b) = decide (0 < z i) := bu_mem_tkSgn.mp hcon
  rw [hb] at hcon'
  exact absurd hcon'.2 (by cases b <;> simp)

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_tkSgn_snd_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_tkSgn_snd_injective {n : ℕ} {z : Fin n → ℤ} :
  Set.InjOn Prod.snd (↑(bu_tkSgn z) : Set (Bool × Fin n)) := by
  intro a ha b hb hab
  rw [Finset.mem_coe] at ha hb
  obtain ⟨a1, a2⟩ := a
  obtain ⟨b1, b2⟩ := b
  have hab2 : a2 = b2 := hab
  subst hab2
  have ha' : z a2 ≠ 0 ∧ a1 = decide (0 < z a2) := bu_mem_tkSgn.mp ha
  have hb' : z a2 ≠ 0 ∧ b1 = decide (0 < z a2) := bu_mem_tkSgn.mp hb
  rw [ha'.2, hb'.2]

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_tkSgn_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_tkSgn_card {n : ℕ} (z : Fin n → ℤ) :
  (bu_tkSgn z).card = (Finset.univ.filter fun i => z i ≠ 0).card := by
  rw [bu_tkSgn]
  apply Finset.card_image_of_injOn
  intro a _ b _ hab
  simp only at hab
  exact congrArg Prod.snd hab

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_tkMv_normal_a](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_tkMv_normal_a {n : ℕ} {b t z : Fin n → ℤ}
  (hbt : bu_tkLe b t) (hbz : bu_tkLe b z) (hzt : bu_tkLe z t) :
  bu_tkMv b z ⊆ bu_tkMv b t ∧ z = bu_tkPt b t (bu_tkMv b z) := by
  have hsub : bu_tkMv b z ⊆ bu_tkMv b t := by
    intro i hi
    have hne : z i ≠ b i := by
      have hm := hi
      rwa [bu_tkMv, Finset.mem_filter] at hm
    have hmem : t i ≠ b i := by
      have h1 := hbz i
      have h2 := hzt i
      have h3 := hbt i
      obtain c1 | ⟨s1, e1⟩ | ⟨s1, e1⟩ := h1
      · exact absurd c1 hne
      · rcases h2 with c2 | ⟨s2, e2⟩ | ⟨s2, e2⟩ <;>
        obtain c3 | ⟨s3, e3⟩ | ⟨s3, e3⟩ <;> omega := h3
      · rcases h2 with c2 | ⟨s2, e2⟩ | ⟨s2, e2⟩ <;>
        obtain c3 | ⟨s3, e3⟩ | ⟨s3, e3⟩ <;> omega := h3
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hmem⟩
  refine ⟨hsub, ?_⟩
  funext i
  by_cases h : z i = b i
  · have hi : i ∉ bu_tkMv b z := by
    rw [bu_tkMv, Finset.mem_filter]
    simp [h]
    have e : (bu_tkPt b t (bu_tkMv b z)) i = b i := by simp [bu_tkPt, hi]
    rwa [e]
  · have hi : i ∈ bu_tkMv b z :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩
    have e : (bu_tkPt b t (bu_tkMv b z)) i = t i := by simp [bu_tkPt, hi]
    rw [e]
    have h1 := hbz i
    have h2 := hzt i
    have h3 := hbt i
    obtain c1 | ⟨s1, e1⟩ | ⟨s1, e1⟩ := h1
    · exact absurd c1 h
    · rcases h2 with c2 | ⟨s2, e2⟩ | ⟨s2, e2⟩ <;>
      obtain c3 | ⟨s3, e3⟩ | ⟨s3, e3⟩ <;> omega := h3
    · rcases h2 with c2 | ⟨s2, e2⟩ | ⟨s2, e2⟩ <;>
      obtain c3 | ⟨s3, e3⟩ | ⟨s3, e3⟩ <;> omega := h3

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_tkPt_mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_tkPt_mono {n : ℕ} {b t : Fin n → ℤ} (hbt : bu_tkLe b t)
  {M1 M2 : Finset (Fin n)} (h : M1 ⊆ M2) :
  bu_tkLe (bu_tkPt b t M1) (bu_tkPt b t M2) := by
  intro i
  have h5 := hbt i
  by_cases h1 : i ∈ M1
  · have h2 : i ∈ M2 := h h1
    have e1 : (bu_tkPt b t M1) i = t i := by simp [bu_tkPt, h1]
    have e2 : (bu_tkPt b t M2) i = t i := by simp [bu_tkPt, h2]
    rw [e1, e2]
    exact Or.inl rfl
  · by_cases h3 : i ∈ M2
    · have e1 : (bu_tkPt b t M1) i = b i := by simp [bu_tkPt, h1]
      have e2 : (bu_tkPt b t M2) i = t i := by simp [bu_tkPt, h3]
      rwa [e1, e2]
    · have e1 : (bu_tkPt b t M1) i = b i := by simp [bu_tkPt, h1]
      have e2 : (bu_tkPt b t M2) i = b i := by simp [bu_tkPt, h3]
      rw [e1, e2]
      exact Or.inl rfl

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_tkMv_mono_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_tkMv_mono_of_le {n : ℕ} {b z w : Fin n → ℤ}
  (hbz : bu_tkLe b z) (hbw : bu_tkLe b w) (hzw : bu_tkLe z w) :
  bu_tkMv b z ⊆ bu_tkMv b w := by
  intro i hi
  have hne : z i ≠ b i := by
    have hm := hi
    rwa [bu_tkMv, Finset.mem_filter] at hm
  have hmem : w i ≠ b i := by
    have h1 := hbz i
    have h0 := hzw i
    have h3 := hbw i
    obtain c1 | ⟨s1, e1⟩ | ⟨s1, e1⟩ := h1
    · exact absurd c1 hne
    · rcases h0 with c0 | ⟨s0, e0⟩ | ⟨s0, e0⟩ <;>
      obtain c3 | ⟨s3, e3⟩ | ⟨s3, e3⟩ <;> omega := h3
    · rcases h0 with c0 | ⟨s0, e0⟩ | ⟨s0, e0⟩ <;>
      obtain c3 | ⟨s3, e3⟩ | ⟨s3, e3⟩ <;> omega := h3
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hmem⟩

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_tkMv_le_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_tkMv_le_iff {n : ℕ} {b t z w : Fin n → ℤ}
  (hbt : bu_tkLe b t) (hbz : bu_tkLe b z) (hzt : bu_tkLe z t)
  (hbw : bu_tkLe b w) (hwt : bu_tkLe w t) :
  bu_tkLe z w ↔ bu_tkMv b z ⊆ bu_tkMv b w := by
  constructor
  · intro hzw
    exact bu_tkMv_mono_of_le hbz hbw hzw
  · intro hsub
    have ez : z = bu_tkPt b t (bu_tkMv b z) :=
      (bu_tkMv_normal_a hbt hbz hzt).2
    have ew : w = bu_tkPt b t (bu_tkMv b w) :=
      (bu_tkMv_normal_a hbt hbw hwt).2
    rw [ez, ew]
    exact bu_tkPt_mono hbt hsub

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_tkPt_mem_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_tkPt_mem_of_mem {n : ℕ} {b t : Fin n → ℤ} (hbt : bu_tkLe b t)
  {M : Finset (Fin n)} (hM : M ⊆ bu_tkMv b t) :
  bu_tkLe b (bu_tkPt b t M) ∧ bu_tkLe (bu_tkPt b t M) t ∧
    bu_tkMv b (bu_tkPt b t M) = M := by
  have h1 : bu_tkLe b (bu_tkPt b t M) := by
    intro i
    have h5 := hbt i
    by_cases hM' : i ∈ M
    · have e : (bu_tkPt b t M) i = t i := by simp [bu_tkPt, hM']
      rwa [e]
    · have e : (bu_tkPt b t M) i = b i := by simp [bu_tkPt, hM']
      rw [e]
      exact Or.inl rfl
  have h2 : bu_tkLe (bu_tkPt b t M) t := by
    intro i
    have h5 := hbt i
    by_cases hM' : i ∈ M
    · have e : (bu_tkPt b t M) i = t i := by simp [bu_tkPt, hM']
      rw [e]
      exact Or.inl rfl
    · have e : (bu_tkPt b t M) i = b i := by simp [bu_tkPt, hM']
      rwa [e]
  refine ⟨h1, h2, ?_⟩
  ext i
  rw [bu_tkMv, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  by_cases hM' : i ∈ M
  · have e : (bu_tkPt b t M) i = t i := by simp [bu_tkPt, hM']
    rw [e]
    have ht : t i ≠ b i := by
      have hmem := hM hM'
      rwa [bu_tkMv, Finset.mem_filter] at hmem
    simp [hM', ht]
  · have e : (bu_tkPt b t M) i = b i := by simp [bu_tkPt, hM']
    rw [e]
    simp [hM']

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_tkMv_sub_support](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_tkMv_sub_support {n : ℕ} {b t : Fin n → ℤ} (hbt : bu_tkLe b t)
  (i : Fin n) (hi : t i ≠ b i) : t i ≠ 0 := by
  have h5 := hbt i
  obtain c5 | ⟨s5, e5⟩ | ⟨s5, e5⟩ := h5
  · exact absurd c5 hi
  · omega
  · omega

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_tkMv_abs_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_tkMv_abs_lt {n : ℕ} {b t : Fin n → ℤ} (hbt : bu_tkLe b t)
  (i : Fin n) (hi : t i ≠ b i) : |b i| < |t i| := by
  have h5 := hbt i
  obtain c5 | ⟨s5, e5⟩ | ⟨s5, e5⟩ := h5
  · exact absurd c5 hi
  · rw [e5, abs_of_nonneg s5, abs_of_nonneg (by omega : (0 : ℤ) ≤ b i + 1)]
    omega
  · rw [e5, abs_of_nonpos s5, abs_of_nonpos (by omega : b i - 1 ≤ (0 : ℤ))]
    omega

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_tkMv_eq_off](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_tkMv_eq_off {n : ℕ} {b t : Fin n → ℤ}
  (i : Fin n) (hi : i ∉ bu_tkMv b t) : t i = b i := by
  by_contra h
  have hm := hi
  rw [bu_tkMv, Finset.mem_filter] at hm
  exact hm ⟨Finset.mem_univ i, h⟩

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_tkMv_support_mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_tkMv_support_mono {n : ℕ} {b t : Fin n → ℤ} (hbt : bu_tkLe b t)
  (i : Fin n) (hi : b i ≠ 0) : t i ≠ 0 := by
  have h5 := hbt i
  obtain c5 | ⟨s5, e5⟩ | ⟨s5, e5⟩ := h5
  · rw [c5]
    exact hi
  · omega
  · omega

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_mem_tkExt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_mem_tkExt {α : Type*} [DecidableEq α] {C : Finset (Finset α)}
  {X : Finset α} {M : Finset α} :
  M ∈ bu_tkExt C X ↔ M ∈ X.powerset ∧ M ∉ C ∧ ∀ A ∈ C, A ⊆ M ∨ M ⊆ A := by
  rw [bu_tkExt, Finset.mem_filter]

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_gap_lemma](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_gap_lemma {α : Type*} [DecidableEq α] {X : Finset α}
  {C : Finset (Finset α)} (hsubX : ∀ A ∈ C, A ⊆ X) (hempty : ∅ ∈ C)
  (hX : X ∈ C) (hcomp : ∀ A ∈ C, ∀ B ∈ C, A ⊆ B ∨ B ⊆ A) :
  C.card ≤ X.card + 1 ∧
  (C.card = X.card + 1 → bu_tkExt C X = ∅) ∧
  (C.card = X.card → (bu_tkExt C X).card = 2) := by
  have hinj : Set.InjOn Finset.card (↑C : Set (Finset α)) := by
    intro A hA B hB he
    have hA' : A ∈ C := Finset.mem_coe.mp hA
    have hB' : B ∈ C := Finset.mem_coe.mp hB
    obtain h | h := hcomp A hA' B hB'
    · exact Finset.eq_of_subset_of_card_le h (le_of_eq he.symm)
    · exact (Finset.eq_of_subset_of_card_le h (le_of_eq he)).symm
  have himg : C.image Finset.card ⊆ Finset.range (X.card + 1) := by
    intro k hk
    rw [Finset.mem_image] at hk
    obtain ⟨A, hA, rfl⟩ := hk
    rw [Finset.mem_range]
    have hAle : A.card ≤ X.card := Finset.card_le_card (hsubX A hA)
    omega
  have hcardle : C.card ≤ X.card + 1 := by
    calc C.card = (C.image Finset.card).card :=
      (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.range (X.card + 1)).card := Finset.card_le_card himg
      _ = X.card + 1 := Finset.card_range _
  have hle_sub : ∀ A ∈ C, ∀ D ∈ C, A.card ≤ D.card → A ⊆ D := by
    intro A hA D hD hle
    obtain h | h := hcomp A hA D hD
    · exact h
    · have e : D = A := Finset.eq_of_subset_of_card_le h hle
      rw [e]
  refine ⟨hcardle, ?_, ?_⟩
  · intro hc
    rw [Finset.eq_empty_iff_forall_notMem]
    intro M hM
    rw [bu_tkExt, Finset.mem_filter] at hM
    obtain ⟨hMX, hMnot, hMcomp⟩ := hM
    have hMcard : M.card ≤ X.card :=
      Finset.card_le_card (Finset.mem_powerset.mp hMX)
    have himgeq : C.image Finset.card = Finset.range (X.card + 1) := by
      apply Finset.eq_of_subset_of_card_le himg
      rw [Finset.card_image_of_injOn hinj, Finset.card_range]
      omega
    have hmem : M.card ∈ C.image Finset.card := by
      rw [himgeq, Finset.mem_range]
      omega
    obtain ⟨D, hD, hDcard⟩ := Finset.mem_image.mp hmem
    have e : D = M := by
      obtain h | h := hMcomp D hD
      · exact Finset.eq_of_subset_of_card_le h (by omega)
      · exact (Finset.eq_of_subset_of_card_le h (by omega)).symm
    have hMC : M ∈ C := by
      rwa [← e]
    exact hMnot hMC
  · intro hc
    have himgcard : (C.image Finset.card).card = X.card := by
      rw [Finset.card_image_of_injOn hinj, hc]
    have hsd1 : (Finset.range (X.card + 1) \ C.image Finset.card).card = 1 := by
      rw [Finset.card_sdiff_of_subset himg, Finset.card_range, himgcard]
      omega
    obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hsd1
    have hknot : k ∉ C.image Finset.card := by
      have hkmem : k ∈ Finset.range (X.card + 1) \ C.image Finset.card := by
        rw [hk]
        exact Finset.mem_singleton_self k
      exact (Finset.mem_sdiff.mp hkmem).2
    have hkrange : k ∈ Finset.range (X.card + 1) := by
      have hkmem : k ∈ Finset.range (X.card + 1) \ C.image Finset.card := by
        rw [hk]
        exact Finset.mem_singleton_self k
      exact (Finset.mem_sdiff.mp hkmem).1
    have h0mem : (0 : ℕ) ∈ C.image Finset.card :=
      Finset.mem_image.mpr ⟨∅, hempty, Finset.card_empty⟩
    have hXmem : X.card ∈ C.image Finset.card :=
      Finset.mem_image.mpr ⟨X, hX, rfl⟩
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hknot h0mem
    have hkX : k < X.card := by
      rw [Finset.mem_range] at hkrange
      by_contra hcon
      have hkk : k = X.card := by omega
      rw [hkk] at hknot
      exact hknot hXmem
    have hkpos : 0 < k := by omega
    have hslot : ∀ j, j ∈ Finset.range (X.card + 1) → j ≠ k → ∃ D ∈ C, D.card = j := by
      intro j hj hjk
      have hj' : j ∈ C.image Finset.card := by
        by_contra hcon
        have hjsd : j ∈ Finset.range (X.card + 1) \ C.image Finset.card :=
          Finset.mem_sdiff.mpr ⟨hj, hcon⟩
        rw [hk] at hjsd
        exact hjk (Finset.mem_singleton.mp hjsd)
      exact Finset.mem_image.mp hj'
    obtain ⟨A, hA, hAcard⟩ := hslot (k - 1) (by
      rw [Finset.mem_range]; omega) (by omega)
    obtain ⟨B, hB, hBcard⟩ := hslot (k + 1) (by
      rw [Finset.mem_range]; omega) (by omega)
    have hAB : A ⊆ B := hle_sub A hA B hB (by omega)
    have hBAcard : (B \ A).card = 2 := by
      rw [Finset.card_sdiff_of_subset hAB, hBcard, hAcard]
      omega
    obtain ⟨a, a', haa', haa'B⟩ := Finset.card_eq_two.mp hBAcard
    have haBA : a ∈ B \ A := by
      rw [haa'B]
      exact Finset.mem_insert_self a {a'}
    have haB : a ∈ B := (Finset.mem_sdiff.mp haBA).1
    have haA : a ∉ A := (Finset.mem_sdiff.mp haBA).2
    have haBA' : a' ∈ B \ A := by
      rw [haa'B]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self a')
    have haB' : a' ∈ B := (Finset.mem_sdiff.mp haBA').1
    have haA' : a' ∉ A := (Finset.mem_sdiff.mp haBA').2
    have hBX : B ⊆ X := hsubX B hB
    have haX : a ∈ X := hBX haB
    have haX' : a' ∈ X := hBX haB'
    have hAX : A ⊆ X := Finset.Subset.trans (hle_sub A hA B hB (by omega)) hBX
    have hcardA : (insert a A).card = k := by
      rw [Finset.card_insert_of_notMem haA, hAcard]
      omega
    have hcardA' : (insert a' A).card = k := by
      rw [Finset.card_insert_of_notMem haA', hAcard]
      omega
    have hnotC : insert a A ∉ C := by
      intro hcon
      exact hknot (Finset.mem_image.mpr ⟨insert a A, hcon, hcardA⟩)
    have hnotC' : insert a' A ∉ C := by
      intro hcon
      exact hknot (Finset.mem_image.mpr ⟨insert a' A, hcon, hcardA'⟩)
    have hcompA : ∀ D ∈ C, D ⊆ insert a A ∨ insert a A ⊆ D := by
      intro D hD
      have hDcardle : D.card ≤ X.card := Finset.card_le_card (hsubX D hD)
      by_cases hDk : D.card = k
      · exfalso
        have hmemD : D.card ∈ C.image Finset.card :=
          Finset.mem_image.mpr ⟨D, hD, rfl⟩
        rw [hDk] at hmemD
        exact hknot hmemD
      · by_cases hle : D.card ≤ k - 1
        · left
          have hDA : D ⊆ A := hle_sub D hD A hA (by omega)
          exact Finset.Subset.trans hDA (Finset.subset_insert a A)
        · right
          have hge : k + 1 ≤ D.card := by omega
          have hBD : B ⊆ D := hle_sub B hB D hD (by omega)
          have hAD : A ⊆ D := Finset.Subset.trans
            (hle_sub A hA B hB (by omega)) hBD
          exact Finset.insert_subset (hBD haB) hAD
    have hcompA' : ∀ D ∈ C, D ⊆ insert a' A ∨ insert a' A ⊆ D := by
      intro D hD
      have hDcardle : D.card ≤ X.card := Finset.card_le_card (hsubX D hD)
      by_cases hDk : D.card = k
      · exfalso
        have hmemD : D.card ∈ C.image Finset.card :=
          Finset.mem_image.mpr ⟨D, hD, rfl⟩
        rw [hDk] at hmemD
        exact hknot hmemD
      · by_cases hle : D.card ≤ k - 1
        · left
          have hDA : D ⊆ A := hle_sub D hD A hA (by omega)
          exact Finset.Subset.trans hDA (Finset.subset_insert a' A)
        · right
          have hge : k + 1 ≤ D.card := by omega
          have hBD : B ⊆ D := hle_sub B hB D hD (by omega)
          have hAD : A ⊆ D := Finset.Subset.trans
            (hle_sub A hA B hB (by omega)) hBD
          exact Finset.insert_subset (hBD haB') hAD
    have hinsAX : insert a A ∈ bu_tkExt C X := by
      rw [bu_tkExt, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.insert_subset haX hAX, hnotC, hcompA⟩
    have hinsa'X : insert a' A ∈ bu_tkExt C X := by
      rw [bu_tkExt, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.insert_subset haX' hAX, hnotC', hcompA'⟩
    have hne : insert a A ≠ insert a' A := by
      intro hcon
      have hmem : a ∈ insert a' A := by
        rw [← hcon]
        exact Finset.mem_insert_self a A
      rw [Finset.mem_insert] at hmem
      obtain h | h := hmem
      · exact haa' h
      · exact haA h
    have hExt : bu_tkExt C X = {insert a A, insert a' A} := by
      ext M
      constructor
      · intro hM
        rw [bu_tkExt, Finset.mem_filter] at hM
        obtain ⟨hMX, hMnot, hMcomp⟩ := hM
        have hMcardle : M.card ≤ X.card :=
          Finset.card_le_card (Finset.mem_powerset.mp hMX)
        have hMkrange : M.card ∈ Finset.range (X.card + 1) := by
          rw [Finset.mem_range]
          omega
        have hMcard : M.card = k := by
          by_contra hcon
          obtain ⟨D, hD, hDcard⟩ := hslot M.card hMkrange hcon
          have e : D = M := by
            obtain h | h := hMcomp D hD
            · exact Finset.eq_of_subset_of_card_le h (by omega)
            · exact (Finset.eq_of_subset_of_card_le h (by omega)).symm
          have hMC : M ∈ C := by
            rwa [← e]
          exact hMnot hMC
        have hAM : A ⊆ M := by
          obtain h | h := hMcomp A hA
          · exact h
          · exfalso
            have hle := Finset.card_le_card h
            omega
        have hMB : M ⊆ B := by
          obtain h | h := hMcomp B hB
          · exfalso
            have hle := Finset.card_le_card h
            omega
          · exact h
        have hMAd : (M \ A).card = 1 := by
          rw [Finset.card_sdiff_of_subset hAM, hMcard, hAcard]
          omega
        obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hMAd
        have hxmem : x ∈ M \ A := by
          rw [hx]
          exact Finset.mem_singleton_self x
        have hxM : x ∈ M := (Finset.mem_sdiff.mp hxmem).1
        have hxA : x ∉ A := (Finset.mem_sdiff.mp hxmem).2
        have hxB : x ∈ B \ A :=
          Finset.mem_sdiff.mpr ⟨hMB hxM, hxA⟩
        rw [haa'B, Finset.mem_insert, Finset.mem_singleton] at hxB
        have hMxA : M = insert x A := by
          have hcc : (insert x A).card = M.card := by
            rw [Finset.card_insert_of_notMem hxA, hAcard, hMcard]
            omega
          have hsub : insert x A ⊆ M := Finset.insert_subset hxM hAM
          have hle : M.card ≤ (insert x A).card := le_of_eq hcc.symm
          exact (Finset.eq_of_subset_of_card_le hsub hle).symm
        rw [hMxA]
        obtain hxa | hxa := hxB
        · rw [hxa]
          exact Finset.mem_insert_self _ _
        · rw [hxa]
          exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      · intro hM
        rw [Finset.mem_insert, Finset.mem_singleton] at hM
        obtain rfl | rfl := hM
        · exact hinsAX
        · exact hinsa'X
    rw [hExt, Finset.card_pair_eq_two_iff.mpr hne]

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_mem_tkUp](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_mem_tkUp {n m : ℕ} {σ : Finset (Fin n → ℤ)} {v : Fin n → ℤ} :
  v ∈ bu_tkUp m σ ↔ v ∈ bu_tkBox n m ∧ v ∉ σ ∧ bu_tkChain (insert v σ) ∧
    bu_tkS (insert v σ) ⊆ bu_tkS σ := by
  rw [bu_tkUp, Finset.mem_filter]

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_mem_tkUpL](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_mem_tkUpL {n m : ℕ} {σ : Finset (Fin n → ℤ)}
  {v : Fin n → ℤ} {ℓ : Bool × Fin n} :
  v ∈ bu_tkUpL m σ ℓ ↔ v ∈ bu_tkBox n m ∧ v ∉ σ ∧ bu_tkChain (insert v σ) ∧
    bu_tkS (insert v σ) = insert ℓ (bu_tkS σ) := by
  rw [bu_tkUpL, Finset.mem_filter]

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_cofacet_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_cofacet_pos {n : ℕ} {σ : Finset (Fin n → ℤ)} {b t v : Fin n → ℤ}
  (hbσ : b ∈ σ) (htσ : t ∈ σ)
  (hchain : bu_tkChain (insert v σ)) (hv : v ∉ σ) :
  (bu_tkLe b v ∧ bu_tkLe v t) ∨ (bu_tkLe v b ∧ v ≠ b) ∨ (bu_tkLe t v ∧ v ≠ t) := by
  have hbv : bu_tkLe b v ∨ bu_tkLe v b := by
    have h := hchain.2 v (Finset.mem_insert_self v σ) b
      (Finset.mem_insert_of_mem hbσ)
    obtain h | h := h
    · exact Or.inr h
    · exact Or.inl h
  obtain hle | hle := hbv
  · have hvt : bu_tkLe v t ∨ bu_tkLe t v := by
    have h := hchain.2 v (Finset.mem_insert_self v σ) t
      (Finset.mem_insert_of_mem htσ)
    obtain h | h := h
    · exact Or.inl h
    · exact Or.inr h
    obtain h | h := hvt
    · exact Or.inl ⟨hle, h⟩
    · have hne : v ≠ t := by
      rintro rfl
      exact hv htσ
      exact Or.inr (Or.inr ⟨h, hne⟩)
  · have hne : v ≠ b := by
    rintro rfl
    exact hv hbσ
    exact Or.inr (Or.inl ⟨hle, hne⟩)

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_tkPull_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_tkPull_le {n : ℕ} {b : Fin n → ℤ} {c : Fin n} (hne : b c ≠ 0) :
  bu_tkLe (bu_tkPull b c) b ∧ bu_tkPull b c ≠ b := by
  have hle : bu_tkLe (bu_tkPull b c) b := by
    intro i
    by_cases hic : i = c
    · rw [hic]
      by_cases hpos : 0 < b c
      · have e : (bu_tkPull b c) c = b c - 1 := by simp [bu_tkPull, hpos]
        rw [e]
        exact Or.inr (Or.inl ⟨by omega, by omega⟩)
      · have e : (bu_tkPull b c) c = b c + 1 := by simp [bu_tkPull, hpos]
        rw [e]
        exact Or.inr (Or.inr ⟨by omega, by omega⟩)
    · have e : (bu_tkPull b c) i = b i := by simp [bu_tkPull, hic]
      rw [e]
      exact Or.inl rfl
  refine ⟨hle, ?_⟩
  intro hcon
  have hc := congrArg (fun z => z c) hcon
  by_cases hpos : 0 < b c
  · have e : (bu_tkPull b c) c = b c - 1 := by simp [bu_tkPull, hpos]
    omega
  · have e : (bu_tkPull b c) c = b c + 1 := by simp [bu_tkPull, hpos]
    omega

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_tkPull_abs](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_tkPull_abs {n : ℕ} {b : Fin n → ℤ} {c : Fin n} (hne : b c ≠ 0) :
  |bu_tkPull b c c| ≤ |b c| := by
  by_cases hpos : 0 < b c
  · have e : (bu_tkPull b c) c = b c - 1 := by simp [bu_tkPull, hpos]
    rw [e, abs_of_nonneg (by omega : (0 : ℤ) ≤ b c - 1),
      abs_of_nonneg (by omega : (0 : ℤ) ≤ b c)]
    omega
  · have e : (bu_tkPull b c) c = b c + 1 := by simp [bu_tkPull, hpos]
    have h1 : b c + 1 ≤ (0 : ℤ) := by omega
    have h2 : b c ≤ (0 : ℤ) := by omega
    rw [e, abs_of_nonpos h1, abs_of_nonpos h2]
    omega

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_tkPull_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_tkPull_mem_box {n m : ℕ} {b : Fin n → ℤ} {c : Fin n}
  (hb : b ∈ bu_tkBox n m) (hne : b c ≠ 0) : bu_tkPull b c ∈ bu_tkBox n m := by
  rw [bu_mem_tkBox] at hb ⊢
  intro i
  by_cases hic : i = c
  · rw [hic]
    exact le_trans (bu_tkPull_abs hne) (hb c)
  · have e : (bu_tkPull b c) i = b i := by simp [bu_tkPull, hic]
    rw [e]
    exact hb i

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_tkPush_up](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_tkPush_up {n : ℕ} {t : Fin n → ℤ} {j : Fin n} (h0 : 0 ≤ t j) :
  bu_tkLe t (bu_tkPush t j 1) ∧ bu_tkPush t j 1 ≠ t := by
  have hle : bu_tkLe t (bu_tkPush t j 1) := by
    intro i
    by_cases hij : i = j
    · rw [hij]
      have e : (bu_tkPush t j 1) j = t j + 1 := by simp [bu_tkPush]
      rw [e]
      exact Or.inr (Or.inl ⟨h0, rfl⟩)
    · have e : (bu_tkPush t j 1) i = t i := by simp [bu_tkPush, hij]
      rw [e]
      exact Or.inl rfl
  refine ⟨hle, ?_⟩
  intro hcon
  have hc := congrArg (fun z => z j) hcon
  have e : (bu_tkPush t j 1) j = t j + 1 := by simp [bu_tkPush]
  rw [e] at hc
  omega

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_tkPush_down](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_tkPush_down {n : ℕ} {t : Fin n → ℤ} {j : Fin n} (h0 : t j ≤ 0) :
  bu_tkLe t (bu_tkPush t j (-1)) ∧ bu_tkPush t j (-1) ≠ t := by
  have hle : bu_tkLe t (bu_tkPush t j (-1)) := by
    intro i
    by_cases hij : i = j
    · rw [hij]
      have e : (bu_tkPush t j (-1)) j = t j + -1 := by simp [bu_tkPush]
      rw [e]
      exact Or.inr (Or.inr ⟨h0, by omega⟩)
    · have e : (bu_tkPush t j (-1)) i = t i := by simp [bu_tkPush, hij]
      rw [e]
      exact Or.inl rfl
  refine ⟨hle, ?_⟩
  intro hcon
  have hc := congrArg (fun z => z j) hcon
  have e : (bu_tkPush t j (-1)) j = t j + -1 := by simp [bu_tkPush]
  rw [e] at hc
  omega

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_inside_mem_ext](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_inside_mem_ext {n : ℕ} {σ : Finset (Fin n → ℤ)} {b t v : Fin n → ℤ}
  (hbt : bu_tkLe b t) (hbot : ∀ z ∈ σ, bu_tkLe b z) (htop : ∀ z ∈ σ, bu_tkLe z t)
  (hchain : bu_tkChain (insert v σ))
  (hbv : bu_tkLe b v) (hvt : bu_tkLe v t) (hv : v ∉ σ) :
  bu_tkMv b v ∈ bu_tkExt (σ.image (bu_tkMv b)) (bu_tkMv b t) := by
  rw [bu_mem_tkExt]
  refine ⟨Finset.mem_powerset.mpr (bu_tkMv_mono_of_le hbv hbt hvt), ?_, ?_⟩
  · intro hcon
    rw [Finset.mem_image] at hcon
    obtain ⟨z, hz, hze⟩ := hcon
    have ev : v = bu_tkPt b t (bu_tkMv b v) := (bu_tkMv_normal_a hbt hbv hvt).2
    have ez : z = bu_tkPt b t (bu_tkMv b z) :=
      (bu_tkMv_normal_a hbt (hbot z hz) (htop z hz)).2
    have heq : v = z := by rw [ev, ez, hze]
    subst heq
    exact hv hz
  · intro A hA
    rw [Finset.mem_image] at hA
    obtain ⟨z, hz, rfl⟩ := hA
    have hcomp : bu_tkLe v z ∨ bu_tkLe z v := hchain.2 v
      (Finset.mem_insert_self v σ) z (Finset.mem_insert_of_mem hz)
    obtain h | h := hcomp
    · exact Or.inr ((bu_tkMv_le_iff hbt hbv hvt (hbot z hz) (htop z hz)).mp h)
    · exact Or.inl ((bu_tkMv_le_iff hbt (hbot z hz) (htop z hz) hbv hvt).mp h)

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_below_eq_pull](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_below_eq_pull {n : ℕ} {b v : Fin n → ℤ} {c : Fin n}
  (hvb : bu_tkLe v b) (hD : bu_tkMv v b = {c}) : v = bu_tkPull b c := by
  funext i
  by_cases hic : i = c
  · rw [hic]
    have hvc : v c ≠ b c := by
      have hm : c ∈ bu_tkMv v b := by
        rw [hD]
        exact Finset.mem_singleton_self c
      rw [bu_tkMv, Finset.mem_filter] at hm
      exact Ne.symm hm.2
    have h1 := hvb c
    by_cases hpos : 0 < b c
    · have e : (bu_tkPull b c) c = b c - 1 := by simp [bu_tkPull, hpos]
      rw [e]
      obtain c1 | ⟨s1, e1⟩ | ⟨s1, e1⟩ := h1
      · exact absurd c1.symm hvc
      · omega
      · omega
    · have e : (bu_tkPull b c) c = b c + 1 := by simp [bu_tkPull, hpos]
      rw [e]
      obtain c1 | ⟨s1, e1⟩ | ⟨s1, e1⟩ := h1
      · exact absurd c1.symm hvc
      · omega
      · omega
  · have hvi : v i = b i := by
    have hni : i ∉ bu_tkMv v b := by
      rw [hD]
      simp [hic]
    exact (bu_tkMv_eq_off i hni).symm
    have hpi : bu_tkPull b c i = b i := by simp [bu_tkPull, hic]
    exact hvi.trans hpi.symm

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_above_eq_push](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_above_eq_push {n : ℕ} {t v : Fin n → ℤ} {c : Fin n}
  (htc : t c ≠ 0) (htv : bu_tkLe t v) (hE : bu_tkMv t v = {c}) :
  v = bu_tkPush t c (if 0 < t c then 1 else -1) := by
  funext i
  by_cases hic : i = c
  · rw [hic]
    have hvc : v c ≠ t c := by
      have hm : c ∈ bu_tkMv t v := by
        rw [hE]
        exact Finset.mem_singleton_self c
      rwa [bu_tkMv, Finset.mem_filter] at hm
    have h1 := htv c
    by_cases hpos : 0 < t c
    · have es : (if 0 < t c then (1 : ℤ) else -1) = 1 := by simp [hpos]
      have ep : (bu_tkPush t c 1) c = t c + 1 := by simp [bu_tkPush]
      rw [es, ep]
      obtain c1 | ⟨s1, e1⟩ | ⟨s1, e1⟩ := h1
      · exact absurd c1 hvc
      · exact e1
      · omega
    · have es : (if 0 < t c then (1 : ℤ) else -1) = -1 := by simp [hpos]
      have ep : (bu_tkPush t c (-1)) c = t c + -1 := by simp [bu_tkPush]
      rw [es, ep]
      obtain c1 | ⟨s1, e1⟩ | ⟨s1, e1⟩ := h1
      · exact absurd c1 hvc
      · omega
      · omega
  · have hvi : v i = t i := by
    have hni : i ∉ bu_tkMv t v := by
      rw [hE]
      simp [hic]
    exact bu_tkMv_eq_off i hni
    have hpi : bu_tkPush t c (if 0 < t c then 1 else -1) i = t i := by
      simp [bu_tkPush, hic]
    exact hvi.trans hpi.symm

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_pull_le_chain](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_pull_le_chain {n : ℕ} {σ : Finset (Fin n → ℤ)} {b t : Fin n → ℤ}
  {c : Fin n} (hbt : bu_tkLe b t)
  (hzn : ∀ z ∈ σ, bu_tkMv b z ⊆ bu_tkMv b t ∧ z = bu_tkPt b t (bu_tkMv b z))
  (hcX : c ∉ bu_tkMv b t) (hne : b c ≠ 0)
  (z : Fin n → ℤ) (hz : z ∈ σ) :
  bu_tkLe (bu_tkPull b c) z := by
  intro i
  have hMz : bu_tkMv b z ⊆ bu_tkMv b t := (hzn z hz).1
  have ez : z = bu_tkPt b t (bu_tkMv b z) := (hzn z hz).2
  by_cases hic : i = c
  · rw [hic]
    have hcMz : c ∉ bu_tkMv b z := fun hcon => hcX (hMz hcon)
    have hzc : z c = b c := by
      have e2 : (bu_tkPt b t (bu_tkMv b z)) c = b c := by simp [bu_tkPt, hcMz]
      rwa [ez]
    rw [hzc]
    by_cases hpos : 0 < b c
    · have e : (bu_tkPull b c) c = b c - 1 := by simp [bu_tkPull, hpos]
      rw [e]
      exact Or.inr (Or.inl ⟨by omega, by omega⟩)
    · have e : (bu_tkPull b c) c = b c + 1 := by simp [bu_tkPull, hpos]
      rw [e]
      exact Or.inr (Or.inr ⟨by omega, by omega⟩)
  · have e : (bu_tkPull b c) i = b i := by simp [bu_tkPull, hic]
    rw [e]
    by_cases hmem : i ∈ bu_tkMv b z
    · have hzi : z i = t i := by
      have e2 : (bu_tkPt b t (bu_tkMv b z)) i = t i := by simp [bu_tkPt, hmem]
      rwa [ez]
      rw [hzi]
      exact hbt i
    · have hzi : z i = b i := by
      have e2 : (bu_tkPt b t (bu_tkMv b z)) i = b i := by simp [bu_tkPt, hmem]
      rwa [ez]
      rw [hzi]
      exact Or.inl rfl

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_push_le_chain](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_push_le_chain {n : ℕ} {σ : Finset (Fin n → ℤ)} {b t : Fin n → ℤ}
  {j : Fin n} {s : ℤ} (hs : s = 1 ∨ s = -1)
  (hsign : (s = 1 → 0 ≤ t j) ∧ (s = -1 → t j ≤ 0))
  (htop : ∀ z ∈ σ, bu_tkLe z t)
  (hzn : ∀ z ∈ σ, bu_tkMv b z ⊆ bu_tkMv b t ∧ z = bu_tkPt b t (bu_tkMv b z))
  (hjX : j ∉ bu_tkMv b t) (hjt : t j = b j)
  (z : Fin n → ℤ) (hz : z ∈ σ) :
  bu_tkLe z (bu_tkPush t j s) := by
  intro i
  have h1 := (htop z hz) i
  have hMz : bu_tkMv b z ⊆ bu_tkMv b t := (hzn z hz).1
  have ez : z = bu_tkPt b t (bu_tkMv b z) := (hzn z hz).2
  by_cases hij : i = j
  · rw [hij]
    have hjMz : j ∉ bu_tkMv b z := fun hcon => hjX (hMz hcon)
    have hzj : z j = t j := by
      have e2 : (bu_tkPt b t (bu_tkMv b z)) j = b j := by simp [bu_tkPt, hjMz]
      rw [ez, e2, hjt]
    have ep : (bu_tkPush t j s) j = t j + s := by simp [bu_tkPush]
    rw [hzj, ep]
    obtain rfl | rfl := hs
    · exact Or.inr (Or.inl ⟨hsign.1 rfl, by omega⟩)
    · exact Or.inr (Or.inr ⟨hsign.2 rfl, by omega⟩)
  · have ep : (bu_tkPush t j s) i = t i := by simp [bu_tkPush, hij]
    rwa [ep]

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_tkMv_natAbs_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_tkMv_natAbs_lt {n : ℕ} {b t : Fin n → ℤ} (hbt : bu_tkLe b t)
  (i : Fin n) (hi : t i ≠ b i) : (b i).natAbs < (t i).natAbs := by
  have h5 := hbt i
  obtain c5 | ⟨s5, e5⟩ | ⟨s5, e5⟩ := h5
  · exact absurd c5 hi
  · omega
  · omega

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_mem_tkBox_natAbs](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_mem_tkBox_natAbs {n m : ℕ} {z : Fin n → ℤ} :
  z ∈ bu_tkBox n m ↔ ∀ i, (z i).natAbs ≤ m := by
  rw [bu_mem_tkBox]
  constructor
  · intro h i
    have h1 := h i
    rw [Int.abs_eq_natAbs] at h1
    exact_mod_cast h1
  · intro h i
    have h1 := h i
    rw [Int.abs_eq_natAbs]
    exact_mod_cast h1

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_eq_singleton_of_sub](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_eq_singleton_of_sub {α : Type*} {s : Finset α} {c : α}
  (hsub : s ⊆ {c}) (hne : s.Nonempty) : s = {c} := by
  have hcard : s.card = 1 := by
    have h1 : s.card ≤ 1 := by
      calc s.card ≤ ({c} : Finset α).card := Finset.card_le_card hsub
        _ = 1 := Finset.card_singleton c
    have h2 : 0 < s.card := Finset.card_pos.mpr hne
    omega
  obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcard
  have hxmem : x ∈ ({c} : Finset α) := by
    have h1 : x ∈ s := by
      rw [hx]
      exact Finset.mem_singleton_self x
    exact hsub h1
  have hxc : x = c := Finset.mem_singleton.mp hxmem
  rw [hx, hxc]

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_push_sgn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_push_sgn {n : ℕ} {t : Fin n → ℤ} {c : Fin n} {s : ℤ}
  (hs : s = 1 ∨ s = -1)
  (hsign : (s = 1 → 0 ≤ t c) ∧ (s = -1 → t c ≤ 0)) (htc : t c ≠ 0) :
  bu_tkSgn (bu_tkPush t c s) = bu_tkSgn t := by
  ext ⟨β, i⟩
  simp only [bu_mem_tkSgn]
  by_cases hic : i = c
  · rw [hic]
    have e : (bu_tkPush t c s) c = t c + s := by simp [bu_tkPush]
    rw [e]
    obtain rfl | rfl := hs
    · have h0 : 0 ≤ t c := hsign.1 rfl
      have h1 : t c + 1 ≠ 0 := by omega
      have h2 : decide (0 < t c + 1) = decide (0 < t c) := by
        by_cases hpos : 0 < t c
        · simp [hpos, show (0 : ℤ) < t c + 1 by omega]
        · have htc0 : t c = 0 := by omega
          rw [htc0] at htc
          exact absurd rfl htc
      constructor
      · rintro ⟨_, hβ⟩
        exact ⟨htc, by rw [h2] at hβ; exact hβ⟩
      · rintro ⟨_, hβ⟩
        exact ⟨h1, by rw [h2]; exact hβ⟩
    · have h0 : t c ≤ 0 := hsign.2 rfl
      have h1 : t c + -1 ≠ 0 := by omega
      have h2 : decide (0 < t c + -1) = decide (0 < t c) := by
        by_cases hpos : 0 < t c
        · exfalso
          omega
        · simp [hpos, show ¬ (0 : ℤ) < t c + -1 by omega]
      constructor
      · rintro ⟨_, hβ⟩
        exact ⟨htc, by rw [h2] at hβ; exact hβ⟩
      · rintro ⟨_, hβ⟩
        exact ⟨h1, by rw [h2]; exact hβ⟩
  · have e : (bu_tkPush t c s) i = t i := by simp [bu_tkPush, hic]
    rw [e]

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_push_abs](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_push_abs {n : ℕ} {t : Fin n → ℤ} {c : Fin n} {s : ℤ}
  (hs : s = 1 ∨ s = -1)
  (hsign : (s = 1 → 0 ≤ t c) ∧ (s = -1 → t c ≤ 0)) :
  (bu_tkPush t c s c).natAbs = (t c).natAbs + 1 := by
  have e : (bu_tkPush t c s) c = t c + s := by simp [bu_tkPush]
  rw [e]
  obtain rfl | rfl := hs
  · have h0 := hsign.1 rfl
    omega
  · have h0 := hsign.2 rfl
    omega

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_push_height](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_push_height {n : ℕ} {t : Fin n → ℤ} {c : Fin n} {s : ℤ}
  (hs : s = 1 ∨ s = -1)
  (hsign : (s = 1 → 0 ≤ t c) ∧ (s = -1 → t c ≤ 0)) :
  bu_tkH t < bu_tkH (bu_tkPush t c s) := by
  apply Finset.sum_lt_sum
  · intro i _
    by_cases hic : i = c
    · rw [hic]
      have e : (bu_tkPush t c s) c = t c + s := by simp [bu_tkPush]
      rw [e]
      obtain rfl | rfl := hs
      · have h0 := hsign.1 rfl
        omega
      · have h0 := hsign.2 rfl
        omega
    · have e : (bu_tkPush t c s) i = t i := by simp [bu_tkPush, hic]
      rw [e]
  · refine ⟨c, Finset.mem_univ c, ?_⟩
    have e : (bu_tkPush t c s) c = t c + s := by simp [bu_tkPush]
    rw [e]
    obtain rfl | rfl := hs
    · have h0 := hsign.1 rfl
      omega
    · have h0 := hsign.2 rfl
      omega

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_pull_height](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_pull_height {n : ℕ} {b : Fin n → ℤ} {c : Fin n}
  (hne : b c ≠ 0) : bu_tkH (bu_tkPull b c) < bu_tkH b := by
  apply Finset.sum_lt_sum
  · intro i _
    by_cases hic : i = c
    · rw [hic]
      by_cases hpos : 0 < b c
      · have e : (bu_tkPull b c) c = b c - 1 := by simp [bu_tkPull, hpos]
        rw [e]
        omega
      · have e : (bu_tkPull b c) c = b c + 1 := by simp [bu_tkPull, hpos]
        rw [e]
        omega
    · have e : (bu_tkPull b c) i = b i := by simp [bu_tkPull, hic]
      rw [e]
  · refine ⟨c, Finset.mem_univ c, ?_⟩
    by_cases hpos : 0 < b c
    · have e : (bu_tkPull b c) c = b c - 1 := by simp [bu_tkPull, hpos]
      rw [e]
      omega
    · have e : (bu_tkPull b c) c = b c + 1 := by simp [bu_tkPull, hpos]
      rw [e]
      omega

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_happy_tight_image](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_happy_tight_image {n m : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
  {σ : Finset (Fin n → ℤ)} (h : bu_tkHappy m L σ)
  (hc : σ.card = (bu_tkS σ).card) : σ.image L = bu_tkS σ := by
  have hle : (σ.image L).card ≤ (bu_tkS σ).card := by
    calc (σ.image L).card ≤ σ.card := Finset.card_image_le
      _ = (bu_tkS σ).card := hc
  exact (Finset.eq_of_subset_of_card_le h.2.2 hle).symm

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_happy_loose_neg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_happy_loose_neg {n m : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
  {σ : Finset (Fin n → ℤ)} (h : bu_tkHappy m L σ) (hN : bu_tkNoCompl m L)
  {ℓ : Bool × Fin n} (hℓnot : ℓ ∉ bu_tkS σ) (himg : σ.image L = insert ℓ (bu_tkS σ)) :
  bu_tkNeg ℓ ∉ bu_tkS σ ∧
    ∀ t : Fin n → ℤ, t ∈ σ → (∀ z ∈ σ, bu_tkLe z t) →
      bu_tkS σ = bu_tkSgn t → t ℓ.2 = 0 := by
  have hℓimg : ℓ ∈ σ.image L := by
    rw [himg]
    exact Finset.mem_insert_self ℓ _
  obtain ⟨w, hwσ, hLw⟩ := Finset.mem_image.mp hℓimg
  have hsub : σ ⊆ bu_tkBox n m := h.1
  have hchain := h.2.1
  have hneg : bu_tkNeg ℓ ∉ bu_tkS σ := by
    intro hcon
    have hmem : bu_tkNeg ℓ ∈ σ.image L := h.2.2 hcon
    obtain ⟨w', hw'σ, hLw'⟩ := Finset.mem_image.mp hmem
    obtain hle | hle := hchain.2 w hwσ w' hw'σ
    · exact hN w (hsub hwσ) w' (hsub hw'σ) hle (by rw [hLw', hLw])
    · exact hN w' (hsub hw'σ) w (hsub hwσ) hle (by
      rw [hLw, hLw']
      exact (bu_tkNeg_invol ℓ).symm)
  refine ⟨hneg, ?_⟩
  intro t _ _ hSeq
  obtain ⟨β, j⟩ := ℓ
  have h1 : (β, j) ∉ bu_tkSgn t := by
    rwa [← hSeq]
  have h2 : bu_tkNeg (β, j) ∉ bu_tkSgn t := by
    rwa [← hSeq]
  by_contra hcon
  have hmem : (decide (0 < t j), j) ∈ bu_tkSgn t :=
    bu_mem_tkSgn.mpr ⟨hcon, rfl⟩
  by_cases hβ : decide (0 < t j) = β
  · have he : (decide (0 < t j), j) = (β, j) := Prod.ext_iff.mpr ⟨hβ, rfl⟩
    rw [he] at hmem
    exact h1 hmem
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
    exact h2 hmem

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_tkSgn_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_tkSgn_zero {n : ℕ} : bu_tkSgn (0 : Fin n → ℤ) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro l hl
  rw [bu_mem_tkSgn] at hl
  exact hl.1 rfl

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_happy_erase](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_happy_erase {n m : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
  {τ : Finset (Fin n → ℤ)} {w : Fin n → ℤ} {σ : Finset (Fin n → ℤ)}
  (hsub : τ ⊆ bu_tkBox n m) (hchain : bu_tkChain τ)
  (hσ : σ = τ.erase w) (hne : σ.Nonempty)
  (hcover : bu_tkS τ ⊆ σ.image L) : bu_tkHappy m L σ := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hσ]
    exact Finset.Subset.trans (Finset.erase_subset w τ) hsub
  · refine ⟨hne, ?_⟩
    intro z hz w' hw'
    have hzτ : z ∈ τ := Finset.mem_of_mem_erase (hσ ▸ hz)
    have hwτ : w' ∈ τ := Finset.mem_of_mem_erase (hσ ▸ hw')
    exact hchain.2 z hzτ w' hwτ
  · have hmono : bu_tkS σ ⊆ bu_tkS τ :=
    Finset.sup_mono (hσ ▸ Finset.erase_subset w τ)
    exact Finset.Subset.trans hmono hcover

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_happy_insert](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_happy_insert {n m : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
  {σ : Finset (Fin n → ℤ)} {v : Fin n → ℤ} {τ : Finset (Fin n → ℤ)}
  (hv : v ∈ bu_tkBox n m) (hσ : bu_tkHappy m L σ)
  (hτ : τ = insert v σ) (hchain : bu_tkChain τ)
  (hcover : bu_tkS τ ⊆ σ.image L) : bu_tkHappy m L τ := by
  refine ⟨?_, hchain, ?_⟩
  · rw [hτ]
    exact Finset.insert_subset hv hσ.1
  · have hmono : σ.image L ⊆ τ.image L :=
    Finset.image_subset_image (hτ ▸ Finset.subset_insert v σ)
    exact Finset.Subset.trans hcover hmono

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_tkS_neg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_tkS_neg {n : ℕ} {σ : Finset (Fin n → ℤ)} :
  bu_tkS (σ.image Neg.neg) = (bu_tkS σ).image bu_tkNeg := by
  ext l
  simp only [bu_tkS, Finset.mem_sup, Finset.mem_image]
  constructor
  · rintro ⟨z, ⟨y, hy, rfl⟩, hl⟩
    rw [bu_tkSgn_neg] at hl
    obtain ⟨l', hl', rfl⟩ := Finset.mem_image.mp hl
    exact ⟨l', ⟨y, hy, hl'⟩, rfl⟩
  · rintro ⟨l', ⟨y, hy, hl'⟩, rfl⟩
    refine ⟨-y, ⟨y, hy, rfl⟩, ?_⟩
    rw [bu_tkSgn_neg]
    exact Finset.mem_image.mpr ⟨l', hl', rfl⟩

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_tkNeg_happy](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_tkNeg_happy {n m : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
  (hanti : ∀ z ∈ bu_tkBox n m, (∃ i, |z i| = (m : ℤ)) → L (-z) = bu_tkNeg (L z))
  {σ : Finset (Fin n → ℤ)} (h : bu_tkHappy m L σ) (hb : bu_tkBdry m σ) :
  bu_tkHappy m L (σ.image Neg.neg) := by
  obtain ⟨hsub, hchain, hcover⟩ := h
  have hsubN : σ.image Neg.neg ⊆ bu_tkBox n m := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    exact bu_neg_mem_tkBox (hsub hz)
  have hchainN : bu_tkChain (σ.image Neg.neg) := by
    refine ⟨?_, ?_⟩
    · obtain ⟨z, hz⟩ := hchain.1
      exact ⟨-z, Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩
    · intro y1 hy1 y2 hy2
      obtain ⟨z1, hz1, rfl⟩ := Finset.mem_image.mp hy1
      obtain ⟨z2, hz2, rfl⟩ := Finset.mem_image.mp hy2
      obtain h | h := hchain.2 z1 hz1 z2 hz2
      · exact Or.inl (bu_tkLe_neg.mpr h)
      · exact Or.inr (bu_tkLe_neg.mpr h)
  refine ⟨hsubN, hchainN, ?_⟩
  rw [bu_tkS_neg]
  have hL : (σ.image Neg.neg).image L = (σ.image L).image bu_tkNeg := by
    ext l
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨z, ⟨y, hy, rfl⟩, hl⟩
      refine ⟨L y, ⟨y, hy, rfl⟩, ?_⟩
      rw [← hl]
      exact (hanti y (hsub hy) (hb y hy)).symm
    · rintro ⟨l', ⟨y, hy, rfl⟩, hl⟩
      refine ⟨-y, ⟨y, hy, rfl⟩, ?_⟩
      rwa [hanti y (hsub hy) (hb y hy)]
  rw [hL]
  exact Finset.image_subset_image hcover

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_mem_antiFin](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_mem_antiFin {n : ℕ} {m : ℕ} {σ τ' : Finset (Fin n → ℤ)} :
  τ' ∈ bu_antiFin m σ ↔ bu_tkBdry m σ ∧ τ' = σ.image Neg.neg := by
  by_cases hb : bu_tkBdry m σ <;> simp [bu_antiFin, hb, Finset.mem_singleton]

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_neighbor_image](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_neighbor_image {n m : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
  (hm : 1 ≤ m)
  (hanti : ∀ z ∈ bu_tkBox n m, (∃ i, |z i| = (m : ℤ)) → L (-z) = bu_tkNeg (L z))
  {σ : bu_tkV n m} (hσ : bu_tkHappy m L σ.val) :
  Finset.image Subtype.val ((bu_tkG n m L hm).neighborFinset σ) =
    bu_upFin m L σ.val ∪ bu_downFin L σ.val ∪ bu_antiFin m σ.val := by
  have hsub : σ.val ⊆ bu_tkBox n m := Finset.mem_powerset.mp σ.property
  ext τ'
  simp only [Finset.mem_union]
  constructor
  · intro h
    obtain ⟨τ, hτmem, rfl⟩ := Finset.mem_image.mp h
    have hτadj := (SimpleGraph.mem_neighborFinset (bu_tkG n m L hm) σ τ).mp hτmem
    obtain ⟨hs, ht, hdoor⟩ := hτadj
    obtain ⟨v, hvnot, heq, hcover⟩ | ⟨w, hwnot, heq, hcover⟩ | ⟨hb, heq⟩ := hdoor
    · have hvbox : v ∈ bu_tkBox n m := by
      have hmem : v ∈ τ.val := heq ▸ Finset.mem_insert_self v σ.val
      have hτsub : τ.val ⊆ bu_tkBox n m := Finset.mem_powerset.mp τ.property
      exact hτsub hmem
      have hchain : bu_tkChain (insert v σ.val) := heq ▸ ht.2.1
      have hcover' : bu_tkS (insert v σ.val) ⊆ σ.val.image L := heq ▸ hcover
      have hvmem : v ∈ (bu_tkBox n m).filter
        (fun v => v ∉ σ.val ∧ bu_tkChain (insert v σ.val) ∧
          bu_tkS (insert v σ.val) ⊆ σ.val.image L) := by
        rw [Finset.mem_filter]
        exact ⟨hvbox, hvnot, hchain, hcover'⟩
      have hUmem : insert v σ.val ∈ bu_upFin m L σ.val :=
        Finset.mem_image.mpr ⟨v, hvmem, rfl⟩
      rw [heq]
      exact Or.inl (Or.inl hUmem)
    · have hτe : τ.val = σ.val.erase w := by
      rw [heq, Finset.erase_insert hwnot]
      have hwσ : w ∈ σ.val := heq ▸ Finset.mem_insert_self w τ.val
      have hne : (σ.val.erase w).Nonempty := hτe ▸ ht.2.1.1
      have hcover' : bu_tkS σ.val ⊆ (σ.val.erase w).image L := hτe ▸ hcover
      have hwmem : w ∈ σ.val.filter
        (fun w => (σ.val.erase w).Nonempty ∧ bu_tkS σ.val ⊆ (σ.val.erase w).image L) := by
        rw [Finset.mem_filter]
        exact ⟨hwσ, hne, hcover'⟩
      have hDmem : σ.val.erase w ∈ bu_downFin L σ.val :=
        Finset.mem_image.mpr ⟨w, hwmem, rfl⟩
      rw [hτe]
      exact Or.inl (Or.inr hDmem)
    · have hAmem : σ.val.image Neg.neg ∈ bu_antiFin m σ.val :=
      bu_mem_antiFin.mpr ⟨hb, rfl⟩
      rw [heq]
      exact Or.inr hAmem
  · intro h
    obtain (hU | hD) | hA := h
    · obtain ⟨v, hvF, rfl⟩ := Finset.mem_image.mp hU
      rw [Finset.mem_filter] at hvF
      obtain ⟨hvbox, hvnot, hchain, hcover⟩ := hvF
      have hmem : insert v σ.val ∈ (bu_tkBox n m).powerset := by
        rw [Finset.mem_powerset]
        exact Finset.insert_subset hvbox hsub
      have hadj : bu_tkAdj m L σ.val (insert v σ.val) :=
        ⟨hσ, bu_happy_insert hvbox hσ rfl hchain hcover, Or.inl ⟨v, hvnot, rfl, hcover⟩⟩
      exact Finset.mem_image.mpr ⟨⟨insert v σ.val, hmem⟩,
        (SimpleGraph.mem_neighborFinset (bu_tkG n m L hm) _ _).mpr hadj, rfl⟩
    · obtain ⟨w, hwF, rfl⟩ := Finset.mem_image.mp hD
      rw [Finset.mem_filter] at hwF
      obtain ⟨hwσ, hne, hcover⟩ := hwF
      have hmem : σ.val.erase w ∈ (bu_tkBox n m).powerset := by
        rw [Finset.mem_powerset]
        exact Finset.Subset.trans (Finset.erase_subset w σ.val) hsub
      have hadj : bu_tkAdj m L σ.val (σ.val.erase w) :=
        ⟨hσ, bu_happy_erase hsub hσ.2.1 rfl hne hcover,
          Or.inr (Or.inl ⟨w, Finset.notMem_erase w σ.val,
            (Finset.insert_erase hwσ).symm, hcover⟩)⟩
      exact Finset.mem_image.mpr ⟨⟨σ.val.erase w, hmem⟩,
        (SimpleGraph.mem_neighborFinset (bu_tkG n m L hm) _ _).mpr hadj, rfl⟩
    · rw [bu_mem_antiFin] at hA
      obtain ⟨hb, rfl⟩ := hA
      have hmem : σ.val.image Neg.neg ∈ (bu_tkBox n m).powerset := by
        rw [Finset.mem_powerset]
        intro y hy
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
        exact bu_neg_mem_tkBox (hsub hz)
      have hadj : bu_tkAdj m L σ.val (σ.val.image Neg.neg) :=
        ⟨hσ, bu_tkNeg_happy hanti hσ hb, Or.inr (Or.inr ⟨hb, rfl⟩)⟩
      exact Finset.mem_image.mpr ⟨⟨σ.val.image Neg.neg, hmem⟩,
        (SimpleGraph.mem_neighborFinset (bu_tkG n m L hm) _ _).mpr hadj, rfl⟩

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_neighbor_cards](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_neighbor_cards {n m : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
  {σ : Finset (Fin n → ℤ)} {x : Finset (Fin n → ℤ)}
  (hxU : x ∈ bu_upFin m L σ) : x.card = σ.card + 1 := by
  obtain ⟨v, hvF, hvv⟩ := Finset.mem_image.mp hxU
  rw [Finset.mem_filter] at hvF
  obtain ⟨_, hvnot, _, _⟩ := hvF
  rw [← hvv, Finset.card_insert_of_notMem hvnot]

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_neighbor_cards_down](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_neighbor_cards_down {n : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
  {σ : Finset (Fin n → ℤ)} {x : Finset (Fin n → ℤ)}
  (hxD : x ∈ bu_downFin L σ) : x.card = σ.card - 1 := by
  obtain ⟨w, hwF, hww⟩ := Finset.mem_image.mp hxD
  rw [Finset.mem_filter] at hwF
  obtain ⟨hwσ, _, _⟩ := hwF
  rw [← hww, Finset.card_erase_of_mem hwσ]

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_neighbor_cards_anti](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_neighbor_cards_anti {n m : ℕ}
  {σ : Finset (Fin n → ℤ)} {x : Finset (Fin n → ℤ)}
  (hxA : x ∈ bu_antiFin m σ) : x.card = σ.card := by
  rw [bu_mem_antiFin] at hxA
  obtain ⟨_, rfl⟩ := hxA
  exact Finset.card_image_of_injective _ neg_injective

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_neighbor_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_neighbor_disjoint {n m : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
  {σ : Finset (Fin n → ℤ)} (hcard : 1 ≤ σ.card) :
  Disjoint (bu_upFin m L σ) (bu_downFin L σ) ∧
  Disjoint (bu_upFin m L σ) (bu_antiFin m σ) ∧
  Disjoint (bu_downFin L σ) (bu_antiFin m σ) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro x hxU hxD
    have h1 := bu_neighbor_cards hxU
    have h2 := bu_neighbor_cards_down hxD
    omega
  · rw [Finset.disjoint_left]
    intro x hxU hxA
    have h1 := bu_neighbor_cards hxU
    have h2 := bu_neighbor_cards_anti hxA
    omega
  · rw [Finset.disjoint_left]
    intro x hxD hxA
    have h1 := bu_neighbor_cards_down hxD
    have h2 := bu_neighbor_cards_anti hxA
    omega

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_degree_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_degree_eq {n m : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
  {hm : 1 ≤ m}
  (hanti : ∀ z ∈ bu_tkBox n m, (∃ i, |z i| = (m : ℤ)) → L (-z) = bu_tkNeg (L z))
  {σ : bu_tkV n m} (hσ : bu_tkHappy m L σ.val) :
  (bu_tkG n m L hm).degree σ =
    (bu_upFin m L σ.val).card + (bu_downFin L σ.val).card +
      (bu_antiFin m σ.val).card := by
  have himg := bu_neighbor_image hm hanti hσ
  have hcard : ((bu_tkG n m L hm).neighborFinset σ).card =
    (bu_upFin m L σ.val ∪ bu_downFin L σ.val ∪ bu_antiFin m σ.val).card := by
    rw [← himg]
    have hinj : Function.Injective
      (Subtype.val : bu_tkV n m → Finset (Fin n → ℤ)) := Subtype.val_injective
    exact (Finset.card_image_of_injective _ hinj).symm
  have h1pos : 1 ≤ σ.val.card := Finset.card_pos.mpr hσ.2.1.1
  have hd := bu_neighbor_disjoint (n := n) (m := m) (L := L) (σ := σ.val) h1pos
  have hUDA : ((bu_upFin m L σ.val ∪ bu_downFin L σ.val) ∪ bu_antiFin m σ.val).card =
    (bu_upFin m L σ.val).card + (bu_downFin L σ.val).card +
      (bu_antiFin m σ.val).card := by
    rw [Finset.card_union_of_disjoint
      (Finset.disjoint_union_left.mpr ⟨hd.2.1, hd.2.2⟩),
      Finset.card_union_of_disjoint hd.1]
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hcard, hUDA]

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_anti_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_anti_card {n m : ℕ} {σ : Finset (Fin n → ℤ)} :
  (bu_antiFin m σ).card = if bu_tkBdry m σ then 1 else 0 := by
  by_cases hb : bu_tkBdry m σ <;> simp [bu_antiFin, hb]

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_down_tight](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_down_tight {n : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
  {σ : Finset (Fin n → ℤ)} (hchain : bu_tkChain σ)
  (hc : σ.card = (bu_tkS σ).card) :
  bu_downFin L σ = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro x hx
  obtain ⟨w, hwF, rfl⟩ := Finset.mem_image.mp hx
  rw [Finset.mem_filter] at hwF
  obtain ⟨hwσ, _, hcover⟩ := hwF
  have hpos : 1 ≤ σ.card := Finset.card_pos.mpr hchain.1
  have h1 : (bu_tkS σ).card ≤ ((σ.erase w).image L).card :=
    Finset.card_le_card hcover
  have h2 : ((σ.erase w).image L).card ≤ σ.card - 1 :=
    le_trans Finset.card_image_le (by rw [Finset.card_erase_of_mem hwσ])
  omega

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_label_image_cases](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_label_image_cases {α β : Type*} [DecidableEq β]
  {σ : Finset α} {L : α → β} {S : Finset β}
  (hSsub : S ⊆ σ.image L) (hcard : σ.card = S.card + 1) :
  σ.image L = S ∨ ∃ ℓ, ℓ ∉ S ∧ σ.image L = insert ℓ S := by
  have himg_le : (σ.image L).card ≤ S.card + 1 :=
    le_trans Finset.card_image_le (le_of_eq hcard)
  have hDcard : (σ.image L \ S).card ≤ 1 := by
    have h := Finset.card_sdiff_of_subset hSsub
    omega
  by_cases hempty : σ.image L \ S = ∅
  · left
    exact Finset.Subset.antisymm
      (Finset.sdiff_eq_empty_iff_subset.mp hempty) hSsub
  · right
    have hne : (σ.image L \ S).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hempty
    have hcard1 : (σ.image L \ S).card = 1 := by
      have hpos : 0 < (σ.image L \ S).card := Finset.card_pos.mpr hne
      omega
    obtain ⟨ℓ, hℓ⟩ := Finset.card_eq_one.mp hcard1
    have hℓmem : ℓ ∈ σ.image L \ S := by
      rw [hℓ]
      exact Finset.mem_singleton_self ℓ
    have hℓimg : ℓ ∈ σ.image L := (Finset.mem_sdiff.mp hℓmem).1
    have hℓnot : ℓ ∉ S := (Finset.mem_sdiff.mp hℓmem).2
    refine ⟨ℓ, hℓnot, ?_⟩
    ext y
    constructor
    · intro hy
      by_cases hyS : y ∈ S
      · exact Finset.mem_insert_of_mem hyS
      · have hmem : y ∈ σ.image L \ S := Finset.mem_sdiff.mpr ⟨hy, hyS⟩
        rw [hℓ] at hmem
        have hyℓ : y = ℓ := Finset.mem_singleton.mp hmem
        rw [hyℓ]
        exact Finset.mem_insert_self ℓ S
    · intro hy
      rw [Finset.mem_insert] at hy
      obtain rfl | hyS := hy
      · exact hℓimg
      · exact hSsub hyS

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_label_removal_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_label_removal_two {α β : Type*} [DecidableEq α] [DecidableEq β]
  {σ : Finset α} {L : α → β} {S : Finset β}
  (hcard : σ.card = S.card + 1) (himg : σ.image L = S) :
  (σ.filter (fun w => S ⊆ (σ.erase w).image L)).card = 2 := by
  have hlt : S.card < σ.card := by omega
  have hmaps : Set.MapsTo L (↑σ : Set α) (↑S : Set β) := by
    intro x hx
    have hx' : x ∈ σ := Finset.mem_coe.mp hx
    have hL : L x ∈ σ.image L := Finset.mem_image.mpr ⟨x, hx', rfl⟩
    rw [himg] at hL
    exact Finset.mem_coe.mpr hL
  obtain ⟨x, hxσ, y, hyσ, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hmaps
  have hDn : ∀ w : α, w ∈ σ.filter (fun w => S ⊆ (σ.erase w).image L) ↔ w = x ∨ w = y := by
    intro w
    constructor
    · intro hw
      rw [Finset.mem_filter] at hw
      obtain ⟨hwσ, hsubw⟩ := hw
      by_cases hwx : w = x
      · exact Or.inl hwx
      · by_cases hwy : w = y
        · exact Or.inr hwy
        · exfalso
          have hxE : x ∈ σ.erase w :=
            Finset.mem_erase.mpr ⟨fun h => hwx h.symm, hxσ⟩
          have hyE : y ∈ σ.erase w :=
            Finset.mem_erase.mpr ⟨fun h => hwy h.symm, hyσ⟩
          have hcardE : (σ.erase w).card = S.card := by
            rw [Finset.card_erase_of_mem hwσ]
            omega
          have heqS : (σ.erase w).image L = S := by
            have hle : ((σ.erase w).image L).card ≤ S.card := by
              calc ((σ.erase w).image L).card ≤ (σ.erase w).card :=
                Finset.card_image_le
                _ = S.card := hcardE
            exact (Finset.eq_of_subset_of_card_le hsubw hle).symm
          have hinj : Set.InjOn L (↑(σ.erase w) : Set α) := by
            have hc : ((σ.erase w).image L).card = (σ.erase w).card := by
              rw [heqS, hcardE]
            exact Finset.card_image_iff.mp hc
          have hcon : x = y := hinj (Finset.mem_coe.mpr hxE)
            (Finset.mem_coe.mpr hyE) heq
          exact hne hcon
    · intro hw
      have hSsub : S ⊆ σ.image L := by rw [himg]
      obtain hwx | hwy := hw
      · rw [hwx, Finset.mem_filter]
        refine ⟨hxσ, ?_⟩
        intro s hs
        have hsimg : s ∈ σ.image L := hSsub hs
        obtain ⟨z, hzσ, hLz⟩ := Finset.mem_image.mp hsimg
        by_cases hzx : z = x
        · rw [hzx] at hLz
          have hLy : L y = s := heq.symm.trans hLz
          exact Finset.mem_image.mpr ⟨y,
            Finset.mem_erase.mpr ⟨Ne.symm hne, hyσ⟩, hLy⟩
        · exact Finset.mem_image.mpr ⟨z,
          Finset.mem_erase.mpr ⟨hzx, hzσ⟩, hLz⟩
      · rw [hwy, Finset.mem_filter]
        refine ⟨hyσ, ?_⟩
        intro s hs
        have hsimg : s ∈ σ.image L := hSsub hs
        obtain ⟨z, hzσ, hLz⟩ := Finset.mem_image.mp hsimg
        by_cases hzy : z = y
        · rw [hzy] at hLz
          have hLx : L x = s := heq.trans hLz
          exact Finset.mem_image.mpr ⟨x,
            Finset.mem_erase.mpr ⟨hne, hxσ⟩, hLx⟩
        · exact Finset.mem_image.mpr ⟨z,
          Finset.mem_erase.mpr ⟨hzy, hzσ⟩, hLz⟩
  have hEq : σ.filter (fun w => S ⊆ (σ.erase w).image L) = {x, y} := by
    ext w
    rw [hDn, Finset.mem_insert, Finset.mem_singleton]
  rw [hEq, Finset.card_pair_eq_two_iff.mpr hne]

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_label_removal_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_label_removal_one {α β : Type*} [DecidableEq α] [DecidableEq β]
  {σ : Finset α} {L : α → β} {S : Finset β} {ℓ : β}
  (hcard : σ.card = S.card + 1) (hℓ : ℓ ∉ S) (himg : σ.image L = insert ℓ S) :
  σ.filter (fun w => S ⊆ (σ.erase w).image L) =
    σ.filter (fun w => L w = ℓ) ∧
  (σ.filter (fun w => S ⊆ (σ.erase w).image L)).card = 1 := by
  have hcardI : (insert ℓ S).card = S.card + 1 := Finset.card_insert_of_notMem hℓ
  have hinj : Set.InjOn L (↑σ : Set α) := by
    have hc : (σ.image L).card = σ.card := by rw [himg, hcardI, ← hcard]
    exact Finset.card_image_iff.mp hc
  have hEq : σ.filter (fun w => S ⊆ (σ.erase w).image L) =
    σ.filter (fun w => L w = ℓ) := by
    ext w
    by_cases hwσ : w ∈ σ
    · rw [Finset.mem_filter, Finset.mem_filter]
      constructor
      · intro h
        obtain ⟨_, hsubw⟩ := h
        by_contra hcon
        have hwimg : L w ∈ σ.image L :=
          Finset.mem_image.mpr ⟨w, hwσ, rfl⟩
        rw [himg] at hwimg
        rw [Finset.mem_insert] at hwimg
        obtain hℓw | hSw := hwimg
        · exact hcon ⟨hwσ, hℓw⟩
        · have hnot : L w ∉ (σ.erase w).image L := by
          intro hcon2
          obtain ⟨z, hzE, hLz⟩ := Finset.mem_image.mp hcon2
          have hzσ : z ∈ σ := Finset.mem_of_mem_erase hzE
          have hzw : z ≠ w := Finset.ne_of_mem_erase hzE
          have hzw' : z = w := hinj (Finset.mem_coe.mpr hzσ)
            (Finset.mem_coe.mpr hwσ) hLz
          exact hzw hzw'
          exact hnot (hsubw hSw)
      · intro h
        obtain ⟨hwσ', hLw⟩ := h
        refine ⟨hwσ', ?_⟩
        intro s hs
        have hSsub : S ⊆ σ.image L := by rw [himg]; exact Finset.subset_insert ℓ S
        have hsimg : s ∈ σ.image L := hSsub hs
        obtain ⟨z, hzσ, hLz⟩ := Finset.mem_image.mp hsimg
        have hzw : z ≠ w := by
          intro hcon
          rw [hcon] at hLz
          rw [← hLz] at hs
          rw [hLw] at hs
          exact hℓ hs
        exact Finset.mem_image.mpr ⟨z, Finset.mem_erase.mpr ⟨hzw, hzσ⟩, hLz⟩
    · rw [Finset.mem_filter, Finset.mem_filter]
      simp [hwσ]
  refine ⟨hEq, ?_⟩
  rw [hEq]
  obtain ⟨w0, hw0σ, hL0⟩ : ∃ w0 ∈ σ, L w0 = ℓ := by
    have hmem : ℓ ∈ σ.image L := by rw [himg]; exact Finset.mem_insert_self ℓ S
    obtain ⟨w0, hw0σ, hL0⟩ := Finset.mem_image.mp hmem
    exact ⟨w0, hw0σ, hL0⟩
  have hsingle : σ.filter (fun w => L w = ℓ) = {w0} := by
    ext w
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro h
      obtain ⟨hwσ, hLw⟩ := h
      have he : w = w0 := hinj (Finset.mem_coe.mpr hwσ)
        (Finset.mem_coe.mpr hw0σ) (by rw [hLw, hL0])
      exact he
    · intro h
      rw [h]
      exact ⟨hw0σ, hL0⟩
  rw [hsingle, Finset.card_singleton]

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_insert_inj_of_notMem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_insert_inj_of_notMem {n : ℕ} {σ : Finset (Fin n → ℤ)}
  {v₁ v₂ : Fin n → ℤ} (h₁ : v₁ ∉ σ)
  (he : insert v₁ σ = insert v₂ σ) : v₁ = v₂ := by
  have hm : v₁ ∈ insert v₂ σ := he ▸ Finset.mem_insert_self v₁ σ
  rw [Finset.mem_insert] at hm
  obtain h | h := hm
  · exact h
  · exact absurd h h₁

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_erase_inj](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_erase_inj {n : ℕ} {σ : Finset (Fin n → ℤ)}
  {w₁ w₂ : Fin n → ℤ} (h₁ : w₁ ∈ σ)
  (he : σ.erase w₁ = σ.erase w₂) : w₁ = w₂ := by
  by_contra hne
  have hm1 : w₁ ∈ σ.erase w₂ := Finset.mem_erase.mpr ⟨hne, h₁⟩
  have hm2 : w₁ ∈ σ.erase w₁ := he.symm ▸ hm1
  exact Finset.notMem_erase w₁ σ hm2

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_upFin_tight_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_upFin_tight_card {n m : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
  {σ : Finset (Fin n → ℤ)} (himg : σ.image L = bu_tkS σ) :
  (bu_upFin m L σ).card = (bu_tkUp m σ).card := by
  have hfilter : ((bu_tkBox n m).filter fun v =>
    v ∉ σ ∧ bu_tkChain (insert v σ) ∧ bu_tkS (insert v σ) ⊆ σ.image L) =
    ((bu_tkBox n m).filter fun v =>
      v ∉ σ ∧ bu_tkChain (insert v σ) ∧ bu_tkS (insert v σ) ⊆ bu_tkS σ) := by
    rw [himg]
  have hinj : Set.InjOn (fun v => insert v σ)
    (↑((bu_tkBox n m).filter fun v =>
      v ∉ σ ∧ bu_tkChain (insert v σ) ∧ bu_tkS (insert v σ) ⊆ bu_tkS σ) :
      Set (Fin n → ℤ)) := by
    intro v₁ hv₁ v₂ hv₂ he
    have h₁ : v₁ ∉ σ := (Finset.mem_filter.mp (Finset.mem_coe.mp hv₁)).2.1
    exact bu_insert_inj_of_notMem h₁ he
  rw [bu_upFin, hfilter, bu_tkUp, Finset.card_image_of_injOn hinj]

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_singleton_not_bdry](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_singleton_not_bdry {n m : ℕ} (hm : 1 ≤ m) :
  ¬ bu_tkBdry m ({0} : Finset (Fin n → ℤ)) := by
  intro hbd
  obtain ⟨i, hi⟩ := hbd 0 (Finset.mem_singleton_self 0)
  simp at hi
  omega

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_down_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_down_singleton {n : ℕ} {L : (Fin n → ℤ) → Bool × Fin n} :
  bu_downFin L ({0} : Finset (Fin n → ℤ)) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro x hx
  obtain ⟨w, hwF, _⟩ := Finset.mem_image.mp hx
  rw [Finset.mem_filter] at hwF
  obtain ⟨hwσ, hne, _⟩ := hwF
  rw [Finset.mem_singleton] at hwσ
  subst hwσ
  simp at hne

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_downFin_card_of_two_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_downFin_card_of_two_le {n : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
  {σ : Finset (Fin n → ℤ)} (h2 : 2 ≤ σ.card) :
  (bu_downFin L σ).card =
    (σ.filter fun w => bu_tkS σ ⊆ (σ.erase w).image L).card := by
  have hfilter : (σ.filter fun w =>
    (σ.erase w).Nonempty ∧ bu_tkS σ ⊆ (σ.erase w).image L) =
    (σ.filter fun w => bu_tkS σ ⊆ (σ.erase w).image L) := by
    ext w
    rw [Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨hwσ, _, hcover⟩
      exact ⟨hwσ, hcover⟩
    · rintro ⟨hwσ, hcover⟩
      refine ⟨hwσ, ?_, hcover⟩
      rw [← Finset.card_pos]
      rw [Finset.card_erase_of_mem hwσ]
      omega
  have hinj : Set.InjOn (fun w => σ.erase w)
    (↑(σ.filter fun w => bu_tkS σ ⊆ (σ.erase w).image L) : Set (Fin n → ℤ)) := by
    intro w₁ hw₁ w₂ hw₂ he
    have h₁ : w₁ ∈ σ := (Finset.mem_filter.mp (Finset.mem_coe.mp hw₁)).1
    exact bu_erase_inj h₁ he
  rw [bu_downFin, hfilter, Finset.card_image_of_injOn hinj]

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_anti_card_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_anti_card_pos {n m : ℕ} {σ : Finset (Fin n → ℤ)}
  (hb : bu_tkBdry m σ) : (bu_antiFin m σ).card = 1 := by
  simp [bu_anti_card, hb]

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_anti_card_neg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_anti_card_neg {n m : ℕ} {σ : Finset (Fin n → ℤ)}
  (hb : ¬ bu_tkBdry m σ) : (bu_antiFin m σ).card = 0 := by
  simp [bu_anti_card, hb]

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_degree_not_happy](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma bu_degree_not_happy {n m : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
  {hm : 1 ≤ m} {σ : bu_tkV n m} (hnh : ¬ bu_tkHappy m L σ.val) :
  (bu_tkG n m L hm).degree σ = 0 := by
  have hempty : (bu_tkG n m L hm).neighborFinset σ = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro τ hτ
    rw [SimpleGraph.mem_neighborFinset] at hτ
    exact hnh hτ.1
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hempty, Finset.card_empty]

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[buV_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma buV_continuous {n : ℕ} : Continuous (buV n) := by
  have hcons : Continuous
    (fun x : Fin n → ℝ => (Fin.cons ((1 : ℝ) - ‖x‖) x : Fin (n + 1) → ℝ)) :=
    Continuous.finCons (A := fun _ => ℝ)
      (continuous_const.sub continuous_norm : Continuous fun x : Fin n → ℝ => (1 : ℝ) - ‖x‖)
      continuous_id
  have hto : Continuous
    (fun y : Fin (n + 1) → ℝ => (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin (n + 1)))) := by
    fun_prop
  unfold buV
  exact hto.comp hcons

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[buV_neg_of_norm_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma buV_neg_of_norm_one {n : ℕ} {x : Fin n → ℝ} (h : ‖x‖ = 1) :
  buV n (-x) = -buV n x := by
  have hhead : (1 : ℝ) - ‖-x‖ = -((1 : ℝ) - ‖x‖) := by
    rw [norm_neg, h]
    norm_num
  have hcons : (Fin.cons ((1 : ℝ) - ‖-x‖) (-x) : Fin (n + 1) → ℝ) =
    -(Fin.cons ((1 : ℝ) - ‖x‖) x : Fin (n + 1) → ℝ) := by
    funext j
    refine Fin.cases ?_ ?_ j
    · simp only [Fin.cons_zero, Pi.neg_apply]
      exact hhead
    · intro i
      simp only [Fin.cons_succ, Pi.neg_apply]
  simp only [buV, hcons, WithLp.toLp_neg]

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[buLift_neg_of_norm_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma buLift_neg_of_norm_one {n : ℕ} {x : Fin n → ℝ} (h : ‖x‖ = 1) :
  buLift n (-x) = -buLift n x := by
  apply Subtype.ext
  rw [coe_neg_sphere]
  change ‖buV n (-x)‖⁻¹ • buV n (-x) = -(‖buV n x‖⁻¹ • buV n x)
  rw [buV_neg_of_norm_one h, norm_neg, smul_neg]

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[buG_neg_of_norm_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma buG_neg_of_norm_one {n : ℕ}
  {F : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 → EuclideanSpace ℝ (Fin n)}
  {x : Fin n → ℝ} (h : ‖x‖ = 1) : buG n F (-x) = -buG n F x := by
  have hL : buLift n (-x) = -buLift n x := buLift_neg_of_norm_one h
  funext i
  change (F (buLift n (-x)) - F (-buLift n (-x))).ofLp i =
    -((F (buLift n x) - F (-buLift n x)).ofLp i)
  rw [hL, neg_neg, ← neg_sub, WithLp.ofLp_neg, Pi.neg_apply]

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[buG_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma buG_zero {n : ℕ}
  {F : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 → EuclideanSpace ℝ (Fin n)}
  {x : Fin n → ℝ} (h : buG n F x = 0) :
  F (buLift n x) = F (-buLift n x) := by
  have hsub : F (buLift n x) - F (-buLift n x) = 0 := by
    apply PiLp.ext
    intro i
    exact congrFun h i
  exact sub_eq_zero.mp hsub

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[buIdx_max](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma buIdx_max {n : ℕ} [Nonempty (Fin n)] (a : Fin n → ℝ) (j : Fin n) :
  a j ≤ a (buIdx a) :=
  (Classical.choose_spec
    (Finset.exists_max_image Finset.univ a Finset.univ_nonempty)).2 j
    (Finset.mem_univ j)

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[buI_max](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma buI_max {n : ℕ} [Nonempty (Fin n)] (v : Fin n → ℝ) (j : Fin n) :
  |v j| ≤ |v (buI v)| :=
  buIdx_max (fun i => |v i|) j

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[buI_norm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma buI_norm {n : ℕ} [Nonempty (Fin n)] (v : Fin n → ℝ) :
  ‖v‖ = |v (buI v)| := by
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg (abs_nonneg _)]
    intro i
    rw [Real.norm_eq_abs]
    exact buI_max v i
  · rw [← Real.norm_eq_abs]
    exact norm_le_pi_norm v (buI v)

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[buI_neg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma buI_neg {n : ℕ} [Nonempty (Fin n)] (v : Fin n → ℝ) :
  buI (-v) = buI v := by
  have heq : (fun i => |(-v) i|) = (fun i => |v i|) := by
    funext i
    rw [Pi.neg_apply, abs_neg]
  unfold buI
  rw [heq]

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[buI_ne_zero_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma buI_ne_zero_of_ne {n : ℕ} [Nonempty (Fin n)] {v : Fin n → ℝ}
  (hv : v ≠ 0) : v (buI v) ≠ 0 := by
  intro hcon
  apply hv
  funext j
  have hle : |v j| ≤ 0 := by
    have h := buI_max v j
    rwa [hcon, abs_zero] at h
  have hj : |v j| = 0 := le_antisymm hle (abs_nonneg _)
  exact abs_eq_zero.mp hj

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[buLab_neg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma buLab_neg {n : ℕ} [Nonempty (Fin n)] {v : Fin n → ℝ}
  (hv : v ≠ 0) : buLab (-v) = bu_tkNeg (buLab v) := by
  have hI : buI (-v) = buI v := buI_neg v
  have hne : v (buI v) ≠ 0 := buI_ne_zero_of_ne hv
  simp only [buLab, hI, bu_tkNeg, Pi.neg_apply, Prod.mk.injEq]
  refine ⟨?_, trivial⟩
  by_cases hpos : 0 < v (buI v)
  · rw [decide_eq_true hpos]
    have hneg : ¬ (0 : ℝ) < -(v (buI v)) :=
      not_lt.mpr (neg_nonpos.mpr hpos.le)
    rw [decide_eq_false hneg]
    rfl
  · have hlt : v (buI v) < 0 := lt_of_le_of_ne (not_lt.mp hpos) hne
    rw [decide_eq_false hpos, decide_eq_true (neg_pos.mpr hlt)]
    rfl

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[bu_eps_delta](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
and uniformly continuous there. -/
private lemma bu_eps_delta {n : ℕ} {g : (Fin n → ℝ) → (Fin n → ℝ)}
  (hg : Continuous g)
  (hne : ∀ x ∈ Metric.closedBall (0 : Fin n → ℝ) 1, g x ≠ 0) :
  ∃ ε : ℝ, 0 < ε ∧ (∀ x ∈ Metric.closedBall (0 : Fin n → ℝ) 1, ε ≤ ‖g x‖) ∧
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Metric.closedBall (0 : Fin n → ℝ) 1,
      ∀ y ∈ Metric.closedBall (0 : Fin n → ℝ) 1,
        dist x y < δ → dist (g x) (g y) < ε := by
  have hcompact : IsCompact (Metric.closedBall (0 : Fin n → ℝ) 1) :=
    isCompact_closedBall _ _
  have h0mem : (0 : Fin n → ℝ) ∈ Metric.closedBall (0 : Fin n → ℝ) 1 := by
    rw [Metric.mem_closedBall, dist_self]
    norm_num
  obtain ⟨x0, hx0, hmin⟩ :=
    hcompact.exists_isMinOn ⟨0, h0mem⟩ hg.norm.continuousOn
  have hpos : 0 < ‖g x0‖ := norm_pos_iff.mpr (hne x0 hx0)
  refine ⟨‖g x0‖, hpos, (fun x hx => hmin hx), ?_⟩
  obtain ⟨δ, hδpos, hδ⟩ := Metric.uniformContinuousOn_iff.mp
    (hcompact.uniformContinuousOn_of_continuous hg.continuousOn) _ hpos
  exact ⟨δ, hδpos, hδ⟩

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[buPt_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma buPt_apply {n : ℕ} {m : ℕ} {z : Fin n → ℤ} {i : Fin n} :
  (buPt m z) i = ((z i : ℤ) : ℝ) / (m : ℝ) :=
  rfl

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[buPt_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma buPt_mem {n m : ℕ} (hmR : (0 : ℝ) < (m : ℝ)) {z : Fin n → ℤ}
  (hz : z ∈ bu_tkBox n m) : buPt m z ∈ Metric.closedBall (0 : Fin n → ℝ) 1 := by
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  have hi : |z i| ≤ (m : ℤ) := (bu_mem_tkBox.mp hz) i
  have hiR : ((((|z i| : ℤ))) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hi
  rw [Real.norm_eq_abs, buPt_apply, abs_div, abs_of_pos hmR, ← Int.cast_abs,
    div_le_one hmR]
  exact hiR

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[buPt_norm_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma buPt_norm_one {n m : ℕ} (hmR : (0 : ℝ) < (m : ℝ)) {z : Fin n → ℤ}
  (hz : z ∈ bu_tkBox n m) (hbd : ∃ i, |z i| = (m : ℤ)) : ‖buPt m z‖ = 1 := by
  obtain ⟨i, hi⟩ := hbd
  have hiR : ((((|z i| : ℤ))) : ℝ) = (m : ℝ) := by exact_mod_cast hi
  have hle : ‖buPt m z‖ ≤ 1 := mem_closedBall_zero_iff.mp (buPt_mem hmR hz)
  have hge : (1 : ℝ) ≤ ‖buPt m z‖ := by
    have h1 := norm_le_pi_norm (buPt m z) i
    rw [Real.norm_eq_abs, buPt_apply, abs_div, abs_of_pos hmR, ← Int.cast_abs, hiR,
      div_self hmR.ne'] at h1
    exact h1
  exact le_antisymm hle hge

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[buPt_neg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma buPt_neg {n m : ℕ} (z : Fin n → ℤ) :
  buPt m (-z) = -buPt m z := by
  funext i
  simp only [buPt_apply, Pi.neg_apply, Int.cast_neg, neg_div]

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[buPt_dist](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma buPt_dist {n m : ℕ} (hmR : (0 : ℝ) < (m : ℝ)) {z w : Fin n → ℤ}
  (hle : bu_tkLe z w) : dist (buPt m z) (buPt m w) ≤ 1 / (m : ℝ) := by
  have h1m : (0 : ℝ) ≤ 1 / (m : ℝ) := le_of_lt (one_div_pos.mpr hmR)
  rw [dist_eq_norm, pi_norm_le_iff_of_nonneg h1m]
  intro i
  have hzw : |z i - w i| ≤ 1 := by
    have h := hle i
    obtain h | ⟨h1, h2⟩ | ⟨h1, h2⟩ := h
    · rw [h, sub_self, abs_zero]; norm_num
    · rw [h2]; norm_num
    · rw [h2]; norm_num
  have h1 : (((((|z i - w i| : ℤ)))) : ℝ) ≤ 1 := by exact_mod_cast hzw
  have e : ((buPt m z - buPt m w) i) = (((((z i - w i : ℤ)))) : ℝ) / (m : ℝ) := by
    rw [Pi.sub_apply, buPt_apply, buPt_apply, ← sub_div, ← Int.cast_sub]
  rw [Real.norm_eq_abs, e, abs_div, abs_of_pos hmR, ← Int.cast_abs,
    div_le_div_iff_of_pos_right hmR]
  exact h1

end MathlibExt.Topology.Homotopy.BorsukUlamWanted

/--
[borsukUlam](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Homotopy/BorsukUlam.lean)
-/
@[path]
private lemma borsukUlam_eq
  {n : ℕ}
  {f : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 → EuclideanSpace ℝ (Fin n)}
-- given
  (hf : Continuous f) :
-- imply
  ∃ x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, f x = f (-x) := by
-- proof
  apply MathlibExt.Topology.Homotopy.BorsukUlamWanted.borsukUlam f hf


-- created on 2026-10-20
-- updated on 2026-10-26
