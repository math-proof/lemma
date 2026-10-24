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

namespace MathlibExt.Topology.Homotopy.BorsukUlamWanted

open Metric

/-! ## Tucker grid basic definitions and order lemmas -/

/-- Grid box: `z ∈ bu_tkBox n m` iff `|z i| ≤ m` for all `i`. -/
private def bu_tkBox (n m : ℕ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset fun _ : Fin n => Finset.Icc (-(m : ℤ)) (m : ℤ)

/-- Freund–Todd step order: `w` is `z` with some coordinates pushed one unit away from `0`. -/
private def bu_tkLe {n : ℕ} (z w : Fin n → ℤ) : Prop :=
  ∀ i, w i = z i ∨ (0 ≤ z i ∧ w i = z i + 1) ∨ (z i ≤ 0 ∧ w i = z i - 1)

/-- Chains: nonempty sets of pairwise comparable points (the simplices). -/
private def bu_tkChain {n : ℕ} (σ : Finset (Fin n → ℤ)) : Prop :=
  σ.Nonempty ∧ ∀ z ∈ σ, ∀ w ∈ σ, bu_tkLe z w ∨ bu_tkLe w z

/-- Label negation: flips the sign, keeps the index. -/
private def bu_tkNeg {n : ℕ} (l : Bool × Fin n) : Bool × Fin n := (!l.1, l.2)

/-- Sign set of a grid point: `(true, i)` for `z i > 0`, `(false, i)` for `z i < 0`. -/
private def bu_tkSgn {n : ℕ} (z : Fin n → ℤ) : Finset (Bool × Fin n) :=
  (Finset.univ.filter fun i => z i ≠ 0).image fun i => (decide (0 < z i), i)

/-- Sign set of a chain (the sign set of its top vertex). -/
private def bu_tkS {n : ℕ} (σ : Finset (Fin n → ℤ)) : Finset (Bool × Fin n) :=
  σ.sup bu_tkSgn

/-- Boundary: every point of `σ` has some coordinate of absolute value `m`. -/
private def bu_tkBdry {n : ℕ} (m : ℕ) (σ : Finset (Fin n → ℤ)) : Prop :=
  ∀ z ∈ σ, ∃ i, |z i| = (m : ℤ)

/-- Happy chain: inside the box, a chain, and every sign is witnessed by a label. -/
private def bu_tkHappy {n : ℕ} (m : ℕ) (L : (Fin n → ℤ) → Bool × Fin n)
    (σ : Finset (Fin n → ℤ)) : Prop :=
  σ ⊆ bu_tkBox n m ∧ bu_tkChain σ ∧ bu_tkS σ ⊆ σ.image L

/-- No complementary edge: no comparable pair in the box carries opposite labels. -/
private def bu_tkNoCompl {n : ℕ} (m : ℕ) (L : (Fin n → ℤ) → Bool × Fin n) : Prop :=
  ∀ z ∈ bu_tkBox n m, ∀ w ∈ bu_tkBox n m, bu_tkLe z w → L w ≠ bu_tkNeg (L z)

/-- Height: sum of absolute values. Strictly increases along `bu_tkLe`. -/
private def bu_tkH {n : ℕ} (z : Fin n → ℤ) : ℕ := ∑ i, (z i).natAbs

private theorem bu_tkLe_refl {n : ℕ} (z : Fin n → ℤ) : bu_tkLe z z := fun _ =>
  Or.inl rfl

private theorem bu_tkLe_natAbs {n : ℕ} {z w : Fin n → ℤ} (h : bu_tkLe z w)
    (i : Fin n) : (z i).natAbs ≤ (w i).natAbs := by
  rcases h i with hcon | ⟨h0, hw⟩ | ⟨h0, hw⟩ <;> omega

private theorem bu_tkLe_height {n : ℕ} {z w : Fin n → ℤ} (h : bu_tkLe z w) :
    bu_tkH z ≤ bu_tkH w :=
  Finset.sum_le_sum fun i _ => bu_tkLe_natAbs h i

private theorem bu_tkLe_height_lt {n : ℕ} {z w : Fin n → ℤ} (h : bu_tkLe z w)
    (hne : z ≠ w) : bu_tkH z < bu_tkH w := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  refine Finset.sum_lt_sum (fun j _ => bu_tkLe_natAbs h j) ⟨i, Finset.mem_univ i, ?_⟩
  rcases h i with hcon | ⟨h0, hw⟩ | ⟨h0, hw⟩
  · exact (hi hcon.symm).elim
  · simp only [hw]; omega
  · simp only [hw]; omega

private theorem bu_tkLe_of_height_eq {n : ℕ} {z w : Fin n → ℤ} (h : bu_tkLe z w)
    (he : bu_tkH z = bu_tkH w) : z = w := by
  by_contra hne
  exact absurd he (ne_of_lt (bu_tkLe_height_lt h hne))

private theorem bu_tkLe_antisymm {n : ℕ} {z w : Fin n → ℤ} (h1 : bu_tkLe z w)
    (h2 : bu_tkLe w z) : z = w := by
  by_contra hne
  have hlt := bu_tkLe_height_lt h1 hne
  have hle := bu_tkLe_height h2
  omega

private theorem bu_tkSgn_mono {n : ℕ} {z w : Fin n → ℤ} (h : bu_tkLe z w) :
    bu_tkSgn z ⊆ bu_tkSgn w := by
  intro l hl
  have hl' : z l.2 ≠ 0 ∧ l.1 = decide (0 < z l.2) := bu_mem_tkSgn.mp hl
  obtain ⟨hz0, hbl⟩ := hl'
  have hw0 : w l.2 ≠ 0 := by
    have hle := bu_tkLe_natAbs h l.2
    omega
  have hsign : (0 < w l.2) ↔ (0 < z l.2) := by
    rcases h l.2 with heq | ⟨h0, hw⟩ | ⟨h0, hw⟩
    · rw [heq]
    · constructor <;> intro <;> omega
    · constructor <;> intro <;> omega
  have hdec : decide (0 < w l.2) = decide (0 < z l.2) := by
    simp only [hsign]
  have hbl' : l.1 = decide (0 < w l.2) := by rw [hdec]; exact hbl
  exact bu_mem_tkSgn.mpr ⟨hw0, hbl'⟩

/-- Quasi-transitivity: two steps collapse when the endpoints are comparable. -/
private theorem bu_tkLe_trans_of_comparable {n : ℕ} {z w u : Fin n → ℤ}
    (h1 : bu_tkLe z w) (h2 : bu_tkLe w u) (hc : bu_tkLe z u ∨ bu_tkLe u z) :
    bu_tkLe z u := by
  rcases hc with h | h
  · exact h
  · have e1 := bu_tkLe_height h1
    have e2 := bu_tkLe_height h2
    have e3 := bu_tkLe_height h
    have hzw : z = w := bu_tkLe_of_height_eq h1 (by omega)
    subst hzw
    exact h2

/-! ## Chains have a bottom and a top -/

private theorem bu_chain_bot_top {n : ℕ} {σ : Finset (Fin n → ℤ)}
    (hσ : bu_tkChain σ) :
    ∃ b ∈ σ, ∃ t ∈ σ, (∀ z ∈ σ, bu_tkLe b z) ∧ (∀ z ∈ σ, bu_tkLe z t) ∧
      bu_tkS σ = bu_tkSgn t := by
  obtain ⟨hne, hcomp⟩ := hσ
  obtain ⟨b, hbσ, hbmin⟩ := Finset.exists_min_image σ bu_tkH hne
  obtain ⟨t, htσ, htmax⟩ := Finset.exists_max_image σ bu_tkH hne
  have hbot : ∀ z ∈ σ, bu_tkLe b z := by
    intro z hz
    rcases hcomp b hbσ z hz with h | h
    · exact h
    · have he : bu_tkH z = bu_tkH b :=
        le_antisymm (bu_tkLe_height h) (hbmin z hz)
      have e : z = b := bu_tkLe_of_height_eq h he
      rw [e]
      exact bu_tkLe_refl b
  have htop : ∀ z ∈ σ, bu_tkLe z t := by
    intro z hz
    rcases hcomp z hz t htσ with h | h
    · exact h
    · have he : bu_tkH t = bu_tkH z :=
        le_antisymm (bu_tkLe_height h) (htmax z hz)
      have e : t = z := bu_tkLe_of_height_eq h he
      rw [e]
      exact bu_tkLe_refl z
  refine ⟨b, hbσ, t, htσ, hbot, htop, ?_⟩
  apply le_antisymm
  · simp only [bu_tkS, Finset.sup_le_iff]
    intro z hz
    exact bu_tkSgn_mono (htop z hz)
  · exact Finset.le_sup htσ

/-- Within a chain, the order is the height order. -/
private theorem bu_chain_height_iff {n : ℕ} {σ : Finset (Fin n → ℤ)}
    (hσ : bu_tkChain σ) {z w : Fin n → ℤ} (hz : z ∈ σ) (hw : w ∈ σ) :
    bu_tkLe z w ↔ bu_tkH z ≤ bu_tkH w := by
  constructor
  · exact bu_tkLe_height
  · intro hle
    rcases hσ.2 z hz w hw with h | h
    · exact h
    · have he : bu_tkH z = bu_tkH w := le_antisymm hle (bu_tkLe_height h)
      have e : z = w := (bu_tkLe_of_height_eq h he.symm).symm
      rw [e]
      exact bu_tkLe_refl w

/-- The height is injective on a chain. -/
private theorem bu_chain_height_inj {n : ℕ} {σ : Finset (Fin n → ℤ)}
    (hσ : bu_tkChain σ) {z w : Fin n → ℤ} (hz : z ∈ σ) (hw : w ∈ σ)
    (he : bu_tkH z = bu_tkH w) : z = w := by
  rcases hσ.2 z hz w hw with h | h
  · exact bu_tkLe_of_height_eq h he
  · exact (bu_tkLe_of_height_eq h he.symm).symm

/-! ## Moved-set normal form -/

/-- Moved set: coordinates where `z` differs from the bottom `b`. -/
private def bu_tkMv {n : ℕ} (b z : Fin n → ℤ) : Finset (Fin n) :=
  Finset.univ.filter fun i => z i ≠ b i

/-- Point with moved set `M`: take `t` on `M`, `b` off `M`. -/
private def bu_tkPt {n : ℕ} (b t : Fin n → ℤ) (M : Finset (Fin n)) :
    Fin n → ℤ :=
  fun i => if i ∈ M then t i else b i

/-! ## Chain cardinality bound -/

/-- The moved sets of a chain form a chain of subsets with the extremal
properties needed for the counting argument. -/
private theorem bu_chain_card_bound {n : ℕ} {σ : Finset (Fin n → ℤ)}
    (hσ : bu_tkChain σ) :
    ∃ b ∈ σ, ∃ t ∈ σ, (∀ z ∈ σ, bu_tkLe b z) ∧ (∀ z ∈ σ, bu_tkLe z t) ∧
      bu_tkS σ = bu_tkSgn t ∧
      (σ.image (bu_tkMv b)).card = σ.card ∧
      (∀ A ∈ σ.image (bu_tkMv b), A ⊆ bu_tkMv b t) ∧
      σ.card ≤ (bu_tkMv b t).card + 1 ∧
      (bu_tkMv b t).card ≤ (bu_tkS σ).card ∧
      (σ.card = (bu_tkS σ).card + 1 →
        bu_tkMv b t = Finset.univ.filter (fun i => t i ≠ 0) ∧
        (σ.image (bu_tkMv b)).card = (bu_tkMv b t).card + 1) ∧
      (σ.card = (bu_tkS σ).card →
        (bu_tkMv b t = Finset.univ.filter (fun i => t i ≠ 0) ∧
          (σ.image (bu_tkMv b)).card = (bu_tkMv b t).card) ∨
        (∃ c, Finset.univ.filter (fun i => t i ≠ 0) = insert c (bu_tkMv b t) ∧
          c ∉ bu_tkMv b t ∧
          (σ.image (bu_tkMv b)).card = (bu_tkMv b t).card + 1)) := by
  obtain ⟨b, hbσ, t, htσ, hbot, htop, hSeq⟩ := bu_chain_bot_top hσ
  have hbt : bu_tkLe b t := htop b hbσ
  have hinj : Set.InjOn (bu_tkMv b) (↑σ : Set (Fin n → ℤ)) := by
    intro z hz w hw he
    have hz' : z ∈ σ := Finset.mem_coe.mp hz
    have hw' : w ∈ σ := Finset.mem_coe.mp hw
    have ez : z = bu_tkPt b t (bu_tkMv b z) :=
      (bu_tkMv_normal_a hbt (hbot z hz') (htop z hz')).2
    have ew : w = bu_tkPt b t (bu_tkMv b w) :=
      (bu_tkMv_normal_a hbt (hbot w hw') (htop w hw')).2
    rw [ez, he]
    exact ew.symm
  have hC : (σ.image (bu_tkMv b)).card = σ.card :=
    Finset.card_image_of_injOn hinj
  have hmemC : ∀ A ∈ σ.image (bu_tkMv b), ∀ B ∈ σ.image (bu_tkMv b),
      A ⊆ B ∨ B ⊆ A := by
    intro A hA B hB
    rw [Finset.mem_image] at hA hB
    obtain ⟨z, hz, rfl⟩ := hA
    obtain ⟨w, hw, rfl⟩ := hB
    rcases hσ.2 z hz w hw with h | h
    · exact Or.inl ((bu_tkMv_le_iff hbt (hbot z hz) (htop z hz)
        (hbot w hw) (htop w hw)).mp h)
    · exact Or.inr ((bu_tkMv_le_iff hbt (hbot w hw) (htop w hw)
        (hbot z hz) (htop z hz)).mp h)
  have hsubX : ∀ A ∈ σ.image (bu_tkMv b), A ⊆ bu_tkMv b t := by
    intro A hA
    rw [Finset.mem_image] at hA
    obtain ⟨z, hz, rfl⟩ := hA
    exact bu_tkMv_mono_of_le (hbot z hz) hbt (htop z hz)
  have hcard_inj : Set.InjOn Finset.card
      (↑(σ.image (bu_tkMv b)) : Set (Finset (Fin n))) := by
    intro A hA B hB he
    have hA' : A ∈ σ.image (bu_tkMv b) := Finset.mem_coe.mp hA
    have hB' : B ∈ σ.image (bu_tkMv b) := Finset.mem_coe.mp hB
    rcases hmemC A hA' B hB' with h | h
    · exact Finset.eq_of_subset_of_card_le h (le_of_eq he.symm)
    · exact (Finset.eq_of_subset_of_card_le h (le_of_eq he)).symm
  have hcle : (σ.image (bu_tkMv b)).card ≤ (bu_tkMv b t).card + 1 := by
    have himg : (σ.image (bu_tkMv b)).image Finset.card ⊆
        Finset.range ((bu_tkMv b t).card + 1) := by
      intro k hk
      rw [Finset.mem_image] at hk
      obtain ⟨A, hA, rfl⟩ := hk
      rw [Finset.mem_range]
      have hAle : A.card ≤ (bu_tkMv b t).card :=
        Finset.card_le_card (hsubX A hA)
      omega
    calc (σ.image (bu_tkMv b)).card = ((σ.image (bu_tkMv b)).image Finset.card).card :=
          (Finset.card_image_of_injOn hcard_inj).symm
      _ ≤ (Finset.range ((bu_tkMv b t).card + 1)).card :=
          Finset.card_le_card himg
      _ = (bu_tkMv b t).card + 1 := Finset.card_range _
  have hXT : bu_tkMv b t ⊆ Finset.univ.filter (fun i => t i ≠ 0) := by
    intro i hi
    rw [bu_tkMv, Finset.mem_filter] at hi
    obtain ⟨_, hne⟩ := hi
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ i, bu_tkMv_sub_support hbt i hne⟩
  have hST : (bu_tkS σ).card = (Finset.univ.filter fun i => t i ≠ 0).card := by
    rw [hSeq, bu_tkSgn_card]
  have h1 : σ.card ≤ (bu_tkMv b t).card + 1 := by omega
  have h2 : (bu_tkMv b t).card ≤ (bu_tkS σ).card := by
    calc (bu_tkMv b t).card ≤ (Finset.univ.filter fun i => t i ≠ 0).card :=
          Finset.card_le_card hXT
      _ = (bu_tkS σ).card := hST.symm
  refine ⟨b, hbσ, t, htσ, hbot, htop, hSeq, hC, hsubX, h1, h2, ?_, ?_⟩
  · intro hc
    have hXeq : (bu_tkMv b t).card = (bu_tkS σ).card := by omega
    have hXeqT : bu_tkMv b t = Finset.univ.filter (fun i => t i ≠ 0) :=
      Finset.eq_of_subset_of_card_le hXT (by omega)
    refine ⟨hXeqT, by omega⟩
  · intro hc
    by_cases hXTcard : (bu_tkMv b t).card = (bu_tkS σ).card
    · left
      refine ⟨Finset.eq_of_subset_of_card_le hXT (by omega), by omega⟩
    · right
      have hlt : (bu_tkMv b t).card + 1 = (bu_tkS σ).card := by omega
      have hsd : (Finset.univ.filter (fun i => t i ≠ 0) \ bu_tkMv b t).Nonempty := by
        rw [← Finset.card_pos, Finset.card_sdiff_of_subset hXT]
        omega
      obtain ⟨c, hc⟩ := hsd
      obtain ⟨hcT, hcX⟩ := Finset.mem_sdiff.mp hc
      refine ⟨c, ?_, hcX, by omega⟩
      have hsub : insert c (bu_tkMv b t) ⊆
          Finset.univ.filter (fun i => t i ≠ 0) :=
        Finset.insert_subset hcT hXT
      have hcard : (Finset.univ.filter fun i => t i ≠ 0).card ≤
          (insert c (bu_tkMv b t)).card := by
        rw [Finset.card_insert_of_notMem hcX]
        omega
      exact (Finset.eq_of_subset_of_card_le hsub hcard).symm

/-! ## Gap lemma (pure finset combinatorics) -/

/-- Comparable extensions of a chain of subsets: members of the powerset
missing from `C` but comparable with all of `C`. -/
private def bu_tkExt {α : Type*} [DecidableEq α] (C : Finset (Finset α))
    (X : Finset α) : Finset (Finset α) :=
  X.powerset.filter fun M => M ∉ C ∧ ∀ A ∈ C, A ⊆ M ∨ M ⊆ A

/-! ## Cofacet classification -/

/-- Decidability of the chain predicate (for the counter filters). -/
private noncomputable instance bu_tkChain_dec {n : ℕ} (σ : Finset (Fin n → ℤ)) :
    Decidable (bu_tkChain σ) :=
  Classical.dec _

/-- Upward extensions with the same sign set (tight-chain counters). -/
private noncomputable def bu_tkUp {n : ℕ} (m : ℕ)
    (σ : Finset (Fin n → ℤ)) : Finset (Fin n → ℤ) :=
  (bu_tkBox n m).filter fun v => v ∉ σ ∧ bu_tkChain (insert v σ) ∧
    bu_tkS (insert v σ) ⊆ bu_tkS σ

/-- Upward extensions gaining exactly the new sign `ℓ` (loose-chain counters). -/
private noncomputable def bu_tkUpL {n : ℕ} (m : ℕ) (σ : Finset (Fin n → ℤ))
    (ℓ : Bool × Fin n) : Finset (Fin n → ℤ) :=
  (bu_tkBox n m).filter fun v => v ∉ σ ∧ bu_tkChain (insert v σ) ∧
    bu_tkS (insert v σ) = insert ℓ (bu_tkS σ)

/-- The sign set of a chain is the sign set of any top element. -/
private theorem bu_tkS_of_top {n : ℕ} {τ : Finset (Fin n → ℤ)} {t : Fin n → ℤ}
    (hτ : bu_tkChain τ) (ht : t ∈ τ) (hall : ∀ z ∈ τ, bu_tkLe z t) :
    bu_tkS τ = bu_tkSgn t := by
  obtain ⟨_, _, t', ht', _, htop', hSeq'⟩ := bu_chain_bot_top hτ
  have h1 : bu_tkSgn t' ⊆ bu_tkSgn t := bu_tkSgn_mono (hall t' ht')
  have h2 : bu_tkSgn t ⊆ bu_tkSgn t' := bu_tkSgn_mono (htop' t ht)
  rw [hSeq', le_antisymm h1 h2]

/-- Pull `c`: the bottom with coordinate `c` moved one step toward `0`. -/
private def bu_tkPull {n : ℕ} (b : Fin n → ℤ) (c : Fin n) : Fin n → ℤ :=
  fun i => if i = c then (if 0 < b c then b c - 1 else b c + 1) else b i

/-- Push `j` up by one. -/
private def bu_tkPush {n : ℕ} (t : Fin n → ℤ) (j : Fin n) (s : ℤ) : Fin n → ℤ :=
  fun i => if i = j then t j + s else t i

/-- Inside cofacets preserve the sign set. -/
private theorem bu_inside_sign {n : ℕ} {σ : Finset (Fin n → ℤ)} {t v : Fin n → ℤ}
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
private theorem bu_ext_inside {n m : ℕ} {σ : Finset (Fin n → ℤ)} {b t : Fin n → ℤ}
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
private theorem bu_below_mem {n : ℕ} {σ : Finset (Fin n → ℤ)} {b t v : Fin n → ℤ}
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
private theorem bu_above_E {n : ℕ} {σ : Finset (Fin n → ℤ)} {b t v : Fin n → ℤ}
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
private theorem bu_push_notmem {n : ℕ} {σ : Finset (Fin n → ℤ)} {t : Fin n → ℤ}
    {c : Fin n} {s : ℤ} (htop : ∀ z ∈ σ, bu_tkLe z t)
    (hH : bu_tkH t < bu_tkH (bu_tkPush t c s)) :
    bu_tkPush t c s ∉ σ := by
  intro hcon
  have hle := bu_tkLe_height (htop _ hcon)
  omega

/-- The push keeps the chain sign set. -/
private theorem bu_push_S {n : ℕ} {σ : Finset (Fin n → ℤ)} {t : Fin n → ℤ}
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

private theorem bu_tight_cofacet_count {n m : ℕ} (hm : 1 ≤ m)
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

private theorem bu_loose_not_bdry {n m : ℕ} (hm : 1 ≤ m)
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

private theorem bu_loose_strict_growth {n m : ℕ}
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

private theorem bu_happy_card {n m : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
    {σ : Finset (Fin n → ℤ)} (h : bu_tkHappy m L σ) :
    σ.card = (bu_tkS σ).card ∨ σ.card = (bu_tkS σ).card + 1 := by
  obtain ⟨_hsub, hchain, hcover⟩ := h
  obtain ⟨_b, _hb, _t, _ht, _hbot, _htop, _hSeq, _hC, _hsubX, h1, h2, _hLoose,
    _hTight⟩ := bu_chain_card_bound hchain
  have hle : (bu_tkS σ).card ≤ σ.card :=
    calc (bu_tkS σ).card ≤ (σ.image L).card := Finset.card_le_card hcover
      _ ≤ σ.card := Finset.card_image_le
  omega

private theorem bu_happy_empty_iff {n : ℕ}
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

private theorem bu_zero_happy {n m : ℕ} {L : (Fin n → ℤ) → Bool × Fin n} :
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

/-! ## The Tucker graph -/

/-- Vertices: finsets of grid points lying in the box (hence a `Fintype`). -/
private def bu_tkV (n m : ℕ) : Type :=
  { σ : Finset (Fin n → ℤ) // σ ∈ (bu_tkBox n m).powerset }

private instance bu_tkVFintype (n m : ℕ) : Fintype (bu_tkV n m) :=
  Finset.fintypeCoeSort _

/-- Door from `σ` to `τ`: `τ` adds one vertex and the old labels cover the new sign set. -/
private def bu_tkDoor {n : ℕ} (L : (Fin n → ℤ) → Bool × Fin n)
    (σ τ : Finset (Fin n → ℤ)) : Prop :=
  ∃ v, v ∉ σ ∧ τ = insert v σ ∧ bu_tkS τ ⊆ σ.image L

/-- Adjacency on underlying finsets: doors either way, or the antipodal boundary edge. -/
private def bu_tkAdj {n : ℕ} (m : ℕ) (L : (Fin n → ℤ) → Bool × Fin n)
    (σ τ : Finset (Fin n → ℤ)) : Prop :=
  bu_tkHappy m L σ ∧ bu_tkHappy m L τ ∧
    (bu_tkDoor L σ τ ∨ bu_tkDoor L τ σ ∨ (bu_tkBdry m σ ∧ τ = σ.image Neg.neg))

private theorem bu_tkBdry_neg {n m : ℕ} {σ : Finset (Fin n → ℤ)}
    (h : bu_tkBdry m σ) : bu_tkBdry m (σ.image Neg.neg) := by
  intro z hz
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨i, hi⟩ := h y hy
  exact ⟨i, by rw [Pi.neg_apply, abs_neg]; exact hi⟩

private theorem bu_tkAdj_symm {n : ℕ} {m : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
    {σ τ : Finset (Fin n → ℤ)} (h : bu_tkAdj m L σ τ) : bu_tkAdj m L τ σ := by
  obtain ⟨hs, ht, hdoor⟩ := h
  refine ⟨ht, hs, ?_⟩
  rcases hdoor with h | h | ⟨hb, rfl⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · refine Or.inr (Or.inr ⟨bu_tkBdry_neg hb, ?_⟩)
    ext y
    constructor
    · intro hy
      refine Finset.mem_image.mpr ⟨-y, Finset.mem_image.mpr ⟨y, hy, rfl⟩, neg_neg y⟩
    · intro hy
      obtain ⟨z, hz, hzz⟩ := Finset.mem_image.mp hy
      obtain ⟨w, hw, hww⟩ := Finset.mem_image.mp hz
      rw [← hww, neg_neg] at hzz
      rw [← hzz]
      exact hw

private theorem bu_tkNeg_image_ne {n m : ℕ} (hm : 1 ≤ m)
    {σ : Finset (Fin n → ℤ)} (hchain : bu_tkChain σ) (hb : bu_tkBdry m σ) :
    σ.image Neg.neg ≠ σ := by
  intro heq
  obtain ⟨b, hbσ, _t, _ht, hbot, _htop, _hSeq⟩ := bu_chain_bot_top hchain
  have hnb : -b ∈ σ := by
    rw [← heq]
    exact Finset.mem_image.mpr ⟨b, hbσ, rfl⟩
  have hH : bu_tkH (-b) = bu_tkH b := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Pi.neg_apply]
    exact Int.natAbs_neg _
  have hbb : b = -b := by
    rcases hchain.2 b hbσ (-b) hnb with h | h
    · exact bu_tkLe_of_height_eq h (by omega)
    · exact (bu_tkLe_of_height_eq h (by omega)).symm
  have hb0 : ∀ i, b i = 0 := by
    intro i
    have hi := congrArg (fun z => z i) hbb
    simp only [Pi.neg_apply] at hi
    omega
  obtain ⟨i, hi⟩ := hb b hbσ
  rw [hb0 i, abs_zero] at hi
  have hm0 : m = 0 := by
    have hcast : ((m : ℕ) : ℤ) = 0 := hi.symm
    exact_mod_cast hcast
  omega

private theorem bu_tkAdj_irrefl {n : ℕ} {m : ℕ} (hm : 1 ≤ m)
    {L : (Fin n → ℤ) → Bool × Fin n}
    {σ : Finset (Fin n → ℤ)} (h : bu_tkAdj m L σ σ) : False := by
  obtain ⟨hs, _, hdoor⟩ := h
  rcases hdoor with ⟨v, hv, heq, _⟩ | ⟨v, hv, heq, _⟩ | ⟨hb, heq⟩
  · have hcc := congrArg Finset.card heq
    rw [Finset.card_insert_of_notMem hv] at hcc
    omega
  · have hcc := congrArg Finset.card heq
    rw [Finset.card_insert_of_notMem hv] at hcc
    omega
  · exact bu_tkNeg_image_ne hm hs.2.1 hb heq.symm

private noncomputable def bu_tkG (n m : ℕ) (L : (Fin n → ℤ) → Bool × Fin n)
    (hm : 1 ≤ m) :
    SimpleGraph (bu_tkV n m) where
  Adj σ τ := bu_tkAdj m L σ.val τ.val
  symm := ⟨fun _ _ h => bu_tkAdj_symm h⟩
  loopless := ⟨fun _ h => bu_tkAdj_irrefl hm h⟩

private noncomputable instance bu_tkGDec {n m : ℕ} (L : (Fin n → ℤ) → Bool × Fin n)
    (hm : 1 ≤ m) :
    DecidableRel (bu_tkG n m L hm).Adj :=
  Classical.decRel _

/-! ## Degree count -/

/-- Decidability of the boundary predicate (for the antipodal counter). -/
private noncomputable instance bu_tkBdry_dec {n m : ℕ} (σ : Finset (Fin n → ℤ)) :
    Decidable (bu_tkBdry m σ) :=
  Classical.dec _

/-- Up-neighbors: one-vertex extensions whose new sign set is covered by old labels. -/
private noncomputable def bu_upFin {n : ℕ} (m : ℕ) (L : (Fin n → ℤ) → Bool × Fin n)
    (σ : Finset (Fin n → ℤ)) : Finset (Finset (Fin n → ℤ)) :=
  ((bu_tkBox n m).filter fun v =>
    v ∉ σ ∧ bu_tkChain (insert v σ) ∧ bu_tkS (insert v σ) ⊆ σ.image L).image
    fun v => insert v σ

/-- Down-neighbors: one-vertex deletions still covering the sign set. -/
private def bu_downFin {n : ℕ} (L : (Fin n → ℤ) → Bool × Fin n)
    (σ : Finset (Fin n → ℤ)) : Finset (Finset (Fin n → ℤ)) :=
  (σ.filter fun w =>
    (σ.erase w).Nonempty ∧ bu_tkS σ ⊆ (σ.erase w).image L).image
    fun w => σ.erase w

/-- Antipodal neighbor: the negation image when on the boundary. -/
private noncomputable def bu_antiFin {n : ℕ} (m : ℕ) (σ : Finset (Fin n → ℤ)) :
    Finset (Finset (Fin n → ℤ)) :=
  if bu_tkBdry m σ then {σ.image Neg.neg} else ∅

/-- Loose chains covered by `S` have no up-neighbors (signs would grow). -/
private theorem bu_up_loose_eq {n m : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
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

private theorem bu_loose_upL_card {n m : ℕ} (hm : 1 ≤ m)
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
private theorem bu_upFin_loose_new_card {n m : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
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
private theorem bu_degree_singleton {n m : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
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
private theorem bu_degree_tight {n m : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
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
private theorem bu_degree_loose_eq {n m : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
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
private theorem bu_degree_loose_new {n m : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
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
private theorem bu_degree_happy_two {n m : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
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
private theorem bu_degree_odd_iff {n m : ℕ} {L : (Fin n → ℤ) → Bool × Fin n}
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

/-! ## Lift from the cube to the upper hemisphere -/

/-- The unnormalized lift `x ↦ (1 - ‖x‖, x)` into `ℝ^(n+1)`. -/
private def buV (n : ℕ) (x : Fin n → ℝ) : EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (Fin.cons (α := fun _ => ℝ) (1 - ‖x‖) x)

/-- The lift never hits the origin. -/
private theorem buV_ne_zero {n : ℕ} (x : Fin n → ℝ) : buV n x ≠ 0 := by
  rw [buV]
  intro hcon
  have hcon' : Fin.cons (α := fun _ => ℝ) (1 - ‖x‖) x = (0 : Fin (n + 1) → ℝ) := by
    have h2 := congrArg WithLp.ofLp hcon
    simpa [WithLp.ofLp_toLp] using h2
  have hhead : (1 : ℝ) - ‖x‖ = 0 := by
    have h0 := congrFun hcon' (0 : Fin (n + 1))
    rw [Fin.cons_zero, Pi.zero_apply] at h0
    exact h0
  have hnorm : ‖x‖ = 1 := by
    have h := sub_eq_zero.mp hhead
    exact h.symm
  have hx0 : x ≠ 0 := by
    intro hx
    rw [hx, norm_zero] at hnorm
    exact zero_ne_one hnorm
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx0
  have htail := congrFun hcon' i.succ
  rw [Fin.cons_succ, Pi.zero_apply] at htail
  exact hi htail

/-- The lift to the sphere (normalized). -/
private noncomputable def buLift (n : ℕ) (x : Fin n → ℝ) :
    sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
  ⟨‖buV n x‖⁻¹ • buV n x, by
    rw [mem_sphere_zero_iff_norm]
    exact norm_smul_inv_norm (buV_ne_zero x)⟩

/-- The lift to the sphere is continuous. -/
private theorem buLift_continuous {n : ℕ} : Continuous (buLift n) := by
  have hsmul : Continuous (fun x : Fin n → ℝ => ‖buV n x‖⁻¹ • buV n x) :=
    Continuous.smul
      (Continuous.inv₀ buV_continuous.norm
        (fun x => norm_ne_zero_iff.mpr (buV_ne_zero x)))
      buV_continuous
  exact Continuous.subtype_mk hsmul _

/-! ## The odd map from the lift -/

/-- The difference map `x ↦ F (lift x) - F (-lift x)`, read off in coordinates. -/
private noncomputable def buG (n : ℕ)
    (F : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 → EuclideanSpace ℝ (Fin n))
    (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (F (buLift n x) - F (-buLift n x)).ofLp i

/-- The difference map is continuous. -/
private theorem buG_continuous {n : ℕ}
    {F : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 → EuclideanSpace ℝ (Fin n)}
    (hF : Continuous F) : Continuous (buG n F) := by
  have h1 : Continuous (fun x : Fin n → ℝ => F (buLift n x)) :=
    hF.comp buLift_continuous
  have h2 : Continuous (fun x : Fin n → ℝ => F (-buLift n x)) :=
    hF.comp (continuous_neg.comp buLift_continuous)
  have hsub : Continuous
      (fun x : Fin n → ℝ => F (buLift n x) - F (-buLift n x)) := h1.sub h2
  unfold buG
  exact continuous_pi fun i => (PiLp.continuous_apply 2 _ i).comp hsub

/-! ## Argmax labelling -/

/-- Argmax index of `a : Fin n → ℝ` (any maximizer). -/
private noncomputable def buIdx {n : ℕ} [Nonempty (Fin n)] (a : Fin n → ℝ) : Fin n :=
  Classical.choose (Finset.exists_max_image Finset.univ a Finset.univ_nonempty)

/-- Argmax of absolute values. -/
private noncomputable def buI {n : ℕ} [Nonempty (Fin n)] (v : Fin n → ℝ) : Fin n :=
  buIdx (fun i => |v i|)

/-- The label: sign and argmax index. -/
private noncomputable def buLab {n : ℕ} [Nonempty (Fin n)] (v : Fin n → ℝ) : Bool × Fin n :=
  (decide (0 < v (buI v)), buI v)

/-! ## Tucker's lemma -/

/-- Tucker's lemma on the grid: an antipodal labeling has a complementary edge. -/
private theorem bu_tucker {n m : ℕ} (h0 : 0 < m)
    {L : (Fin n → ℤ) → Bool × Fin n}
    (hanti : ∀ z ∈ bu_tkBox n m, (∃ i, |z i| = (m : ℤ)) → L (-z) = bu_tkNeg (L z)) :
    ∃ z ∈ bu_tkBox n m, ∃ w ∈ bu_tkBox n m,
      bu_tkLe z w ∧ L w = bu_tkNeg (L z) := by
  have hm : 1 ≤ m := h0
  by_contra hcon
  have hN : bu_tkNoCompl m L := by
    intro z hz w hw hle heq
    exact hcon ⟨z, hz, w, hw, hle, heq⟩
  have hmem0 : ({0} : Finset (Fin n → ℤ)) ∈ (bu_tkBox n m).powerset := by
    rw [Finset.mem_powerset]
    intro z hz
    rw [Finset.mem_singleton] at hz
    rw [hz]
    exact bu_zero_mem_tkBox
  set v0 : bu_tkV n m := ⟨{0}, hmem0⟩ with hv0def
  have hfilter : Finset.univ.filter
      (fun v => Odd ((bu_tkG n m L hm).degree v)) = {v0} := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    rw [bu_degree_odd_iff (hm := hm) hanti hN]
    constructor
    · intro hval
      exact Subtype.ext hval
    · intro he
      rw [he]
  have heven := SimpleGraph.even_card_odd_degree_vertices (bu_tkG n m L hm)
  rw [hfilter, Finset.card_singleton] at heven
  exact (by decide : ¬ Even (1 : ℕ)) heven

/-! ## The no-zero contradiction -/

/-- Grid points scaled into the unit cube. -/
private noncomputable def buPt {n : ℕ} (m : ℕ) (z : Fin n → ℤ) : Fin n → ℝ :=
  fun i => ((z i : ℤ) : ℝ) / (m : ℝ)

/-- An odd map on the cube has a zero in the unit ball. -/
private theorem bu_no_zero {n : ℕ} [Nonempty (Fin n)]
    {g : (Fin n → ℝ) → (Fin n → ℝ)} (hg : Continuous g)
    (hodd : ∀ x : Fin n → ℝ, ‖x‖ = 1 → g (-x) = -g x) :
    ∃ x ∈ Metric.closedBall (0 : Fin n → ℝ) 1, g x = 0 := by
  by_contra hcon
  have hne : ∀ x ∈ Metric.closedBall (0 : Fin n → ℝ) 1, g x ≠ 0 := by
    intro x hx heq
    exact hcon ⟨x, hx, heq⟩
  obtain ⟨ε, hεpos, hε, δ, hδpos, hδε⟩ := bu_eps_delta hg hne
  obtain ⟨m, hmgt⟩ := exists_nat_gt (1 / δ)
  have hδnn : (0 : ℝ) < 1 / δ := one_div_pos.mpr hδpos
  have hm0 : 0 < m := by
    have hR : (0 : ℝ) < (m : ℝ) := lt_trans hδnn hmgt
    exact_mod_cast hR
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
  have h1m : (1 : ℝ) / (m : ℝ) < δ := by
    have h := one_div_lt_one_div_of_lt hδnn hmgt
    rwa [one_div_one_div] at h
  have hbox : ∀ z ∈ bu_tkBox n m, buPt m z ∈ Metric.closedBall (0 : Fin n → ℝ) 1 :=
    fun z hz => buPt_mem hmR hz
  have hnorm1 : ∀ z ∈ bu_tkBox n m, (∃ i, |z i| = (m : ℤ)) → ‖buPt m z‖ = 1 :=
    fun z hz hbd => buPt_norm_one hmR hz hbd
  have hPtneg : ∀ z : Fin n → ℤ, buPt m (-z) = -buPt m z := fun z => buPt_neg z
  have hanti : ∀ z ∈ bu_tkBox n m, (∃ i, |z i| = (m : ℤ)) →
      (fun z => buLab (g (buPt m z))) (-z) =
        bu_tkNeg ((fun z => buLab (g (buPt m z))) z) := by
    intro z hz hbd
    change buLab (g (buPt m (-z))) = bu_tkNeg (buLab (g (buPt m z)))
    have h1 : g (buPt m (-z)) = -g (buPt m z) := by
      rw [hPtneg]
      exact hodd _ (hnorm1 z hz hbd)
    rw [h1]
    exact buLab_neg (hne _ (hbox z hz))
  obtain ⟨z, hz, w, hw, hle, heq⟩ :=
    bu_tucker (L := fun z => buLab (g (buPt m z))) hm0 hanti
  have heq_fst : decide (0 < (g (buPt m w)) (buI (g (buPt m w)))) =
      !(decide (0 < (g (buPt m z)) (buI (g (buPt m z))))) :=
    congrArg Prod.fst heq
  have heq_snd : buI (g (buPt m w)) = buI (g (buPt m z)) := congrArg Prod.snd heq
  rw [heq_snd] at heq_fst
  have haI : (g (buPt m z)) (buI (g (buPt m z))) ≠ 0 :=
    buI_ne_zero_of_ne (hne _ (hbox z hz))
  have hbI : (g (buPt m w)) (buI (g (buPt m z))) ≠ 0 := by
    rw [← heq_snd]
    exact buI_ne_zero_of_ne (hne _ (hbox w hw))
  have hsign : (0 < (g (buPt m z)) (buI (g (buPt m z))) ∧
        (g (buPt m w)) (buI (g (buPt m z))) < 0) ∨
      ((g (buPt m z)) (buI (g (buPt m z))) < 0 ∧
        0 < (g (buPt m w)) (buI (g (buPt m z)))) := by
    by_cases hda : 0 < (g (buPt m z)) (buI (g (buPt m z)))
    · left
      refine ⟨hda, ?_⟩
      have hdb : decide (0 < (g (buPt m w)) (buI (g (buPt m z)))) = false := by
        rw [heq_fst, decide_eq_true hda, Bool.not_true]
      have hn : ¬ 0 < (g (buPt m w)) (buI (g (buPt m z))) := of_decide_eq_false hdb
      exact lt_of_le_of_ne (not_lt.mp hn) (fun he => hbI he)
    · right
      have halt : (g (buPt m z)) (buI (g (buPt m z))) < 0 :=
        lt_of_le_of_ne (not_lt.mp hda) (fun he => haI he)
      have hdb : decide (0 < (g (buPt m w)) (buI (g (buPt m z)))) = true := by
        rw [heq_fst, decide_eq_false hda, Bool.not_false]
      exact ⟨halt, of_decide_eq_true hdb⟩
  have hgap : |(g (buPt m z)) (buI (g (buPt m z)))| ≤
      |(g (buPt m z)) (buI (g (buPt m z))) - (g (buPt m w)) (buI (g (buPt m z)))| := by
    rcases hsign with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hle1 : (g (buPt m z)) (buI (g (buPt m z))) ≤
          (g (buPt m z)) (buI (g (buPt m z))) - (g (buPt m w)) (buI (g (buPt m z))) := by
        linarith
      rw [abs_of_pos h1]
      exact le_trans hle1 (le_abs_self _)
    · have hle1 : (g (buPt m z)) (buI (g (buPt m z))) -
          (g (buPt m w)) (buI (g (buPt m z))) ≤
          (g (buPt m z)) (buI (g (buPt m z))) := by
        linarith
      have hneg : (g (buPt m z)) (buI (g (buPt m z))) -
          (g (buPt m w)) (buI (g (buPt m z))) < 0 :=
        lt_of_le_of_lt hle1 h1
      rw [abs_of_neg h1, abs_of_neg hneg]
      linarith
  have hclose : dist (g (buPt m z)) (g (buPt m w)) < ε :=
    hδε _ (hbox z hz) _ (hbox w hw) (buPt_dist hmR hle |>.trans_lt h1m)
  have hfar : ε ≤ dist (g (buPt m z)) (g (buPt m w)) := by
    rw [dist_eq_norm]
    have h1 : |(g (buPt m z)) (buI (g (buPt m z))) -
        (g (buPt m w)) (buI (g (buPt m z)))| ≤ ‖g (buPt m z) - g (buPt m w)‖ := by
      have h2 := norm_le_pi_norm (g (buPt m z) - g (buPt m w)) (buI (g (buPt m z)))
      rwa [Real.norm_eq_abs, Pi.sub_apply] at h2
    have h3 : ‖g (buPt m z)‖ ≤ ‖g (buPt m z) - g (buPt m w)‖ := by
      rw [buI_norm (g (buPt m z))]
      exact le_trans hgap h1
    exact le_trans (hε _ (hbox z hz)) h3
  linarith

/--
Every continuous `S^n → ℝ^n` identifies an antipodal pair `∃ x, f x = f (-x)`. Source: K. Borsuk,
Fund. Math. 20 (1933) 177–190 antipodal theorem; S. Ulam; J. Matoušek, Using the Borsuk–Ulam
Theorem; Lean states `EuclideanSpace ℝ (Fin (n+1))` to `Fin n` specialization.

Proves `Wanted` entry `borsukUlam`.
-/
theorem borsukUlam
    {n : ℕ} (f : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 → EuclideanSpace ℝ (Fin n))
    (hf : Continuous f) :
    ∃ x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, f x = f (-x) := by
  cases n with
  | zero =>
    refine ⟨buLift 0 0, ?_⟩
    apply PiLp.ext
    intro i
    exact Fin.elim0 i
  | succ k =>
    have hg : Continuous (buG (k + 1) f) := buG_continuous hf
    have hodd : ∀ x : Fin (k + 1) → ℝ, ‖x‖ = 1 → buG (k + 1) f (-x) = -buG (k + 1) f x :=
      fun x hx => buG_neg_of_norm_one hx
    obtain ⟨x, _, hx0⟩ := bu_no_zero hg hodd
    exact ⟨buLift (k + 1) x, buG_zero hx0⟩

end MathlibExt.Topology.Homotopy.BorsukUlamWanted
