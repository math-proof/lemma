import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.ArithmeticGeometry.code.PadicCompletion.Part2
open Polynomial PadicInt InverseLimit


namespace InverseLimit

/--
[imgCh_succ_subset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicCompletion.lean)
-/
@[path]
lemma imgCh_succ_subset
  {S : ℕ → Type u}
  {fn : (n : ℕ) → S (n + 1) → S n}
  {n k : ℕ} :
-- imply
  imgCh fn n (k + 1) ⊆ imgCh fn n k := by
-- proof
  induction k generalizing n with
  | zero => intro x _; exact Set.mem_univ x
  | succ k ih => exact Set.image_mono (ih (n + 1))

end InverseLimit

namespace InverseLimit

/--
[imgCh_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicCompletion.lean)
-/
@[path]
lemma imgCh_antitone
  {S : ℕ → Type u}
  {fn : (n : ℕ) → S (n + 1) → S n}
  {n : ℕ} :
-- imply
  Antitone (imgCh fn n) :=
-- proof
  antitone_nat_of_succ_le (imgCh_succ_subset fn n)

end InverseLimit

namespace InverseLimit

/--
[imgCh_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicCompletion.lean)
-/
@[path]
lemma imgCh_nonempty
  {S : ℕ → Type u}
  {fn : (n : ℕ) → S (n + 1) → S n}
  [∀ n, Nonempty (S n)]
  {n k : ℕ} :
-- imply
  (imgCh fn n k).Nonempty := by
-- proof
  induction k generalizing n with
  | zero => exact Set.univ_nonempty
  | succ k ih => exact Set.Nonempty.image _ (ih (n + 1))

end InverseLimit

namespace InverseLimit

/--
[nat_antitone_stabilizes](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicCompletion.lean)
-/
@[path]
lemma nat_antitone_stabilizes
  {S : ℕ → Type u}
  {fn : (n : ℕ) → S (n + 1) → S n}
  {g : ℕ → ℕ}
-- given
  (hg : Antitone g) :
-- imply
  ∃ N, ∀ k, N ≤ k → g k = g N := by
-- proof
  by_contra h
  push Not at h
  have hstep : ∀ N, ∃ k, N ≤ k ∧ g k < g N := by
    intro N; obtain ⟨k, hk1, hk2⟩ := h N
    exact ⟨k, hk1, lt_of_le_of_ne (hg hk1) hk2⟩
  suffices ∀ n, ∃ k, g k + n ≤ g 0 from by
    obtain ⟨k, hk⟩ := this (g 0 + 1); omega
  intro n; induction n with
  | zero => exact ⟨0, le_refl _⟩
  | succ n ih =>
    obtain ⟨k, hk⟩ := ih; obtain ⟨k', _, hlt⟩ := hstep k; exact ⟨k', by omega⟩

end InverseLimit

namespace InverseLimit

/--
[iInter_nonempty_of_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicCompletion.lean)
-/
@[path]
lemma iInter_nonempty_of_antitone
  {S : ℕ → Type u}
  {fn : (n : ℕ) → S (n + 1) → S n}
  {α : Type u}
  [Fintype α]
  {T : ℕ → Set α}
-- given
  (hanti : Antitone T)
  (hne : ∀ k, (T k).Nonempty) :
-- imply
  (⋂ k, T k).Nonempty := by
-- proof
  classical
  have hcard_anti : Antitone (fun k => Fintype.card ↥(T k)) := fun a b hab =>
    Fintype.card_le_of_injective (Set.inclusion (hanti hab)) (Set.inclusion_injective _)
  obtain ⟨N, hN⟩ := nat_antitone_stabilizes hcard_anti
  have hT_stab : ∀ k, N ≤ k → T k = T N :=
    fun k hk => Set.eq_of_subset_of_card_le (hanti hk) (le_of_eq (hN k hk).symm)
  suffices ⋂ k, T k = T N by rw [this]; exact hne N
  apply le_antisymm (Set.iInter_subset T N)
  intro x hx; rw [Set.mem_iInter]
  exact fun k => if hk : N ≤ k then (hT_stab k hk) ▸ hx else hanti (by omega) hx

end InverseLimit

namespace InverseLimit

/--
[surjective_on_eventual_image](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicCompletion.lean)
-/
@[path]
lemma surjective_on_eventual_image
  {S : ℕ → Type u}
  {fn : (n : ℕ) → S (n + 1) → S n}
  [∀ n, Fintype (S n)]
  [∀ n, Nonempty (S n)]
  {n : ℕ}
  {x : S n}
-- given
  (hx : x ∈ ⋂ k, imgCh fn n k) :
-- imply
  ∃ y ∈ ⋂ k, imgCh fn (n + 1) k, fn n y = x := by
-- proof
  classical
  let P : ℕ → Set (S (n + 1)) := fun k => fn n ⁻¹' {x} ∩ imgCh fn (n + 1) k
  have hP_ne : ∀ k, (P k).Nonempty := by
    intro k
    have hxk : x ∈ imgCh fn n (k + 1) := Set.mem_iInter.mp hx (k + 1)
    obtain ⟨y, hy_mem, hy_eq⟩ := hxk
    exact ⟨y, Set.mem_inter (Set.mem_preimage.mpr (Set.mem_singleton_iff.mpr hy_eq)) hy_mem⟩
  have hP_anti : Antitone P := fun _ _ hab =>
    Set.inter_subset_inter_right _ (imgCh_antitone fn (n + 1) hab)
  obtain ⟨y, hy⟩ := iInter_nonempty_of_antitone hP_anti hP_ne
  simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, P] at hy
  exact ⟨y, Set.mem_iInter.mpr (fun k => (hy k).2), (hy 0).1⟩

end InverseLimit

namespace InverseLimit

/--
[nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicCompletion.lean)
-/
@[path]
lemma nonempty
  {S : ℕ → Type u}
  {fn : (n : ℕ) → S (n + 1) → S n}
  {S : ℕ → Type u}
  {fn : (n : ℕ) → S (n + 1) → S n}
  [∀ n, Fintype (S n)]
  [∀ n, Nonempty (S n)] :
-- imply
  Nonempty (InverseLimit S fn) := by
-- proof
  classical
  have hE_ne : ∀ n, (⋂ k, imgCh fn n k).Nonempty :=
    fun n => iInter_nonempty_of_antitone (imgCh_antitone fn n) (imgCh_nonempty fn n)
  have hsurj : ∀ n (x : S n), x ∈ ⋂ k, imgCh fn n k →
    ∃ y ∈ ⋂ k, imgCh fn (n + 1) k, fn n y = x :=
    fun n x hx => surjective_on_eventual_image fn n x hx
  let build : (n : ℕ) → { x : S n // x ∈ ⋂ k, imgCh fn n k } := fun n =>
    Nat.rec
      ⟨(hE_ne 0).some, (hE_ne 0).some_mem⟩
      (fun n prev =>
        ⟨(hsurj n prev.val prev.property).choose,
          (hsurj n prev.val prev.property).choose_spec.1⟩)
      n
  have hcompat : ∀ n, fn n (build (n + 1)).val = (build n).val :=
    fun n => (hsurj n (build n).val (build n).property).choose_spec.2
  exact ⟨⟨fun n => (build n).val, hcompat⟩⟩
end InverseLimit
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime]
open Polynomial PadicInt


/--
[polyRootReduction_val](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicCompletion.lean)
-/
@[path]
lemma polyRootReduction_val
  {p : ℕ}
  [hp : Fact p.Prime]
  {f : Polynomial ℤ_[p]}
  {n : ℕ}
  {x : PolyRootSet f (n + 1)} :
-- imply
  (polyRootReduction f n x).val = ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) x.val :=
-- proof
  rfl

/--
[padic_poly_root_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicCompletion.lean)
-/
@[path]
lemma padic_poly_root_iff
  {p : ℕ}
  [hp : Fact p.Prime]
  {f : Polynomial ℤ_[p]} :
-- imply
  (∃ a : ℤ_[p], Polynomial.eval a f = 0) ↔ (∀ n : ℕ, ∃ r : ZMod (p ^ n), Polynomial.eval r (Polynomial.map (toZModPow n) f) = 0) := by
-- proof
  constructor
  ·
    rintro ⟨a, ha⟩ n
    exact ⟨toZModPow n a, by rw [eval_map, eval₂_at_apply, ha, map_zero]⟩
  ·
    intro hroots
    haveI hne : ∀ n, Nonempty (PolyRootSet f n) := fun n =>
      let ⟨r, hr⟩ := hroots n; ⟨⟨r, hr⟩⟩
    obtain ⟨s⟩ := InverseLimit.nonempty (PolyRootSet f) (polyRootReduction f)
    let seq : ℕ → ℤ := fun n => (s.val n).val.val
    have hdvd : ∀ i, (p : ℤ) ^ i ∣ seq (i + 1) - seq i := by
      intro i
      haveI : NeZero (p ^ i) := ⟨pow_ne_zero i (Nat.Prime.ne_zero hp.out)⟩
      have hcomp := s.property i
      have hcast : (ZMod.castHom (pow_dvd_pow p (Nat.le_succ i)) (ZMod (p ^ i)))
        (s.val (i + 1)).val = (s.val i).val := by
        rw [← polyRootReduction_val]; exact congr_arg Subtype.val hcomp
      rw [ZMod.castHom_apply] at hcast
      rw [show (p ^ i : ℤ) = ((p ^ i : ℕ) : ℤ) from by push_cast; ring]
      rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
      rwa [Int.cast_natCast, Int.cast_natCast, ZMod.natCast_zmod_val, ZMod.natCast_val]
    let a : ℤ_[p] := PadicInt.ofIntSeq seq
      (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub seq p hdvd)
    have hproj : ∀ n, toZModPow n a = (s.val n).val := by
      intro n
      haveI : NeZero (p ^ n) := ⟨pow_ne_zero n (Nat.Prime.ne_zero hp.out)⟩
      have := PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub seq p hdvd n
      simp only [seq] at this
      rw [this, Int.cast_natCast, ZMod.natCast_zmod_val]
    refine ⟨a, ext_of_toZModPow.mp (fun n => ?_)⟩
    have : toZModPow n (Polynomial.eval a f) =
      Polynomial.eval (toZModPow n a) (Polynomial.map (toZModPow n) f) := by
      rw [eval_map, eval₂_at_apply]
    rw [this, hproj n, (s.val n).property, map_zero]
end


-- created on 2026-10-23
