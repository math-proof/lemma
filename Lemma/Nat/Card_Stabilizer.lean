import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.GroupTheory.DicksonPGL2Tame.Part4
open scoped BigOperators
open MetaMathlibExt
open Dickson


namespace Definitions
end Definitions
namespace MetaMathlibExt

/--
[dickson_card_stabilizer_eq_of_quotient_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/DicksonPGL2Tame.lean)
-/
@[path]
private lemma dickson_card_stabilizer_eq_of_quotient_eq
  {G X : Type*} [Group G] [MulAction G X] (u v : X)
  (huv : Quotient.mk'' u = (Quotient.mk'' v : MulAction.orbitRel.Quotient G X)) :
  Nat.card (MulAction.stabilizer G u) = Nat.card (MulAction.stabilizer G v) := by
  obtain ⟨g, hg⟩ := Quotient.exact huv
  rwa [← hg, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
    (Subgroup.equivMapOfInjective (MulAction.stabilizer G v)
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm

end MetaMathlibExt

namespace MetaMathlibExt

/--
[dicksonExceptional_finite](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/DicksonPGL2Tame.lean)
-/
@[path]
private lemma dicksonExceptional_finite {G X : Type*} [Group G] [MulAction G X]
  [Finite G] (hfixed : ∀ g : G, g ≠ 1 → Nat.card (MulAction.fixedBy X g) = 2) :
  Finite (dicksonExceptional G X) := by
  let NG := {g : G // g ≠ 1}
  let Y := Σ g : NG, MulAction.fixedBy X g.1
  let _ : Finite NG := inferInstance
  let _ (g : NG) : Finite (MulAction.fixedBy X g.1) :=
    Nat.finite_of_card_ne_zero (by rw [hfixed g.1 g.2]; decide)
  let _ : Finite Y := inferInstance
  let f : dicksonExceptional G X → Y := fun x =>
    ⟨⟨Classical.choose x.2, (Classical.choose_spec x.2).1⟩,
      ⟨x.1, (Classical.choose_spec x.2).2⟩⟩
  exact Finite.of_injective f fun x y hxy => by
    apply Subtype.ext
    exact congrArg (fun z : Y => z.2.1) hxy

end MetaMathlibExt

namespace MetaMathlibExt

/--
[dickson_two_mul_card_le_orbits_mul_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/DicksonPGL2Tame.lean)
-/
@[path]
private lemma dickson_two_mul_card_le_orbits_mul_card
  (G X : Type*) [Group G] [MulAction G X] [Finite G] [Finite X]
  (hnontrivial : ∀ x : X, Nontrivial (MulAction.stabilizer G x)) :
  2 * Nat.card X ≤ Nat.card (MulAction.orbitRel.Quotient G X) * Nat.card G := by
  classical
  let _ := Fintype.ofFinite G
  let _ := Fintype.ofFinite X
  let _ := Fintype.ofFinite (MulAction.orbitRel.Quotient G X)
  let _ : (x : X) → Fintype (MulAction.stabilizer G x) :=
    fun x => Fintype.ofFinite (MulAction.stabilizer G x)
  simp only [Nat.card_eq_fintype_card]
  rw [MulAction.card_eq_sum_card_group_div_card_stabilizer G X]
  rw [Finset.mul_sum]
  calc
    ∑ ω : MulAction.orbitRel.Quotient G X,
      2 * (Fintype.card G / Fintype.card (MulAction.stabilizer G ω.out)) ≤
      ∑ _ω : MulAction.orbitRel.Quotient G X, Fintype.card G := by
      apply Finset.sum_le_sum
      intro ω _
      have he : 2 ≤ Fintype.card (MulAction.stabilizer G ω.out) := by
        have := Fintype.one_lt_card_iff_nontrivial.mpr (hnontrivial ω.out)
        omega
      have hdvd : Fintype.card (MulAction.stabilizer G ω.out) ∣ Fintype.card G := by
        simpa only [Nat.card_eq_fintype_card] using
          Subgroup.card_subgroup_dvd_card (MulAction.stabilizer G ω.out)
      calc
        2 * (Fintype.card G / Fintype.card (MulAction.stabilizer G ω.out)) ≤
          Fintype.card (MulAction.stabilizer G ω.out) *
            (Fintype.card G / Fintype.card (MulAction.stabilizer G ω.out)) :=
          Nat.mul_le_mul_right _ he
        _ = Fintype.card G := by
          rw [mul_comm, Nat.div_mul_cancel hdvd]
    _ = Fintype.card (MulAction.orbitRel.Quotient G X) * Fintype.card G := by simp

end MetaMathlibExt

namespace MetaMathlibExt

/--
[dickson_orbitPerm_injective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/DicksonPGL2Tame.lean)
-/
@[path]
private lemma dickson_orbitPerm_injective (G X : Type*) [Group G] [MulAction G X]
  [Finite G] [Finite X]
  (hfixed : ∀ g : G, g ≠ 1 → Nat.card (MulAction.fixedBy X g) = 2)
  (x : X) (horbit : 3 ≤ Nat.card (MulAction.orbit G x)) :
  Function.Injective (MulAction.toPermHom G (MulAction.orbit G x)) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  ext g
  simp only [MonoidHom.mem_ker, Subgroup.mem_bot]
  constructor
  · intro hg
    by_contra hg1
    have hfixg (y : MulAction.orbit G x) : g • y = y := by
      have := Equiv.congr_fun hg y
      simpa using this
    let f : MulAction.orbit G x → MulAction.fixedBy X g := fun y =>
      ⟨y.1, congrArg Subtype.val (hfixg y)⟩
    have hle := Nat.card_le_card_of_injective f fun y z hyz => by
      apply Subtype.ext
      exact congrArg (fun w : MulAction.fixedBy X g => w.1) hyz
    rw [hfixed g hg1] at hle
    omega
  · rintro rfl
    exact map_one (MulAction.toPermHom G (MulAction.orbit G x))

end MetaMathlibExt

namespace MetaMathlibExt

/--
[dickson_orbit_count_cases](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/DicksonPGL2Tame.lean)
-/
@[path]
private lemma dickson_orbit_count_cases (N E r : ℕ) (hN : 2 ≤ N)
  (hcount : E + 2 * (N - 1) = r * N)
  (hupper : 2 * E ≤ r * N) (hlower : r ≤ E) : r = 2 ∨ r = 3 := by
  have hr2 : 2 ≤ r := by
    by_contra hn
    have hr1 : r ≤ 1 := by omega
    interval_cases r <;> simp_all <;> omega
  have hE : E ≤ 2 * (N - 1) := by
    rw [← hcount] at hupper
    omega
  have hr3 : r ≤ 3 := by
    by_contra hn
    have hr4 : 4 ≤ r := by omega
    have h4N : 4 * N ≤ r * N := Nat.mul_le_mul_right N hr4
    rw [← hcount] at h4N
    omega
  omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[dickson_orbit_signature_sorted](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/DicksonPGL2Tame.lean)
-/
@[path]
private lemma dickson_orbit_signature_sorted (N a b c e f h : ℕ)
  (hN : 2 ≤ N) (ha : a * e = N) (hb : b * f = N) (hc : c * h = N)
  (he : 2 ≤ e) (hef : e ≤ f) (hfh : f ≤ h)
  (hsum : a + b + c = N + 2) :
  (e = 2 ∧ f = 2 ∧ N = 2 * h) ∨
  (e = 2 ∧ f = 3 ∧ h = 3 ∧ N = 12) ∨
  (e = 2 ∧ f = 3 ∧ h = 4 ∧ N = 24) ∨
  (e = 2 ∧ f = 3 ∧ h = 5 ∧ N = 60) := by
  have ha0 : 1 ≤ a := by
    by_contra hn
    have : a = 0 := by omega
    simp [this] at ha
    omega
  have hb0 : 1 ≤ b := by
    by_contra hn
    have : b = 0 := by omega
    simp [this] at hb
    omega
  have hc0 : 1 ≤ c := by
    by_contra hn
    have : c = 0 := by omega
    simp [this] at hc
    omega
  have he2 : e = 2 := by
    by_contra hn
    have he3 : 3 ≤ e := by omega
    have h3a : 3 * a ≤ N := by nlinarith [ha]
    have h3b : 3 * b ≤ N := by nlinarith [hb]
    have h3c : 3 * c ≤ N := by nlinarith [hc]
    omega
  subst e
  have hf4 : f ≤ 3 := by
    by_contra hn
    have hf4 : 4 ≤ f := by omega
    have h2a : 2 * a = N := by nlinarith [ha]
    have h4b : 4 * b ≤ N := by nlinarith [hb]
    have h4c : 4 * c ≤ N := by nlinarith [hc]
    omega
  have hf2 : 2 ≤ f := by omega
  obtain rfl | rfl := (show f = 2 ∨ f = 3 by omega)
  · left
    refine ⟨rfl, rfl, ?_⟩
    have hc2 : c = 2 := by omega
    nlinarith [hc]
  · right
    have hh3 : 3 ≤ h := by omega
    have hh5 : h ≤ 5 := by
      by_contra hn
      have hh6 : 6 ≤ h := by omega
      have h3a : 3 * N = 6 * a := by nlinarith [ha]
      have h2b : 2 * N = 6 * b := by nlinarith [hb]
      have h6c : 6 * c ≤ N := by nlinarith [hc]
      omega
    interval_cases h
    · left
      omega
    · right; left
      omega
    · right; right
      omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[dickson_orbit_signature](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/DicksonPGL2Tame.lean)
-/
@[path]
private lemma dickson_orbit_signature (N a b c e f h : ℕ)
  (hN : 2 ≤ N) (ha : a * e = N) (hb : b * f = N) (hc : c * h = N)
  (he : 2 ≤ e) (hf : 2 ≤ f) (hh : 2 ≤ h)
  (hsum : a + b + c = N + 2) :
  (∃ n, 2 ≤ n ∧ N = 2 * n ∧ (e = n ∨ f = n ∨ h = n) ∧
    ∀ d, (d = e ∨ d = f ∨ d = h) → d = 2 ∨ d = n) ∨
  (N = 12 ∧ (e = 3 ∨ f = 3 ∨ h = 3) ∧
    ∀ d, (d = e ∨ d = f ∨ d = h) → d = 2 ∨ d = 3) ∨
  (N = 24 ∧ (e = 3 ∨ f = 3 ∨ h = 3) ∧ (e = 4 ∨ f = 4 ∨ h = 4) ∧
    ∀ d, (d = e ∨ d = f ∨ d = h) → d = 2 ∨ d = 3 ∨ d = 4) ∨
  (N = 60 ∧ (e = 2 ∨ f = 2 ∨ h = 2) ∧
    (e = 3 ∨ f = 3 ∨ h = 3) ∧ (e = 5 ∨ f = 5 ∨ h = 5) ∧
    ∀ d, (d = e ∨ d = f ∨ d = h) → d = 2 ∨ d = 3 ∨ d = 5) := by
  let R : Prop :=
    (∃ n, 2 ≤ n ∧ N = 2 * n ∧ (e = n ∨ f = n ∨ h = n) ∧
      ∀ d, (d = e ∨ d = f ∨ d = h) → d = 2 ∨ d = n) ∨
    (N = 12 ∧ (e = 3 ∨ f = 3 ∨ h = 3) ∧
      ∀ d, (d = e ∨ d = f ∨ d = h) → d = 2 ∨ d = 3) ∨
    (N = 24 ∧ (e = 3 ∨ f = 3 ∨ h = 3) ∧ (e = 4 ∨ f = 4 ∨ h = 4) ∧
      ∀ d, (d = e ∨ d = f ∨ d = h) → d = 2 ∨ d = 3 ∨ d = 4) ∨
    (N = 60 ∧ (e = 2 ∨ f = 2 ∨ h = 2) ∧
      (e = 3 ∨ f = 3 ∨ h = 3) ∧ (e = 5 ∨ f = 5 ∨ h = 5) ∧
      ∀ d, (d = e ∨ d = f ∨ d = h) → d = 2 ∨ d = 3 ∨ d = 5)
  change R
  have finish (u v w : ℕ) (hu : u = e ∨ u = f ∨ u = h)
    (hv : v = e ∨ v = f ∨ v = h) (hw : w = e ∨ w = f ∨ w = h)
    (hmem : ∀ d, (d = e ∨ d = f ∨ d = h) ↔ (d = u ∨ d = v ∨ d = w))
    (hw2 : 2 ≤ w)
    (hs : (u = 2 ∧ v = 2 ∧ N = 2 * w) ∨
      (u = 2 ∧ v = 3 ∧ w = 3 ∧ N = 12) ∨
      (u = 2 ∧ v = 3 ∧ w = 4 ∧ N = 24) ∨
      (u = 2 ∧ v = 3 ∧ w = 5 ∧ N = 60)) : R := by
    have hu' : e = u ∨ f = u ∨ h = u := by
      obtain hu | hu | hu := hu
      · exact Or.inl hu.symm
      · exact Or.inr (Or.inl hu.symm)
      · exact Or.inr (Or.inr hu.symm)
    have hv' : e = v ∨ f = v ∨ h = v := by
      obtain hv | hv | hv := hv
      · exact Or.inl hv.symm
      · exact Or.inr (Or.inl hv.symm)
      · exact Or.inr (Or.inr hv.symm)
    have hw' : e = w ∨ f = w ∨ h = w := by
      obtain hw | hw | hw := hw
      · exact Or.inl hw.symm
      · exact Or.inr (Or.inl hw.symm)
      · exact Or.inr (Or.inr hw.symm)
    obtain hs1 | hs234 := hs
    · obtain ⟨hu2, hv2, hNw⟩ := hs1
      left
      subst u
      subst v
      refine ⟨w, hw2, hNw, hw', ?_⟩
      intro d hd
      obtain hd | hd | hd := (hmem d).mp hd
      · exact Or.inl hd
      · exact Or.inl hd
      · exact Or.inr hd
    · obtain hs2 | hs34 := hs234
      · obtain ⟨hu2, hv3, hw3, hN12⟩ := hs2
        right; left
        subst u
        subst v
        subst w
        refine ⟨hN12, hv', ?_⟩
        intro d hd
        obtain hd | hd | hd := (hmem d).mp hd
        · exact Or.inl hd
        · exact Or.inr hd
        · exact Or.inr hd
      · obtain hs3 | hs4 := hs34
        · obtain ⟨hu2, hv3, hw4, hN24⟩ := hs3
          right; right; left
          subst u
          subst v
          subst w
          refine ⟨hN24, hv', hw', ?_⟩
          intro d hd
          obtain hd | hd | hd := (hmem d).mp hd
          · exact Or.inl hd
          · exact Or.inr (Or.inl hd)
          · exact Or.inr (Or.inr hd)
        · obtain ⟨hu2, hv3, hw5, hN60⟩ := hs4
          right; right; right
          subst u
          subst v
          subst w
          refine ⟨hN60, hu', hv', hw', ?_⟩
          intro d hd
          obtain hd | hd | hd := (hmem d).mp hd
          · exact Or.inl hd
          · exact Or.inr (Or.inl hd)
          · exact Or.inr (Or.inr hd)
  by_cases hef : e ≤ f
  · by_cases hfh : f ≤ h
    · exact finish e f h (by simp) (by simp) (by simp) (by intro d; rfl) hh
      (dickson_orbit_signature_sorted N a b c e f h hN ha hb hc he hef hfh hsum)
    · have hhf : h ≤ f := by omega
      by_cases heh : e ≤ h
      · exact finish e h f (by simp) (by simp) (by simp) (by intro d; tauto) hf
        (dickson_orbit_signature_sorted N a c b e h f hN ha hc hb he heh hhf (by omega))
      · have hhe : h ≤ e := by omega
        exact finish h e f (by simp) (by simp) (by simp) (by intro d; tauto) hf
          (dickson_orbit_signature_sorted N c a b h e f hN hc ha hb hh hhe hef (by omega))
  · have hfe : f ≤ e := by omega
    by_cases heh : e ≤ h
    · exact finish f e h (by simp) (by simp) (by simp) (by intro d; tauto) hh
      (dickson_orbit_signature_sorted N b a c f e h hN hb ha hc hf hfe heh (by omega))
    · have hhe : h ≤ e := by omega
      by_cases hfh : f ≤ h
      · exact finish f h e (by simp) (by simp) (by simp) (by intro d; tauto) he
        (dickson_orbit_signature_sorted N b c a f h e hN hb hc ha hf hfh hhe (by omega))
      · have hhf : h ≤ f := by omega
        exact finish h f e (by simp) (by simp) (by simp) (by intro d; tauto) he
          (dickson_orbit_signature_sorted N c b a h f e hN hc hb ha hh hhf hfe (by omega))

end MetaMathlibExt

namespace MetaMathlibExt

/--
[dickson_dihedral_of_index_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/DicksonPGL2Tame.lean)
-/
@[path]
private lemma dickson_dihedral_of_index_two {G : Type*} [Group G] [Finite G]
  (H : Subgroup G) (hHcyc : IsCyclic H) (hindex : H.index = 2)
  (houtside : ∀ g : G, g ∉ H → g ^ 2 = 1) (hH2 : 2 ≤ Nat.card H) :
  Nonempty (G ≃* DihedralGroup (Nat.card H)) := by
  classical
  let n := Nat.card H
  have hn : 2 ≤ n := hH2
  let _ : NeZero n := ⟨by omega⟩
  let _ : H.Normal := Subgroup.normal_of_index_eq_two hindex
  have hHtop : H ≠ ⊤ := by
    intro h
    rw [h, Subgroup.index_top] at hindex
    omega
  obtain ⟨t, ht⟩ : ∃ t : G, t ∉ H := by
    by_contra h
    push Not at h
    apply hHtop
    exact (Subgroup.eq_top_iff' H).mpr h
  have hquotcard : Nat.card (G ⧸ H) = 2 := by
    rwa [← Subgroup.index_eq_card]
  have hquot_unique : ∃! z : G ⧸ H, z ≠ 1 :=
    (Nat.card_eq_two_iff' 1).mp hquotcard
  have hsame_coset {g : G} (hg : g ∉ H) : (t : G ⧸ H) = (g : G ⧸ H) := by
    apply hquot_unique.unique
    · exact (QuotientGroup.eq_one_iff t).not.mpr ht
    · exact (QuotientGroup.eq_one_iff g).not.mpr hg
  have hdecomp {g : G} (hg : g ∉ H) : t⁻¹ * g ∈ H := by
    rw [← QuotientGroup.eq_one_iff]
    change (t : G ⧸ H)⁻¹ * (g : G ⧸ H) = 1
    rw [hsame_coset hg, inv_mul_cancel]
  have ht2 : t ^ 2 = 1 := houtside t ht
  let eH : Multiplicative (ZMod n) ≃* H := zmodCyclicMulEquiv hHcyc
  let rot (i : ZMod n) : G := (eH (Multiplicative.ofAdd i) : H)
  have hrot_mem (i : ZMod n) : rot i ∈ H := (eH (Multiplicative.ofAdd i)).2
  have hrot_zero : rot 0 = 1 := by
    change ((eH 1 : H) : G) = 1
    rw [map_one]
    rfl
  have hrot_add (i j : ZMod n) : rot (i + j) = rot i * rot j := by
    change ((eH (Multiplicative.ofAdd (i + j)) : H) : G) = _
    rw [show Multiplicative.ofAdd (i + j) =
      Multiplicative.ofAdd i * Multiplicative.ofAdd j from rfl, map_mul]
    rfl
  have hrot_neg (i : ZMod n) : rot (-i) = (rot i)⁻¹ := by
    change ((eH (Multiplicative.ofAdd (-i)) : H) : G) = _
    rw [show Multiplicative.ofAdd (-i) = (Multiplicative.ofAdd i)⁻¹ from rfl, map_inv]
    rfl
  have htrot_not (i : ZMod n) : t * rot i ∉ H := by
    intro h
    apply ht
    have hm := H.mul_mem h (H.inv_mem (hrot_mem i))
    simpa [mul_assoc] using hm
  have htrot2 (i : ZMod n) : (t * rot i) ^ 2 = 1 :=
    houtside (t * rot i) (htrot_not i)
  have hconj (i : ZMod n) : t * rot i * t = rot (-i) := by
    rw [hrot_neg]
    apply eq_inv_of_mul_eq_one_left
    simpa [sq, mul_assoc] using htrot2 i
  have htinv : t⁻¹ = t := by
    have htt : t * t = 1 := by simpa [sq] using ht2
    calc
      t⁻¹ = t⁻¹ * 1 := (mul_one _).symm
      _ = t⁻¹ * (t * t) := by rw [htt]
      _ = t := by simp
  have hcross (i : ZMod n) : rot i * t = t * rot (-i) := by
    calc
      rot i * t = t⁻¹ * (t * rot i * t) := by simp [mul_assoc]
      _ = t * (t * rot i * t) := by rw [htinv]
      _ = t * rot (-i) := by rw [hconj]
  let φ : DihedralGroup n →* G := {
    toFun := fun d => match d with
      | .r i => rot i
      | .sr i => t * rot i
    map_one' := hrot_zero
    map_mul' := by
      intro u v
      cases u with
      | r i =>
        cases v with
        | r j => exact hrot_add i j
        | sr j =>
          change t * rot (j - i) = rot i * (t * rot j)
          symm
          calc
            rot i * (t * rot j) = (rot i * t) * rot j := (mul_assoc ..).symm
            _ = (t * rot (-i)) * rot j := by rw [hcross]
            _ = t * (rot (-i) * rot j) := mul_assoc ..
            _ = t * rot (-i + j) := by rw [hrot_add]
            _ = t * rot (j - i) := by congr 2; abel
      | sr i =>
        cases v with
        | r j =>
          change t * rot (i + j) = (t * rot i) * rot j
          rw [hrot_add, mul_assoc]
        | sr j =>
          change rot (j - i) = (t * rot i) * (t * rot j)
          symm
          calc
            (t * rot i) * (t * rot j) = (t * rot i * t) * rot j :=
              (mul_assoc (t * rot i) t (rot j)).symm
            _ = rot (-i) * rot j := by rw [hconj]
            _ = rot (-i + j) := (hrot_add _ _).symm
            _ = rot (j - i) := by congr 1; abel }
  have hφsurj : Function.Surjective φ := by
    intro g
    by_cases hg : g ∈ H
    · obtain ⟨z, hz⟩ := eH.surjective ⟨g, hg⟩
      refine ⟨DihedralGroup.r z.toAdd, ?_⟩
      change rot z.toAdd = g
      exact congrArg Subtype.val hz
    · have hk := hdecomp hg
      obtain ⟨z, hz⟩ := eH.surjective ⟨t⁻¹ * g, hk⟩
      refine ⟨DihedralGroup.sr z.toAdd, ?_⟩
      change t * rot z.toAdd = g
      have hz' : rot z.toAdd = t⁻¹ * g := congrArg Subtype.val hz
      rw [hz']
      simp
  have hcard : Nat.card (DihedralGroup n) = Nat.card G := by
    rw [DihedralGroup.nat_card, ← H.card_mul_index, hindex]
    omega
  have hφbij : Function.Bijective φ :=
    hφsurj.bijective_of_nat_card_le (by rw [hcard])
  exact ⟨(MulEquiv.ofBijective φ hφbij).symm⟩

end MetaMathlibExt

namespace MetaMathlibExt.Dickson

/--
[dickson_not_dvd_orderOf](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/DicksonPGL2Tame.lean)
-/
@[path]
private lemma dickson_not_dvd_orderOf {p : ℕ} {G : Type*} [Group G] [Finite G]
  (hG_tame : ¬p ∣ Nat.card G) (g : G) : ¬p ∣ orderOf g :=
  fun h ↦ hG_tame (h.trans (orderOf_dvd_natCard g))

end MetaMathlibExt.Dickson

namespace MetaMathlibExt.Dickson

/--
[dickson_mk_eq_one_of_toLin_eq_smul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/DicksonPGL2Tame.lean)
-/
@[path]
private lemma dickson_mk_eq_one_of_toLin_eq_smul {F : Type*} [Field F]
  (A : GL (Fin 2) F) (a : F)
  (h : (↑(Matrix.GeneralLinearGroup.toLin A) : Module.End F (Fin 2 → F)) = a • 1) :
  Matrix.ProjGenLinGroup.mk A = 1 := by
  have hmatrix : (A : Matrix (Fin 2) (Fin 2) F) = Matrix.scalar (Fin 2) a := by
    ext i j
    have hv := LinearMap.congr_fun h (Pi.single j 1)
    by_cases hij : i = j
    · subst j
      simpa [Matrix.GeneralLinearGroup.toLin_apply] using congrFun hv i
    · simpa [Matrix.GeneralLinearGroup.toLin_apply, hij] using congrFun hv i
  have ha : a ≠ 0 := by
    intro ha
    apply A.det_ne_zero
    rw [hmatrix, ha]
    simp
  rw [Matrix.ProjGenLinGroup.mk_eq_one,
    Matrix.GeneralLinearGroup.center_eq_range_scalar]
  exact ⟨Units.mk0 a ha, by ext i j; simp [hmatrix]⟩

end MetaMathlibExt.Dickson

namespace MetaMathlibExt.Dickson

/--
[dickson_exists_two_eigenvalues](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/DicksonPGL2Tame.lean)
-/
@[path]
private lemma dickson_exists_two_eigenvalues
  {F V : Type*} [Field F] [IsAlgClosed F] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] [Nontrivial V] (f : Module.End F V)
  (hf : f.IsSemisimple) (hnonscalar : ∀ a : F, f ≠ a • 1) :
  ∃ a b : F, a ≠ b ∧ f.HasEigenvalue a ∧ f.HasEigenvalue b := by
  obtain ⟨a, ha⟩ := Module.End.exists_eigenvalue f
  by_cases hex : ∃ b : F, b ≠ a ∧ f.HasEigenvalue b
  · obtain ⟨b, hba, hb⟩ := hex
    exact ⟨a, b, hba.symm, ha, hb⟩
  · push Not at hex
    have hea : f.eigenspace a = ⊤ := by
      rw [← hf.iSup_eigenspace_eq_top]
      apply le_antisymm (le_iSup (fun b : F => f.eigenspace b) a)
      refine iSup_le fun b => ?_
      by_cases hba : b = a
      · subst b
        exact le_rfl
      · have hb : ¬f.HasEigenvalue b := hex b hba
        have : f.eigenspace b = ⊥ :=
          not_ne_iff.mp (Module.End.hasEigenvalue_iff.not.mp hb)
        simp [this]
    exfalso
    apply hnonscalar a
    rw [← sub_eq_zero]
    have hker : (f - a • 1).ker = ⊤ := by
      simpa only [Module.End.eigenspace_def] using hea
    exact LinearMap.ker_eq_top.mp hker

end MetaMathlibExt.Dickson

namespace MetaMathlibExt.Dickson

/--
[dickson_finrank_eigenspace_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/DicksonPGL2Tame.lean)
-/
@[path]
private lemma dickson_finrank_eigenspace_eq_one
  {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] (f : Module.End F V) (hdim : Module.finrank F V = 2)
  (hnonscalar : ∀ a : F, f ≠ a • 1) {a : F} (ha : f.HasEigenvalue a) :
  Module.finrank F (f.eigenspace a) = 1 := by
  have hge : 1 ≤ Module.finrank F (f.eigenspace a) :=
    Submodule.one_le_finrank_iff.mpr (Module.End.hasEigenvalue_iff.mp ha)
  have hle : Module.finrank F (f.eigenspace a) ≤ 2 :=
    hdim ▸ Submodule.finrank_le (f.eigenspace a)
  have hne : Module.finrank F (f.eigenspace a) ≠ 2 := by
    intro heq
    have htop : f.eigenspace a = ⊤ :=
      Submodule.eq_top_of_finrank_eq (heq.trans hdim.symm)
    apply hnonscalar a
    rw [← sub_eq_zero]
    have hker : (f - a • 1).ker = ⊤ := by
      simpa only [Module.End.eigenspace_def] using htop
    exact LinearMap.ker_eq_top.mp hker
  omega

end MetaMathlibExt.Dickson

namespace MetaMathlibExt.Dickson

/--
[dickson_fixed_hasEigenvector](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/DicksonPGL2Tame.lean)
-/
@[path]
private lemma dickson_fixed_hasEigenvector {F : Type*} [Field F]
  (A : GL (Fin 2) F)
  (x : MulAction.fixedBy (Projectivization F (Fin 2 → F))
    (Matrix.ProjGenLinGroup.mk A)) :
  ∃ a : F, Module.End.HasEigenvector
    (↑(Matrix.GeneralLinearGroup.toLin A) : Module.End F (Fin 2 → F)) a x.1.rep := by
  have hp := MulAction.mem_fixedBy.mp x.2
  rw [← Projectivization.mk_rep x.1] at hp
  rw [Projectivization.PGL.mk_smul_mk] at hp
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff F _ _ _ _).mp hp
  refine ⟨a, Module.End.hasEigenvector_iff.mpr ⟨?_, x.1.rep_nonzero⟩⟩
  rw [Module.End.mem_eigenspace_iff]
  simpa [Matrix.GeneralLinearGroup.toLin_apply, Units.smul_def,
    Matrix.smul_eq_mulVec] using ha.symm

end MetaMathlibExt.Dickson

namespace MetaMathlibExt.Dickson

/--
[dickson_card_fixedBy_mk](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/DicksonPGL2Tame.lean)
-/
@[path]
private lemma dickson_card_fixedBy_mk {F : Type*} [Field F] [IsAlgClosed F]
  (A : GL (Fin 2) F) (hne : Matrix.ProjGenLinGroup.mk A ≠ 1)
  (hsemi : Module.End.IsSemisimple
    (↑(Matrix.GeneralLinearGroup.toLin A) : Module.End F (Fin 2 → F))) :
  Nat.card (MulAction.fixedBy (Projectivization F (Fin 2 → F))
    (Matrix.ProjGenLinGroup.mk A)) = 2 := by
  let f : Module.End F (Fin 2 → F) := Matrix.GeneralLinearGroup.toLin A
  have hnonscalar : ∀ a : F, f ≠ a • 1 := fun a ha =>
    hne (dickson_mk_eq_one_of_toLin_eq_smul A a ha)
  let E := {a : F // f.HasEigenvalue a}
  let ev : MulAction.fixedBy (Projectivization F (Fin 2 → F))
    (Matrix.ProjGenLinGroup.mk A) → E := fun x =>
    ⟨Classical.choose (dickson_fixed_hasEigenvector A x),
      Module.End.hasEigenvalue_of_hasEigenvector
        (Classical.choose_spec (dickson_fixed_hasEigenvector A x))⟩
  have hev (x) : f.HasEigenvector (ev x).1 x.1.rep := by
    exact Classical.choose_spec (dickson_fixed_hasEigenvector A x)
  have hinj : Function.Injective ev := by
    intro x y hxy
    apply Subtype.ext
    apply Projectivization.submodule_injective
    have hxle : x.1.submodule ≤ f.eigenspace (ev x).1 := by
      rw [← Projectivization.mk_rep x.1, Projectivization.submodule_mk,
        Submodule.span_singleton_le_iff_mem]
      exact (Module.End.hasEigenvector_iff.mp (hev x)).1
    have hyle : y.1.submodule ≤ f.eigenspace (ev y).1 := by
      rw [← Projectivization.mk_rep y.1, Projectivization.submodule_mk,
        Submodule.span_singleton_le_iff_mem]
      exact (Module.End.hasEigenvector_iff.mp (hev y)).1
    have hxeq : x.1.submodule = f.eigenspace (ev x).1 :=
      Submodule.eq_of_le_of_finrank_eq hxle <| by
        rw [Projectivization.finrank_submodule]
        exact (dickson_finrank_eigenspace_eq_one f (Module.finrank_fin_fun F)
          hnonscalar (ev x).2).symm
    have hyeq : y.1.submodule = f.eigenspace (ev y).1 :=
      Submodule.eq_of_le_of_finrank_eq hyle <| by
        rw [Projectivization.finrank_submodule]
        exact (dickson_finrank_eigenspace_eq_one f (Module.finrank_fin_fun F)
          hnonscalar (ev y).2).symm
    exact hxeq.trans <| (congrArg (fun z : E => f.eigenspace z.1) hxy).trans hyeq.symm
  let vec : E → Fin 2 → F := fun a =>
    Classical.choose (Module.End.HasEigenvalue.exists_hasEigenvector a.2)
  have hvec (a : E) : f.HasEigenvector a.1 (vec a) :=
    Classical.choose_spec (Module.End.HasEigenvalue.exists_hasEigenvector a.2)
  have hlin : LinearIndependent F vec :=
    f.eigenvectors_linearIndependent {a : F | f.HasEigenvalue a} vec hvec
  let _ : Finite E := hlin.finite
  let _ : Finite (MulAction.fixedBy (Projectivization F (Fin 2 → F))
    (Matrix.ProjGenLinGroup.mk A)) := Finite.of_injective ev hinj
  let _ := Fintype.ofFinite E
  have hE : Nat.card E ≤ 2 := by
    rw [Nat.card_eq_fintype_card]
    simpa only [Module.finrank_fin_fun] using hlin.fintype_card_le_finrank
  have hle := Nat.card_le_card_of_injective ev hinj
  obtain ⟨a, b, hab, ha, hb⟩ :=
    dickson_exists_two_eigenvalues f hsemi hnonscalar
  obtain ⟨v, hv⟩ := ha.exists_hasEigenvector
  obtain ⟨w, hw⟩ := hb.exists_hasEigenvector
  have ha0 : a ≠ 0 := by
    intro ha0
    apply hv.2
    apply (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv.injective
    simpa [f, ha0] using hv.apply_eq_smul
  have hb0 : b ≠ 0 := by
    intro hb0
    apply hw.2
    apply (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv.injective
    simpa [f, hb0] using hw.apply_eq_smul
  have vfix : Projectivization.mk F v hv.2 ∈
    MulAction.fixedBy (Projectivization F (Fin 2 → F))
      (Matrix.ProjGenLinGroup.mk A) := by
    rw [MulAction.mem_fixedBy, Projectivization.PGL.mk_smul_mk,
      Projectivization.mk_eq_mk_iff]
    exact ⟨Units.mk0 a ha0, by
      simpa [f, Matrix.GeneralLinearGroup.toLin_apply, Units.smul_def,
        Matrix.smul_eq_mulVec] using hv.apply_eq_smul.symm⟩
  have wfix : Projectivization.mk F w hw.2 ∈
    MulAction.fixedBy (Projectivization F (Fin 2 → F))
      (Matrix.ProjGenLinGroup.mk A) := by
    rw [MulAction.mem_fixedBy, Projectivization.PGL.mk_smul_mk,
      Projectivization.mk_eq_mk_iff]
    exact ⟨Units.mk0 b hb0, by
      simpa [f, Matrix.GeneralLinearGroup.toLin_apply, Units.smul_def,
        Matrix.smul_eq_mulVec] using hw.apply_eq_smul.symm⟩
  let xv : MulAction.fixedBy (Projectivization F (Fin 2 → F))
    (Matrix.ProjGenLinGroup.mk A) := ⟨Projectivization.mk F v hv.2, vfix⟩
  let xw : MulAction.fixedBy (Projectivization F (Fin 2 → F))
    (Matrix.ProjGenLinGroup.mk A) := ⟨Projectivization.mk F w hw.2, wfix⟩
  have hxvw : xv ≠ xw := by
    intro heq
    have hp : Projectivization.mk F v hv.2 =
      Projectivization.mk F w hw.2 := congrArg Subtype.val heq
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff F _ _ _ _).mp hp
    have hcval : (c : F) • w = v := by simpa [Units.smul_def] using hc
    have hscalar : (c : F) * b = a * (c : F) :=
      (smul_left_injective F hw.2) <| by
        calc
          ((c : F) * b) • w = (c : F) • f w := by rw [hw.apply_eq_smul, mul_smul]
          _ = f ((c : F) • w) := (f.map_smul (c : F) w).symm
          _ = f v := by rw [hcval]
          _ = a • v := hv.apply_eq_smul
          _ = (a * (c : F)) • w := by rw [← hcval, mul_smul]
    apply hab
    apply (mul_left_cancel₀ c.ne_zero)
    calc
      (c : F) * a = a * c := mul_comm _ _
      _ = (c : F) * b := hscalar.symm
  let pair : Fin 2 → MulAction.fixedBy (Projectivization F (Fin 2 → F))
    (Matrix.ProjGenLinGroup.mk A) := ![xv, xw]
  have hpair : Function.Injective pair := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [pair]
  have hge := Nat.card_le_card_of_injective pair hpair
  simp only [Nat.card_fin] at hge
  omega

end MetaMathlibExt.Dickson

namespace MetaMathlibExt.Dickson

variable (p : ℕ) [Fact (Nat.Prime p)]
/--
[dickson_lift_isSemisimple](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/DicksonPGL2Tame.lean)
-/
@[path]
private lemma dickson_lift_isSemisimple (A : GL (Fin 2) (K p)) (m : ℕ)
  (hm : (Matrix.ProjGenLinGroup.mk A) ^ m = 1) (hpm : ¬p ∣ m) :
  Module.End.IsSemisimple
    (↑(Matrix.GeneralLinearGroup.toLin A) : Module.End (K p) (Fin 2 → K p)) := by
  have hcenter : A ^ m ∈ Subgroup.center (GL (Fin 2) (K p)) := by
    rw [← Matrix.ProjGenLinGroup.mk_eq_one]
    simpa only [map_pow] using hm
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hcenter
  obtain ⟨u, hu⟩ := hcenter
  let f : Module.End (K p) (Fin 2 → K p) :=
    (Matrix.GeneralLinearGroup.toLin A :
      LinearMap.GeneralLinearGroup (K p) (Fin 2 → K p))
  change f.IsSemisimple
  have hpow : f ^ m = algebraMap (K p) (Module.End (K p) (Fin 2 → K p)) u.1 := by
    apply LinearMap.ext
    intro v
    funext i
    change ((↑((Matrix.GeneralLinearGroup.toLin A) ^ m) :
      Module.End (K p) (Fin 2 → K p)) v) i = _
    rw [← map_pow, ← hu]
    simp
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (Polynomial.separable_X_pow_sub_C u.1
      ((CharP.cast_eq_zero_iff (K p) p m).not.mpr hpm) u.ne_zero).squarefree
  simp [hpow]

end MetaMathlibExt.Dickson

namespace MetaMathlibExt.Dickson

variable (p : ℕ) [Fact (Nat.Prime p)]
/--
[dickson_card_fixedBy](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/DicksonPGL2Tame.lean)
-/
@[path]
private lemma dickson_card_fixedBy (g : PGL p) (hg : g ≠ 1)
  (hpg : ¬p ∣ orderOf g) :
  Nat.card (MulAction.fixedBy (Projectivization (K p) (Fin 2 → K p)) g) = 2 := by
  obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  apply dickson_card_fixedBy_mk A hg
  exact dickson_lift_isSemisimple p A (orderOf (Matrix.ProjGenLinGroup.mk A))
    (pow_orderOf_eq_one _) hpg

end MetaMathlibExt.Dickson

namespace MetaMathlibExt.Dickson

variable (p : ℕ) [Fact (Nat.Prime p)]
/--
[dickson_card_fixedBy_subgroup](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/DicksonPGL2Tame.lean)
-/
@[path]
private lemma dickson_card_fixedBy_subgroup (G : Subgroup (PGL p)) [Finite G]
  (hG_tame : ¬p ∣ Nat.card G) (g : G) (hg : g ≠ 1) :
  Nat.card (MulAction.fixedBy (Projectivization (K p) (Fin 2 → K p)) g) = 2 := by
  change Nat.card (MulAction.fixedBy (Projectivization (K p) (Fin 2 → K p))
    (g : PGL p)) = 2
  apply dickson_card_fixedBy p g (by simpa using hg)
  simpa only [Subgroup.orderOf_coe] using dickson_not_dvd_orderOf hG_tame g

end MetaMathlibExt.Dickson

namespace MetaMathlibExt.Dickson

variable (p : ℕ) [Fact (Nat.Prime p)]
/--
[dickson_card_orbits_exceptional](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/DicksonPGL2Tame.lean)
-/
@[path]
private lemma dickson_card_orbits_exceptional (G : Subgroup (PGL p)) [Finite G]
  (hG_tame : ¬p ∣ Nat.card G) (hG_nontrivial : Nontrivial G) :
  let X := Projectivization (K p) (Fin 2 → K p)
  let E := dicksonExceptional G X
  Nat.card (MulAction.orbitRel.Quotient G E) = 2 ∨
    Nat.card (MulAction.orbitRel.Quotient G E) = 3 := by
  let X := Projectivization (K p) (Fin 2 → K p)
  let E := dicksonExceptional G X
  have hfixed (g : G) (hg : g ≠ 1) :
    Nat.card (MulAction.fixedBy X g) = 2 :=
    dickson_card_fixedBy_subgroup p G hG_tame g hg
  let _ : Finite E := dicksonExceptional_finite hfixed
  have hfixedE (g : G) (hg : g ≠ 1) :
    Nat.card (MulAction.fixedBy E g) = 2 := by
    rw [Nat.card_congr (dickson_fixedByExceptionalEquiv g hg)]
    exact hfixed g hg
  have hcount := MulAction.card_add_mul_card_sub_one_eq_card_orbits_mul_card
    G E 2 hfixedE
  apply dickson_orbit_count_cases (Nat.card G) (Nat.card E)
    (Nat.card (MulAction.orbitRel.Quotient G E))
  · have := Finite.one_lt_card (α := G)
    omega
  · exact hcount
  · apply dickson_two_mul_card_le_orbits_mul_card
    intro x
    obtain ⟨g, hg, hfixg⟩ := x.2
    exact ⟨⟨⟨1, by simp⟩, ⟨g, Subtype.ext hfixg⟩, by
      intro h
      apply hg
      exact (congrArg Subtype.val h).symm⟩⟩
  · exact Nat.card_le_card_of_surjective Quotient.mk'' Quotient.mk_surjective

end MetaMathlibExt.Dickson

namespace MetaMathlibExt.Dickson

variable (p : ℕ) [Fact (Nat.Prime p)]
/--
[dickson_exceptional_signature](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/DicksonPGL2Tame.lean)
-/
@[path]
private lemma dickson_exceptional_signature
  (G : Subgroup (PGL p)) [Finite G] (hG_tame : ¬p ∣ Nat.card G)
  (hG_nontrivial : Nontrivial G)
  (horbits :
    let X := Projectivization (K p) (Fin 2 → K p)
    let E := dicksonExceptional G X
    Nat.card (MulAction.orbitRel.Quotient G E) = 3) :
  let X := Projectivization (K p) (Fin 2 → K p)
  let E := dicksonExceptional G X
  (∃ n, 2 ≤ n ∧ Nat.card G = 2 * n ∧
    (∃ x : E, Nat.card (MulAction.stabilizer G x) = n) ∧
    ∀ x : E, Nat.card (MulAction.stabilizer G x) = 2 ∨
      Nat.card (MulAction.stabilizer G x) = n) ∨
  (Nat.card G = 12 ∧ (∃ x : E, Nat.card (MulAction.stabilizer G x) = 3) ∧
    ∀ x : E, Nat.card (MulAction.stabilizer G x) = 2 ∨
      Nat.card (MulAction.stabilizer G x) = 3) ∨
  (Nat.card G = 24 ∧
    (∃ x : E, Nat.card (MulAction.stabilizer G x) = 3) ∧
    (∃ x : E, Nat.card (MulAction.stabilizer G x) = 4) ∧
    ∀ x : E, Nat.card (MulAction.stabilizer G x) = 2 ∨
      Nat.card (MulAction.stabilizer G x) = 3 ∨
      Nat.card (MulAction.stabilizer G x) = 4) ∨
  (Nat.card G = 60 ∧
    (∃ x : E, Nat.card (MulAction.stabilizer G x) = 2) ∧
    (∃ x : E, Nat.card (MulAction.stabilizer G x) = 3) ∧
    (∃ x : E, Nat.card (MulAction.stabilizer G x) = 5) ∧
    ∀ x : E, Nat.card (MulAction.stabilizer G x) = 2 ∨
      Nat.card (MulAction.stabilizer G x) = 3 ∨
      Nat.card (MulAction.stabilizer G x) = 5) := by
  classical
  let X := Projectivization (K p) (Fin 2 → K p)
  let E := dicksonExceptional G X
  let Ω := MulAction.orbitRel.Quotient G E
  have hfixed (g : G) (hg : g ≠ 1) :
    Nat.card (MulAction.fixedBy X g) = 2 :=
    dickson_card_fixedBy_subgroup p G hG_tame g hg
  let _ : Finite E := dicksonExceptional_finite hfixed
  have hfixedE (g : G) (hg : g ≠ 1) :
    Nat.card (MulAction.fixedBy E g) = 2 := by
    rw [Nat.card_congr (dickson_fixedByExceptionalEquiv g hg)]
    exact hfixed g hg
  have hcount := MulAction.card_add_mul_card_sub_one_eq_card_orbits_mul_card
    G E 2 hfixedE
  have hN : 2 ≤ Nat.card G := by
    have := Finite.one_lt_card (α := G)
    omega
  have hE : Nat.card E = Nat.card G + 2 := by
    rw [horbits] at hcount
    omega
  let _ := Fintype.ofFinite G
  let _ := Fintype.ofFinite E
  let _ := Fintype.ofFinite Ω
  let _ : (x : E) → Fintype (MulAction.stabilizer G x) :=
    fun x => Fintype.ofFinite (MulAction.stabilizer G x)
  have hclass : Nat.card E =
    ∑ ω : Ω, Nat.card G / Nat.card (MulAction.stabilizer G ω.out) := by
    simpa only [Nat.card_eq_fintype_card] using
      MulAction.card_eq_sum_card_group_div_card_stabilizer G E
  have hΩ : Fintype.card Ω = 3 := by
    simpa only [Nat.card_eq_fintype_card] using horbits
  let q : Ω ≃ Fin 3 := Fintype.equivFinOfCardEq hΩ
  let x0 : E := (q.symm 0).out
  let x1 : E := (q.symm 1).out
  let x2 : E := (q.symm 2).out
  let e0 := Nat.card (MulAction.stabilizer G x0)
  let e1 := Nat.card (MulAction.stabilizer G x1)
  let e2 := Nat.card (MulAction.stabilizer G x2)
  let a0 := Nat.card G / e0
  let a1 := Nat.card G / e1
  let a2 := Nat.card G / e2
  have hstab2 (x : E) : 2 ≤ Nat.card (MulAction.stabilizer G x) := by
    obtain ⟨g, hg, hfixg⟩ := x.2
    let _ : Nontrivial (MulAction.stabilizer G x) :=
      ⟨⟨⟨1, by simp⟩, ⟨g, Subtype.ext hfixg⟩, by
        intro h
        apply hg
        exact (congrArg Subtype.val h).symm⟩⟩
    have := Finite.one_lt_card (α := MulAction.stabilizer G x)
    omega
  have hprod (x : E) :
    (Nat.card G / Nat.card (MulAction.stabilizer G x)) *
      Nat.card (MulAction.stabilizer G x) = Nat.card G :=
    Nat.div_mul_cancel (Subgroup.card_subgroup_dvd_card (MulAction.stabilizer G x))
  have hsum : a0 + a1 + a2 = Nat.card G + 2 := by
    rw [← hE, hclass]
    change (Nat.card G / Nat.card (MulAction.stabilizer G (q.symm 0).out)) +
      (Nat.card G / Nat.card (MulAction.stabilizer G (q.symm 1).out)) +
      (Nat.card G / Nat.card (MulAction.stabilizer G (q.symm 2).out)) = _
    rw [← q.symm.sum_comp, Fin.sum_univ_three]
  have hsignature := dickson_orbit_signature (Nat.card G) a0 a1 a2 e0 e1 e2 hN
    (hprod x0) (hprod x1) (hprod x2) (hstab2 x0) (hstab2 x1) (hstab2 x2) hsum
  have hcard_mem (x : E) : Nat.card (MulAction.stabilizer G x) = e0 ∨
    Nat.card (MulAction.stabilizer G x) = e1 ∨
    Nat.card (MulAction.stabilizer G x) = e2 := by
    let i : Fin 3 := q (Quotient.mk'' x)
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by
      omega
    change q (Quotient.mk'' x) = 0 ∨ q (Quotient.mk'' x) = 1 ∨
      q (Quotient.mk'' x) = 2 at hi
    obtain hi | hi | hi := hi
    · left
      apply dickson_card_stabilizer_eq_of_quotient_eq x x0
      have hq : Quotient.mk'' x = q.symm 0 := q.injective (by simpa using hi)
      simpa [x0] using hq
    · right; left
      apply dickson_card_stabilizer_eq_of_quotient_eq x x1
      have hq : Quotient.mk'' x = q.symm 1 := q.injective (by simpa using hi)
      simpa [x1] using hq
    · right; right
      apply dickson_card_stabilizer_eq_of_quotient_eq x x2
      have hq : Quotient.mk'' x = q.symm 2 := q.injective (by simpa using hi)
      simpa [x2] using hq
  obtain hs1 | hs234 := hsignature
  · obtain ⟨n, hn, hGn, he, hall⟩ := hs1
    left
    refine ⟨n, hn, hGn, ?_, fun x => hall _ (hcard_mem x)⟩
    obtain he | he | he := he
    · exact ⟨x0, he⟩
    · exact ⟨x1, he⟩
    · exact ⟨x2, he⟩
  · obtain hs2 | hs34 := hs234
    · obtain ⟨hG12, he, hall⟩ := hs2
      right; left
      refine ⟨hG12, ?_, fun x => hall _ (hcard_mem x)⟩
      obtain he | he | he := he
      · exact ⟨x0, he⟩
      · exact ⟨x1, he⟩
      · exact ⟨x2, he⟩
    · obtain hs3 | hs4 := hs34
      · obtain ⟨hG24, he3, he4, hall⟩ := hs3
        right; right; left
        refine ⟨hG24, ?_, ?_, fun x => hall _ (hcard_mem x)⟩
        · obtain he | he | he := he3
          · exact ⟨x0, he⟩
          · exact ⟨x1, he⟩
          · exact ⟨x2, he⟩
        · obtain he | he | he := he4
          · exact ⟨x0, he⟩
          · exact ⟨x1, he⟩
          · exact ⟨x2, he⟩
      · obtain ⟨hG60, he2, he3, he5, hall⟩ := hs4
        right; right; right
        refine ⟨hG60, ?_, ?_, ?_, fun x => hall _ (hcard_mem x)⟩
        · obtain he | he | he := he2
          · exact ⟨x0, he⟩
          · exact ⟨x1, he⟩
          · exact ⟨x2, he⟩
        · obtain he | he | he := he3
          · exact ⟨x0, he⟩
          · exact ⟨x1, he⟩
          · exact ⟨x2, he⟩
        · obtain he | he | he := he5
          · exact ⟨x0, he⟩
          · exact ⟨x1, he⟩
          · exact ⟨x2, he⟩
end MetaMathlibExt.Dickson

namespace MetaMathlibExt.Dickson

variable (p : ℕ) [Fact (Nat.Prime p)]
/--
[dickson_isAlternatingFour](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/DicksonPGL2Tame.lean)
-/
@[path]
private lemma dickson_isAlternatingFour
  (G : Subgroup (PGL p)) [Finite G] (hG_tame : ¬p ∣ Nat.card G)
  (hG12 : Nat.card G = 12)
  (x : dicksonExceptional G (Projectivization (K p) (Fin 2 → K p)))
  (hstab3 : Nat.card (MulAction.stabilizer G x) = 3) :
  Nonempty (G ≃* alternatingGroup (Fin 4)) := by
  classical
  let X := Projectivization (K p) (Fin 2 → K p)
  let E := dicksonExceptional G X
  let O := MulAction.orbit G x
  have hfixed (g : G) (hg : g ≠ 1) :
    Nat.card (MulAction.fixedBy X g) = 2 :=
    dickson_card_fixedBy_subgroup p G hG_tame g hg
  let _ : Finite E := dicksonExceptional_finite hfixed
  have hfixedE (g : G) (hg : g ≠ 1) :
    Nat.card (MulAction.fixedBy E g) = 2 := by
    rw [Nat.card_congr (dickson_fixedByExceptionalEquiv g hg)]
    exact hfixed g hg
  let _ := Fintype.ofFinite G
  let _ := Fintype.ofFinite O
  let _ := Fintype.ofFinite (MulAction.stabilizer G x)
  have hprod : Nat.card O * Nat.card (MulAction.stabilizer G x) = Nat.card G := by
    simpa only [Nat.card_eq_fintype_card] using
      MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := G) x
  have hO : Nat.card O = 4 := by
    rw [hstab3, hG12] at hprod
    omega
  have hρinj : Function.Injective (MulAction.toPermHom G O) :=
    dickson_orbitPerm_injective G E hfixedE x (hO ▸ by decide)
  have hOFintype : Fintype.card O = 4 := by
    simpa only [Nat.card_eq_fintype_card] using hO
  let q : O ≃ Fin 4 := Fintype.equivFinOfCardEq hOFintype
  let σ : G →* Equiv.Perm (Fin 4) :=
    q.permCongrHom.toMonoidHom.comp (MulAction.toPermHom G O)
  have hσinj : Function.Injective σ := q.permCongrHom.injective.comp hρinj
  have hrange_card : Nat.card σ.range = 12 := by
    calc
      Nat.card σ.range = Nat.card G := (Nat.card_congr (MonoidHom.ofInjective hσinj)).symm
      _ = 12 := hG12
  have hindex : σ.range.index = 2 := by
    rw [Subgroup.index_eq_card_div, Nat.card_perm, Nat.card_fin, hrange_card]
    norm_num [Nat.factorial]
  have hrange : σ.range = alternatingGroup (Fin 4) :=
    Equiv.Perm.eq_alternatingGroup_of_index_eq_two hindex
  let eG : G ≃* σ.range := MonoidHom.ofInjective hσinj
  rw [hrange] at eG
  exact ⟨eG⟩

end MetaMathlibExt.Dickson

namespace MetaMathlibExt.Dickson

variable (p : ℕ) [Fact (Nat.Prime p)]
/--
[dickson_same_orbit_of_stabilizer_card_two](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/DicksonPGL2Tame.lean)
-/
@[path]
private lemma dickson_same_orbit_of_stabilizer_card_two
  {G X : Type*} [Group G] [MulAction G X] [Finite G]
  (x₂ x₃ x₅ : dicksonExceptional G X)
  (h₂ : Nat.card (MulAction.stabilizer G x₂) = 2)
  (h₃ : Nat.card (MulAction.stabilizer G x₃) = 3)
  (h₅ : Nat.card (MulAction.stabilizer G x₅) = 5)
  (horbits : Nat.card
    (MulAction.orbitRel.Quotient G (dicksonExceptional G X)) = 3)
  {x y : dicksonExceptional G X}
  (hx : Nat.card (MulAction.stabilizer G x) = 2)
  (hy : Nat.card (MulAction.stabilizer G y) = 2) :
  Quotient.mk'' x = (Quotient.mk'' y :
    MulAction.orbitRel.Quotient G (dicksonExceptional G X)) := by
  classical
  let E := dicksonExceptional G X
  let Ω := MulAction.orbitRel.Quotient G E
  have h₂₃ : (Quotient.mk'' x₂ : Ω) ≠ Quotient.mk'' x₃ := by
    intro h
    have hc := dickson_card_stabilizer_eq_of_quotient_eq x₂ x₃ h
    omega
  have h₂₅ : (Quotient.mk'' x₂ : Ω) ≠ Quotient.mk'' x₅ := by
    intro h
    have hc := dickson_card_stabilizer_eq_of_quotient_eq x₂ x₅ h
    omega
  have h₃₅ : (Quotient.mk'' x₃ : Ω) ≠ Quotient.mk'' x₅ := by
    intro h
    have hc := dickson_card_stabilizer_eq_of_quotient_eq x₃ x₅ h
    omega
  let reps : Fin 3 → Ω := ![Quotient.mk'' x₂, Quotient.mk'' x₃, Quotient.mk'' x₅]
  have hreps_inj : Function.Injective reps := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [reps]
  let _ : Finite Ω := Nat.finite_of_card_ne_zero (by rw [horbits]; decide)
  have hΩ : Nat.card Ω = 3 := by simpa [Ω, E] using horbits
  have hreps_bij : Function.Bijective reps :=
    hreps_inj.bijective_of_nat_card_le (by rw [hΩ, Nat.card_fin])
  have hx₂ : (Quotient.mk'' x : Ω) = Quotient.mk'' x₂ := by
    obtain ⟨i, hi⟩ := hreps_bij.2 (Quotient.mk'' x)
    fin_cases i
    · simpa [reps] using hi.symm
    · have hc := dickson_card_stabilizer_eq_of_quotient_eq x₃ x (by simpa [reps] using hi)
      omega
    · have hc := dickson_card_stabilizer_eq_of_quotient_eq x₅ x (by simpa [reps] using hi)
      omega
  have hy₂ : (Quotient.mk'' y : Ω) = Quotient.mk'' x₂ := by
    obtain ⟨i, hi⟩ := hreps_bij.2 (Quotient.mk'' y)
    fin_cases i
    · simpa [reps] using hi.symm
    · have hc := dickson_card_stabilizer_eq_of_quotient_eq x₃ y (by simpa [reps] using hi)
      omega
    · have hc := dickson_card_stabilizer_eq_of_quotient_eq x₅ y (by simpa [reps] using hi)
      omega
  exact hx₂.trans hy₂.symm

end MetaMathlibExt.Dickson

namespace MetaMathlibExt.Dickson

variable (p : ℕ) [Fact (Nat.Prime p)]
/--
[dickson_card_centralizer_le_four](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/DicksonPGL2Tame.lean)
-/
@[path]
private lemma dickson_card_centralizer_le_four
  (G : Subgroup (PGL p)) [Finite G] (hG_tame : ¬p ∣ Nat.card G)
  (hall : ∀ x : dicksonExceptional G (Projectivization (K p) (Fin 2 → K p)),
    Nat.card (MulAction.stabilizer G x) = 2 ∨
    Nat.card (MulAction.stabilizer G x) = 3 ∨
    Nat.card (MulAction.stabilizer G x) = 5)
  (t : G) (ht : orderOf t = 2) :
  Nat.card (Subgroup.centralizer ({t} : Set G)) ≤ 4 := by
  classical
  let X := Projectivization (K p) (Fin 2 → K p)
  let E := dicksonExceptional G X
  let F := MulAction.fixedBy X t
  have ht1 : t ≠ 1 := by intro h; simp_all
  have hF : Nat.card F = 2 := dickson_card_fixedBy_subgroup p G hG_tame t ht1
  have hFdata : Nonempty F ∧ Finite F := Nat.card_pos_iff.mp (by rw [hF]; decide)
  let _ : Finite F := hFdata.2
  let xF : F := Classical.choice hFdata.1
  have htfix : t • xF.1 = xF.1 := MulAction.mem_fixedBy.mp xF.2
  let xE : E := ⟨xF.1, ⟨t, ht1, htfix⟩⟩
  have htmem : t ∈ MulAction.stabilizer G xE := by
    exact Subtype.ext htfix
  have htdiv := Subgroup.orderOf_dvd_natCard (MulAction.stabilizer G xE) htmem
  have hstabx : Nat.card (MulAction.stabilizer G xE) = 2 := by
    obtain h | h | h := hall xE
    · exact h
    · rw [h, ht] at htdiv
      norm_num at htdiv
    · rw [h, ht] at htdiv
      norm_num at htdiv
  let C := Subgroup.centralizer ({t} : Set G)
  let O := MulAction.orbit C xF.1
  have horbit_fixed (y : X) (hy : y ∈ O) : t • y = y := by
    obtain ⟨c, hc⟩ := hy
    have hcomm : t * (c : G) = (c : G) * t :=
      (Subgroup.mem_centralizer_iff.mp c.2) t (Set.mem_singleton t)
    have hfix : t • ((c : G) • xF.1) = (c : G) • xF.1 := by
      calc
        t • ((c : G) • xF.1) = (t * (c : G)) • xF.1 :=
          (mul_smul t (c : G) xF.1).symm
        _ = ((c : G) * t) • xF.1 := by rw [hcomm]
        _ = (c : G) • (t • xF.1) := mul_smul (c : G) t xF.1
        _ = (c : G) • xF.1 := by rw [htfix]
    rwa [← hc]
  let f : O → F := fun y => ⟨y.1, MulAction.mem_fixedBy.mpr (horbit_fixed y.1 y.2)⟩
  have hfinj : Function.Injective f := by
    intro y z h
    apply Subtype.ext
    exact congrArg (fun w : F => w.1) h
  have hO : Nat.card O ≤ 2 := by
    rw [← hF]
    exact Nat.card_le_card_of_injective f hfinj
  let S := MulAction.stabilizer C xF.1
  let j : S → MulAction.stabilizer G xE := fun c => ⟨c.1.1, by
    exact Subtype.ext c.2⟩
  have hjinj : Function.Injective j := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : MulAction.stabilizer G xE => z.1) h
  have hS : Nat.card S ≤ 2 := by
    calc
      Nat.card S ≤ Nat.card (MulAction.stabilizer G xE) :=
        Nat.card_le_card_of_injective j hjinj
      _ = 2 := hstabx
  let orbitMap : C → O := fun c => ⟨c • xF.1, MulAction.mem_orbit_iff.mpr ⟨c, rfl⟩⟩
  have horbitMap : Function.Surjective orbitMap := by
    intro y
    obtain ⟨c, hc⟩ := y.2
    refine ⟨c, Subtype.ext ?_⟩
    exact hc
  let _ : Finite O := Finite.of_surjective orbitMap horbitMap
  let _ := Fintype.ofFinite C
  let _ := Fintype.ofFinite O
  let _ := Fintype.ofFinite S
  have hprod : Nat.card O * Nat.card S = Nat.card C := by
    simpa only [Nat.card_eq_fintype_card] using
      MulAction.card_orbit_mul_card_stabilizer_eq_card_group C xF.1
  nlinarith

end MetaMathlibExt.Dickson

namespace MetaMathlibExt.Dickson

variable (p : ℕ) [Fact (Nat.Prime p)]
/--
[dickson_sylow_two_sq_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/DicksonPGL2Tame.lean)
-/
@[path]
private lemma dickson_sylow_two_sq_eq_one
  (G : Subgroup (PGL p)) [Finite G] (hG_tame : ¬p ∣ Nat.card G)
  (hG60 : Nat.card G = 60)
  (hall : ∀ x : dicksonExceptional G (Projectivization (K p) (Fin 2 → K p)),
    Nat.card (MulAction.stabilizer G x) = 2 ∨
    Nat.card (MulAction.stabilizer G x) = 3 ∨
    Nat.card (MulAction.stabilizer G x) = 5)
  (Q : Sylow 2 G) (u : Q) : (u : G) ^ 2 = 1 := by
  classical
  by_cases hu1 : (u : G) = 1
  · simp [hu1]
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hQ4 : Nat.card Q = 4 := by
    rw [Sylow.card_eq_multiplicity, hG60]
    norm_num [Nat.factorization]
  let X := Projectivization (K p) (Fin 2 → K p)
  let E := dicksonExceptional G X
  let F := MulAction.fixedBy X (u : G)
  have hF : Nat.card F = 2 := dickson_card_fixedBy_subgroup p G hG_tame u hu1
  have hFdata : Nonempty F ∧ Finite F := Nat.card_pos_iff.mp (by rw [hF]; decide)
  let xF : F := Classical.choice hFdata.1
  let xE : E := ⟨xF.1, ⟨u, hu1, MulAction.mem_fixedBy.mp xF.2⟩⟩
  have humem : (u : G) ∈ MulAction.stabilizer G xE := by
    exact Subtype.ext (MulAction.mem_fixedBy.mp xF.2)
  have hdivQ := Subgroup.orderOf_dvd_natCard (Q : Subgroup G) u.2
  have hdivS := Subgroup.orderOf_dvd_natCard (MulAction.stabilizer G xE) humem
  have hordpos : 0 < orderOf (u : G) := by
    simpa only [Subgroup.orderOf_coe] using orderOf_pos u
  have hordne : orderOf (u : G) ≠ 1 := mt orderOf_eq_one_iff.mp hu1
  have hordle : orderOf (u : G) ≤ 4 := by
    rw [hQ4] at hdivQ
    exact Nat.le_of_dvd (by decide) hdivQ
  have hord : orderOf (u : G) = 2 := by
    obtain hs | hs | hs := hall xE
    · rw [hs] at hdivS
      interval_cases orderOf (u : G) <;> simp_all [Nat.dvd_iff_mod_eq_zero]
    · rw [hs] at hdivS
      interval_cases orderOf (u : G) <;> simp_all [Nat.dvd_iff_mod_eq_zero]
    · rw [hs] at hdivS
      interval_cases orderOf (u : G) <;> simp_all [Nat.dvd_iff_mod_eq_zero]
  simpa only [hord] using pow_orderOf_eq_one (u : G)

end MetaMathlibExt.Dickson

namespace MetaMathlibExt.Dickson

variable (p : ℕ) [Fact (Nat.Prime p)]
/--
[dickson_sylow_two_commute](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/DicksonPGL2Tame.lean)
-/
@[path]
private lemma dickson_sylow_two_commute
  (G : Subgroup (PGL p)) [Finite G] (hG_tame : ¬p ∣ Nat.card G)
  (hG60 : Nat.card G = 60)
  (hall : ∀ x : dicksonExceptional G (Projectivization (K p) (Fin 2 → K p)),
    Nat.card (MulAction.stabilizer G x) = 2 ∨
    Nat.card (MulAction.stabilizer G x) = 3 ∨
    Nat.card (MulAction.stabilizer G x) = 5)
  (Q : Sylow 2 G) (a b : Q) : Commute (a : G) (b : G) := by
  have ha2 := dickson_sylow_two_sq_eq_one p G hG_tame hG60 hall Q a
  have hb2 := dickson_sylow_two_sq_eq_one p G hG_tame hG60 hall Q b
  let ab : Q := a * b
  have hab2 := dickson_sylow_two_sq_eq_one p G hG_tame hG60 hall Q ab
  have ha_inv : (a : G) = (a : G)⁻¹ := eq_inv_of_mul_eq_one_left (by simpa [pow_two] using ha2)
  have hb_inv : (b : G) = (b : G)⁻¹ := eq_inv_of_mul_eq_one_left (by simpa [pow_two] using hb2)
  have hab_inv : (a : G) * b = ((a : G) * b)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by simpa [ab, pow_two] using hab2)
  exact calc
    (a : G) * b = ((a : G) * b)⁻¹ := hab_inv
    _ = (b : G)⁻¹ * (a : G)⁻¹ := mul_inv_rev (a : G) b
    _ = (b : G) * a := by rw [← hb_inv, ← ha_inv]

end MetaMathlibExt.Dickson

namespace MetaMathlibExt.Dickson

variable (p : ℕ) [Fact (Nat.Prime p)]
/--
[dickson_sylow_two_unique_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/DicksonPGL2Tame.lean)
-/
@[path]
private lemma dickson_sylow_two_unique_of_mem
  (G : Subgroup (PGL p)) [Finite G] (hG_tame : ¬p ∣ Nat.card G)
  (hG60 : Nat.card G = 60)
  (hall : ∀ x : dicksonExceptional G (Projectivization (K p) (Fin 2 → K p)),
    Nat.card (MulAction.stabilizer G x) = 2 ∨
    Nat.card (MulAction.stabilizer G x) = 3 ∨
    Nat.card (MulAction.stabilizer G x) = 5)
  (r : G) (hr : orderOf r = 2) (Q R : Sylow 2 G)
  (hrQ : r ∈ Q) (hrR : r ∈ R) : Q = R := by
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hsylow4 (S : Sylow 2 G) : Nat.card S = 4 := by
    rw [Sylow.card_eq_multiplicity, hG60]
    norm_num [Nat.factorization]
  have centralizer_eq (S : Sylow 2 G) (hrS : r ∈ S) :
    (S : Subgroup G) = Subgroup.centralizer ({r} : Set G) := by
    have hSle : (S : Subgroup G) ≤ Subgroup.centralizer ({r} : Set G) := by
      intro s hs
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst z
      exact dickson_sylow_two_commute p G hG_tame hG60 hall S ⟨r, hrS⟩ ⟨s, hs⟩
    apply Subgroup.eq_of_le_of_card_ge hSle
    rw [hsylow4 S]
    exact dickson_card_centralizer_le_four p G hG_tame hall r hr
  apply Sylow.ext
  exact (centralizer_eq Q hrQ).trans (centralizer_eq R hrR).symm

end MetaMathlibExt.Dickson

namespace MetaMathlibExt.Dickson

variable (p : ℕ) [Fact (Nat.Prime p)]
/--
[dickson_involutions_conjugate](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/DicksonPGL2Tame.lean)
-/
@[path]
private lemma dickson_involutions_conjugate
  (G : Subgroup (PGL p)) [Finite G] (hG_tame : ¬p ∣ Nat.card G)
  (horbits : Nat.card (MulAction.orbitRel.Quotient G
    (dicksonExceptional G (Projectivization (K p) (Fin 2 → K p)))) = 3)
  (x₂ x₃ x₅ : dicksonExceptional G (Projectivization (K p) (Fin 2 → K p)))
  (h₂ : Nat.card (MulAction.stabilizer G x₂) = 2)
  (h₃ : Nat.card (MulAction.stabilizer G x₃) = 3)
  (h₅ : Nat.card (MulAction.stabilizer G x₅) = 5)
  (hall : ∀ x : dicksonExceptional G (Projectivization (K p) (Fin 2 → K p)),
    Nat.card (MulAction.stabilizer G x) = 2 ∨
    Nat.card (MulAction.stabilizer G x) = 3 ∨
    Nat.card (MulAction.stabilizer G x) = 5)
  (t s : G) (ht : orderOf t = 2) (hs : orderOf s = 2) :
  ∃ g : G, g * t * g⁻¹ = s := by
  classical
  let X := Projectivization (K p) (Fin 2 → K p)
  let E := dicksonExceptional G X
  have point (a : G) (ha : orderOf a = 2) :
    ∃ x : E, Nat.card (MulAction.stabilizer G x) = 2 ∧ a • x = x := by
    have ha1 : a ≠ 1 := by intro h; simp_all
    let F := MulAction.fixedBy X a
    have hF : Nat.card F = 2 := dickson_card_fixedBy_subgroup p G hG_tame a ha1
    have hFdata : Nonempty F ∧ Finite F := Nat.card_pos_iff.mp (by rw [hF]; decide)
    let z : F := Classical.choice hFdata.1
    let x : E := ⟨z.1, ⟨a, ha1, MulAction.mem_fixedBy.mp z.2⟩⟩
    have hfix : a • x = x := Subtype.ext (MulAction.mem_fixedBy.mp z.2)
    have hdiv := Subgroup.orderOf_dvd_natCard (MulAction.stabilizer G x) hfix
    have hstab : Nat.card (MulAction.stabilizer G x) = 2 := by
      obtain h | h | h := hall x
      · exact h
      · rw [h, ha] at hdiv
        norm_num at hdiv
      · rw [h, ha] at hdiv
        norm_num at hdiv
    exact ⟨x, hstab, hfix⟩
  obtain ⟨xt, hxt, htfix⟩ := point t ht
  obtain ⟨xs, hxs, hsfix⟩ := point s hs
  have hquot : Quotient.mk'' xt = (Quotient.mk'' xs : MulAction.orbitRel.Quotient G E) :=
    dickson_same_orbit_of_stabilizer_card_two x₂ x₃ x₅ h₂ h₃ h₅ horbits hxt hxs
  obtain ⟨g, hg⟩ := Quotient.exact hquot
  let S := MulAction.stabilizer G xs
  let ct : S := ⟨g⁻¹ * t * g, by
    change (g⁻¹ * t * g) • xs = xs
    calc
      (g⁻¹ * t * g) • xs = g⁻¹ • (t • (g • xs)) := by simp only [mul_smul]
      _ = g⁻¹ • (t • xt) := congrArg (fun z : E => g⁻¹ • (t • z)) hg
      _ = g⁻¹ • xt := by rw [htfix]
      _ = xs := by rw [← hg, inv_smul_smul]⟩
  let ss : S := ⟨s, hsfix⟩
  have ht1 : t ≠ 1 := by intro h; simp_all
  have hs1 : s ≠ 1 := by intro h; simp_all
  have hct1 : ct ≠ 1 := by
    intro h
    apply ht1
    have hval : g⁻¹ * t * g = 1 := congrArg Subtype.val h
    calc
      t = g * (g⁻¹ * t * g) * g⁻¹ := by group
      _ = 1 := by rw [hval]; simp
  have hss1 : ss ≠ 1 := by
    intro h
    apply hs1
    exact congrArg Subtype.val h
  have hunique : ∃! z : S, z ≠ 1 := (Nat.card_eq_two_iff' 1).mp hxs
  have hcts : ct = ss := hunique.unique hct1 hss1
  have hval : g⁻¹ * t * g = s := congrArg (fun z : S => (z : G)) hcts
  exact ⟨g⁻¹, by simpa using hval⟩

end MetaMathlibExt.Dickson

namespace MetaMathlibExt.Dickson

variable (p : ℕ) [Fact (Nat.Prime p)]
/--
[dickson_card_ne_one_of_card_four](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/DicksonPGL2Tame.lean)
-/
@[path]
private lemma dickson_card_ne_one_of_card_four
  {H : Type*} [Group H] [Finite H] (hH : Nat.card H = 4) :
  Nat.card {u : H // u ≠ 1} = 3 := by
  classical
  let _ := Fintype.ofFinite H
  let _ := Fintype.ofFinite {u : H // u ≠ 1}
  let _ := Fintype.ofFinite {u : H // u = 1}
  have hHF : Fintype.card H = 4 := by
    simpa only [Nat.card_eq_fintype_card] using hH
  rw [Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype_compl (fun u : H => u = 1)]
  simp [hHF]

end MetaMathlibExt.Dickson

namespace MetaMathlibExt.Dickson

variable (p : ℕ) [Fact (Nat.Prime p)]
/--
[dickson_card_sylow_two_eq_five](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/DicksonPGL2Tame.lean)
-/
@[path]
private lemma dickson_card_sylow_two_eq_five
  (G : Subgroup (PGL p)) [Finite G] (hG_tame : ¬p ∣ Nat.card G)
  (hG60 : Nat.card G = 60)
  (horbits : Nat.card (MulAction.orbitRel.Quotient G
    (dicksonExceptional G (Projectivization (K p) (Fin 2 → K p)))) = 3)
  (x₂ x₃ x₅ : dicksonExceptional G (Projectivization (K p) (Fin 2 → K p)))
  (h₂ : Nat.card (MulAction.stabilizer G x₂) = 2)
  (h₃ : Nat.card (MulAction.stabilizer G x₃) = 3)
  (h₅ : Nat.card (MulAction.stabilizer G x₅) = 5)
  (hall : ∀ x : dicksonExceptional G (Projectivization (K p) (Fin 2 → K p)),
    Nat.card (MulAction.stabilizer G x) = 2 ∨
    Nat.card (MulAction.stabilizer G x) = 3 ∨
    Nat.card (MulAction.stabilizer G x) = 5) :
  Nat.card (Sylow 2 G) = 5 := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hsylow4 (Q : Sylow 2 G) : Nat.card Q = 4 := by
    rw [Sylow.card_eq_multiplicity, hG60]
    norm_num [Nat.factorization]
  have sylow_centralizer (r : G) (hr : orderOf r = 2) (Q : Sylow 2 G)
    (hrQ : r ∈ Q) : (Q : Subgroup G) = Subgroup.centralizer ({r} : Set G) := by
    have hQle : (Q : Subgroup G) ≤ Subgroup.centralizer ({r} : Set G) := by
      intro q hq
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst z
      exact dickson_sylow_two_commute p G hG_tame hG60 hall Q ⟨r, hrQ⟩ ⟨q, hq⟩
    apply Subgroup.eq_of_le_of_card_ge hQle
    rw [hsylow4 Q]
    exact dickson_card_centralizer_le_four p G hG_tame hall r hr
  have sylow_unique (r : G) (hr : orderOf r = 2) (Q R : Sylow 2 G)
    (hrQ : r ∈ Q) (hrR : r ∈ R) : Q = R := by
    apply Sylow.ext
    exact (sylow_centralizer r hr Q hrQ).trans (sylow_centralizer r hr R hrR).symm
  let P : Sylow 2 G := Classical.choice inferInstance
  have hP4 : Nat.card P = 4 := hsylow4 P
  let _ : Nontrivial P := Finite.one_lt_card_iff_nontrivial.mp (by rw [hP4]; decide)
  obtain ⟨t, ht1⟩ := exists_ne (1 : P)
  have ht1G : (t : G) ≠ 1 := by exact fun h => ht1 (Subtype.ext h)
  have ht2pow := dickson_sylow_two_sq_eq_one p G hG_tame hG60 hall P t
  have htorder : orderOf (t : G) = 2 := orderOf_eq_prime ht2pow ht1G
  let C := Subgroup.centralizer ({(t : G)} : Set G)
  have hPC : (P : Subgroup G) = C := sylow_centralizer t htorder P t.2
  have hC4 : Nat.card C = 4 := by rw [← hPC, hP4]
  let I := {r : G // orderOf r = 2}
  let O := MulAction.orbit (ConjAct G) (t : G)
  let f : O → I := fun y => ⟨y.1, by
    obtain ⟨c, hc⟩ := y.2
    rw [← hc]
    calc
      orderOf (c • (t : G)) = orderOf ((t : G)) := by
        change orderOf ((MulAut.conj (ConjAct.ofConjAct c)) (t : G)) = _
        exact MulEquiv.orderOf_eq (MulAut.conj (ConjAct.ofConjAct c)) t
      _ = 2 := htorder⟩
  have hfinj : Function.Injective f := by
    intro y z h
    apply Subtype.ext
    exact congrArg (fun w : I => w.1) h
  have hfsurj : Function.Surjective f := by
    intro r
    obtain ⟨g, hg⟩ := dickson_involutions_conjugate p G hG_tame horbits
      x₂ x₃ x₅ h₂ h₃ h₅ hall t r htorder r.2
    have hact : ConjAct.toConjAct g • (t : G) = r.1 := by
      simpa only [ConjAct.toConjAct_smul_eq_mulAut_conj, MulAut.conj_apply] using hg
    exact ⟨⟨r.1, ⟨ConjAct.toConjAct g, hact⟩⟩, Subtype.ext rfl⟩
  let S := MulAction.stabilizer (ConjAct G) (t : G)
  have hS4 : Nat.card S = 4 := by
    calc
      Nat.card S = Nat.card (Subgroup.centralizer ({(t : G)} : Set G)) := by
        simpa [S] using (Subgroup.nat_card_centralizer_nat_card_stabilizer (t : G)).symm
      _ = Nat.card C := rfl
      _ = 4 := hC4
  let _ : Finite O := Finite.of_injective f hfinj
  let _ := Fintype.ofFinite G
  let _ := Fintype.ofEquiv G (ConjAct.toConjAct (G := G)).toEquiv
  let _ := Fintype.ofFinite O
  let _ := Fintype.ofFinite S
  have hprod : Nat.card O * Nat.card S = Nat.card (ConjAct G) := by
    simpa only [Nat.card_eq_fintype_card] using
      MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) (t : G)
  have hO15 : Nat.card O = 15 := by
    have hconj : Nat.card (ConjAct G) = Nat.card G :=
      Nat.card_congr (ConjAct.ofConjAct (G := G)).toEquiv
    rw [hS4, hconj, hG60] at hprod
    omega
  have hI15 : Nat.card I = 15 := by
    rw [← hO15]
    exact (Nat.card_congr (Equiv.ofBijective f ⟨hfinj, hfsurj⟩)).symm
  let A := (Q : Sylow 2 G) × {u : (Q : Subgroup G) // u ≠ 1}
  let φ : A → I := fun z => ⟨(z.2.1 : G), by
    have hu1 : (z.2.1 : G) ≠ 1 := by
      exact fun h => z.2.2 (Subtype.ext h)
    exact orderOf_eq_prime
      (dickson_sylow_two_sq_eq_one p G hG_tame hG60 hall z.1 z.2.1) hu1⟩
  have hφinj : Function.Injective φ := by
    rintro ⟨Qa, ua⟩ ⟨Qb, ub⟩ hab
    have hval : (ua.1 : G) = (ub.1 : G) := congrArg (fun r : I => r.1) hab
    have huaQb : (ua.1 : G) ∈ Qb := by rw [hval]; exact ub.1.2
    have hQR : Qa = Qb := sylow_unique (ua.1 : G) (φ ⟨Qa, ua⟩).2 Qa Qb ua.1.2 huaQb
    subst Qb
    have huv : ua = ub := Subtype.ext (Subtype.ext hval)
    subst ub
    rfl
  have hφsurj : Function.Surjective φ := by
    intro r
    let R : Subgroup G := Subgroup.zpowers r.1
    have hRcard : Nat.card R = 2 := by
      rw [show Nat.card R = orderOf r.1 by exact Nat.card_zpowers r.1, r.2]
    have hRgroup : IsPGroup 2 R := IsPGroup.iff_card.mpr ⟨1, by
      simpa only [pow_one, Nat.card_eq_fintype_card] using hRcard⟩
    obtain ⟨Q, hRQ⟩ := hRgroup.exists_le_sylow
    have hrR : r.1 ∈ R := Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩
    let u : Q := ⟨r.1, hRQ hrR⟩
    have hu1 : u ≠ 1 := by
      intro h
      have hr1 : r.1 = 1 := congrArg Subtype.val h
      have hrne : r.1 ≠ 1 := by
        intro hr
        have hord := r.2
        rw [hr] at hord
        norm_num at hord
      exact hrne hr1
    refine ⟨⟨Q, ⟨u, hu1⟩⟩, ?_⟩
    exact Subtype.ext rfl
  have hfiber3 (Q : Sylow 2 G) :
    Nat.card {u : (Q : Subgroup G) // u ≠ 1} = 3 := by
    exact dickson_card_ne_one_of_card_four (hsylow4 Q)
  let _ := Fintype.ofFinite (Sylow 2 G)
  let _ (Q : Sylow 2 G) := Fintype.ofFinite {u : (Q : Subgroup G) // u ≠ 1}
  have hAcard : Nat.card A = Nat.card (Sylow 2 G) * 3 := by
    calc
      Nat.card A = ∑ Q : Sylow 2 G,
        Nat.card {u : (Q : Subgroup G) // u ≠ 1} := by
        simp only [A, Nat.card_eq_fintype_card, Fintype.card_sigma]
      _ = ∑ _Q : Sylow 2 G, 3 := by
        apply Finset.sum_congr rfl
        intro Q _
        exact hfiber3 Q
      _ = Nat.card (Sylow 2 G) * 3 := by
        simp [Nat.card_eq_fintype_card]
  have hA15 : Nat.card A = 15 := by
    rw [Nat.card_congr (Equiv.ofBijective φ ⟨hφinj, hφsurj⟩), hI15]
  omega

end MetaMathlibExt.Dickson

/--
[classification_tame](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/DicksonPGL2Tame.lean)
-/
@[path]
private lemma classification_tame_eq
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 < p)]
  {G : Subgroup (PGL p)} [Finite G]
-- given
  (hG_tame : ¬ (p : ℕ) ∣ Nat.card G)
  (hG_nontrivial : Nontrivial G) :
-- imply
  (IsCyclic G) ∨
    (∃ n : ℕ, n ≥ 2 ∧ Nonempty (G ≃* DihedralGroup n)) ∨
    (Nonempty (G ≃* alternatingGroup (Fin 4))) ∨
    (Nonempty (G ≃* Equiv.Perm (Fin 4))) ∨
    (Nonempty (G ≃* alternatingGroup (Fin 5))) := by
-- proof
  apply MetaMathlibExt.Dickson.classification_tame p G hG_tame hG_nontrivial


-- created on 2026-10-20
-- updated on 2026-10-26
