/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/Green25_upper_solution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.FC.Green25_upper_solution.Part4
open Asymptotics Filter Finset


namespace Green25

lemma complemented_digit_partition (Q m r : ℕ) (hQ : 2 ≤ Q) (heven : 2 ∣ Q)
    (hr : r ≤ m) :
    ∃ P : Finpartition (Icc 1 (Q ^ m)),
      #P.parts = Q ^ m / 2 ^ r ∧
      #(P.parts.biUnion Finset.restrictedSumset) ≤ r * (2 * Q) ^ (m - 1) := by
  letI : NeZero (Q ^ m) := ⟨pow_ne_zero _ (by omega)⟩
  let s : Setoid ℕ := Setoid.ker (vectorKey Q m r)
  letI : DecidableRel s.r := Classical.decRel _
  let P : Finpartition (Icc 1 (Q ^ m)) := Finpartition.ofSetSetoid s _
  have hcardpart : ∀ p ∈ P.parts, #p = 2 ^ r := by
    intro p hp
    obtain ⟨a, ha⟩ := P.nonempty_of_mem_parts hp
    have haI : a ∈ Icc 1 (Q ^ m) := P.subset hp ha
    rw [← P.part_eq_of_mem hp ha]
    let v := digitVector Q m a
    let f : (Fin r → Bool) → ℕ := fun b => encodeVector (flipVector Q r v b)
    have hfmem : ∀ b : Fin r → Bool, f b ∈ P.part a := by
      intro b
      rw [show P = Finpartition.ofSetSetoid s (Icc 1 (Q ^ m)) by rfl]
      rw [Finpartition.mem_part_ofSetSetoid_iff_rel]
      exact ⟨haI, encodeVector_mem Q m (flipVector Q r v b), by
        change (Setoid.ker (vectorKey Q m r)) a (f b)
        rw [Setoid.ker_def]
        funext i
        change (if i.1 < r then complementKey Q (digitVector Q m a i)
          else digitVector Q m a i) =
          (if i.1 < r then complementKey Q (digitVector Q m (encodeVector (flipVector Q r v b)) i)
          else digitVector Q m (encodeVector (flipVector Q r v b)) i)
        rw [digitVector_encode Q m]
        simp only [v]
        by_cases hi : i.1 < r
        · by_cases hb : b ⟨i, hi⟩ = true
          · have hc : complementKey Q (digitVector Q m a i) =
                complementKey Q (Q - 1 - digitVector Q m a i) :=
              (complementKey_eq_iff Q _ _ (by omega) (by omega) heven).2 (Or.inr rfl)
            simpa [flipVector, hi, hb] using hc
          · simp [flipVector, hi, hb]
        · simp [hi, flipVector]
        ⟩
    have hfinj : Function.Injective f := by
      intro b c hbc
      have hv : flipVector Q r v b = flipVector Q r v c := by
        apply finFunctionFinEquiv.injective
        apply Fin.ext
        simpa [f, encodeVector] using congrArg (fun n => n - 1) hbc
      funext j
      let i : Fin m := ⟨j, lt_of_lt_of_le j.isLt hr⟩
      have hij : i.1 < r := j.isLt
      have hh := congrFun hv i
      have hhval := congrArg Fin.val hh
      have hji : (⟨i, hij⟩ : Fin r) = j := Fin.ext rfl
      simp only [flipVector, dif_pos hij, hji] at hhval
      have hn := ne_complement Q (v i) (v i).isLt heven
      cases hb : b j <;> cases hc : c j
      · rfl
      · exfalso
        simp [hb, hc] at hhval
        apply hn
        omega
      · exfalso
        simp [hb, hc] at hhval
        apply hn
        omega
      · rfl
    have hc := Finset.card_bij (fun b (_ : b ∈ (Finset.univ : Finset (Fin r → Bool))) => f b)
      (fun b _ => hfmem b)
      (fun b _ c _ h => hfinj h)
      (fun x hx => by
        rw [show P = Finpartition.ofSetSetoid s (Icc 1 (Q ^ m)) by rfl] at hx
        rw [Finpartition.mem_part_ofSetSetoid_iff_rel] at hx
        let w := digitVector Q m x
        let b : Fin r → Bool := fun j => decide (w ⟨j, lt_of_lt_of_le j.isLt hr⟩ ≠
          v ⟨j, lt_of_lt_of_le j.isLt hr⟩)
        refine ⟨b, Finset.mem_univ _, ?_⟩
        change f b = x
        rw [← encode_digitVector Q m x hx.2.1]
        change encodeVector (flipVector Q r v b) = encodeVector (digitVector Q m x)
        apply congrArg encodeVector
        ext i
        by_cases hi : i.1 < r
        · have hkey := congrFun hx.2.2 i
          simp only [s, Setoid.ker_def, vectorKey, hi, ↓reduceIte] at hkey
          have hkey' : complementKey Q (v i) = complementKey Q (w i) := by
            simpa [v, w] using hkey
          have hor := (complementKey_eq_iff Q _ _ (v i).isLt (w i).isLt heven).1 hkey'
          change (flipVector Q r v b i).1 = (w i).1
          by_cases heq : w i = v i
          · simpa [flipVector, hi, b, heq]
          · rcases hor with hor | hor
            · exact (heq (Fin.ext hor)).elim
            · simpa [flipVector, hi, b, heq] using hor.symm
        · have hkey := congrFun hx.2.2 i
          simp only [s, Setoid.ker_def, vectorKey, hi, ↓reduceIte] at hkey
          change (flipVector Q r v b i).1 = (w i).1
          simpa [flipVector, hi, v, w] using hkey)
    simpa [Fintype.card_fun] using hc.symm
  refine ⟨P, ?_, ?_⟩
  · have hs := P.sum_card_parts
    have heq : #P.parts * 2 ^ r = Q ^ m := by
      calc
        #P.parts * 2 ^ r = ∑ p ∈ P.parts, 2 ^ r := by simp
        _ = ∑ p ∈ P.parts, #p := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [hcardpart p hp]
        _ = #(Icc 1 (Q ^ m)) := hs
        _ = Q ^ m := by simp [Nat.card_Icc]
    exact (Nat.div_eq_of_eq_mul_left (by positivity) heq.symm).symm
  · by_cases hr0 : r = 0
    · subst r
      simp only [zero_mul, Nat.le_zero]
      rw [Finset.card_eq_zero]
      ext z
      simp only [Finset.mem_biUnion]
      constructor
      · rintro ⟨p, hp, hz⟩
        rw [Finset.restrictedSumset] at hz
        obtain ⟨xy, hxy, rfl⟩ := Finset.mem_image.mp hz
        rw [Finset.mem_offDiag] at hxy
        have hc := hcardpart p hp
        rw [pow_zero] at hc
        obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hc
        simp_all
      · simp
    · have hm0 : m ≠ 0 := by omega
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
      let C := Fin r × (Fin n → Fin (2 * Q))
      let decode : C → ℕ := fun c =>
        let j : Fin (n + 1) := ⟨c.1.1, lt_of_lt_of_le c.1.2 hr⟩
        let d : Fin (n + 1) → Fin (2 * Q) :=
          Fin.insertNth j ⟨Q - 1, by omega⟩ c.2
        2 + ∑ i, (d i : ℕ) * Q ^ (i : ℕ)
      have hsubset : P.parts.biUnion Finset.restrictedSumset ⊆
          (Finset.univ : Finset C).image decode := by
        intro z hz
        rw [Finset.mem_biUnion] at hz
        obtain ⟨p, hp, hz⟩ := hz
        rw [Finset.restrictedSumset] at hz
        obtain ⟨xy, hxy, hsum⟩ := Finset.mem_image.mp hz
        rw [Finset.mem_offDiag] at hxy
        let x := xy.1
        let y := xy.2
        have hx : x ∈ p := hxy.1
        have hy : y ∈ p := hxy.2.1
        have hne : x ≠ y := hxy.2.2
        have hxI : x ∈ Icc 1 (Q ^ (n + 1)) := P.subset hp hx
        have hyI : y ∈ Icc 1 (Q ^ (n + 1)) := P.subset hp hy
        have hyPart : y ∈ P.part x := by
          rw [P.part_eq_of_mem hp hx]
          exact hy
        have hrel : vectorKey Q (n + 1) r x = vectorKey Q (n + 1) r y := by
          rw [show P = Finpartition.ofSetSetoid s (Icc 1 (Q ^ (n + 1))) by rfl] at hyPart
          rw [Finpartition.mem_part_ofSetSetoid_iff_rel] at hyPart
          exact hyPart.2.2
        let vx := digitVector Q (n + 1) x
        let vy := digitVector Q (n + 1) y
        have hvne : vx ≠ vy := by
          intro hv
          apply hne
          rw [← encode_digitVector Q (n + 1) x hxI,
            ← encode_digitVector Q (n + 1) y hyI]
          change encodeVector vx = encodeVector vy
          rw [hv]
        obtain ⟨i, hi⟩ := Function.ne_iff.mp hvne
        have hir : i.1 < r := by
          by_contra hir
          have hk := congrFun hrel i
          simp only [vectorKey, hir, ↓reduceIte] at hk
          exact hi (Fin.ext hk)
        have hk := congrFun hrel i
        simp only [vectorKey, hir, ↓reduceIte] at hk
        have hk' : complementKey Q (vx i) = complementKey Q (vy i) := by
          simpa [vx, vy] using hk
        have hor := (complementKey_eq_iff Q _ _ (vx i).isLt (vy i).isLt heven).1 hk'
        have hcomp : (vy i : ℕ) = Q - 1 - (vx i : ℕ) := by
          rcases hor with hor | hor
          · exact (hi (Fin.ext hor.symm)).elim
          · exact hor
        let j : Fin r := ⟨i.1, hir⟩
        let jm : Fin (n + 1) := ⟨j.1, lt_of_lt_of_le j.2 hr⟩
        have hjm : jm = i := Fin.ext rfl
        let d : Fin (n + 1) → Fin (2 * Q) := fun k =>
          ⟨(vx k : ℕ) + (vy k : ℕ), by
            have hxlt := (vx k).isLt
            have hylt := (vy k).isLt
            omega⟩
        have hdjm : d jm = (⟨Q - 1, by omega⟩ : Fin (2 * Q)) := by
          apply Fin.ext
          simp only [d, hjm]
          omega
        let c : C := (j, Fin.removeNth jm d)
        refine Finset.mem_image.mpr ⟨c, Finset.mem_univ _, ?_⟩
        have hrecon : Fin.insertNth jm (⟨Q - 1, by omega⟩ : Fin (2 * Q))
            (Fin.removeNth jm d) = d := by
          rw [Fin.insertNth_removeNth]
          rw [show (⟨Q - 1, by omega⟩ : Fin (2 * Q)) = d jm from hdjm.symm]
          simp
        change 2 + ∑ k, ((Fin.insertNth jm (⟨Q - 1, by omega⟩ : Fin (2 * Q))
          (Fin.removeNth jm d)) k : ℕ) * Q ^ (k : ℕ) = z
        rw [hrecon]
        change x + y = z at hsum
        rw [← hsum]
        rw [← encode_digitVector Q (n + 1) x hxI,
          ← encode_digitVector Q (n + 1) y hyI]
        simp only [encodeVector, finFunctionFinEquiv_apply, d, vx, vy,
          Nat.add_mul, Finset.sum_add_distrib]
        omega
      calc
        #(P.parts.biUnion Finset.restrictedSumset) ≤
            #((Finset.univ : Finset C).image decode) := Finset.card_le_card hsubset
        _ ≤ #(Finset.univ : Finset C) := Finset.card_image_le
        _ = r * (2 * Q) ^ ((n + 1) - 1) := by
          simp [C, Fintype.card_fun]


lemma digit_partition (t : ℕ) (ht : 5 ≤ t) :
    ∃ P : Finpartition (Icc 1 (2 ^ (4 * (2 ^ t) ^ 2))),
      #P.parts = candidate25 (2 ^ (4 * (2 ^ t) ^ 2)) ∧
      20 * #(P.parts.biUnion Finset.restrictedSumset) <
        2 ^ (4 * (2 ^ t) ^ 2) := by
  have hrall : ∀ u : ℕ, 5 ≤ u → 4 + 4 * u ≤ 2 ^ u := by
    intro u hu
    obtain ⟨v, rfl⟩ := Nat.exists_eq_add_of_le hu
    induction v with
    | zero => norm_num
    | succ v ih =>
      specialize ih (by omega)
      rw [show 5 + (v + 1) = (5 + v) + 1 by omega, pow_succ]
      have hp : 4 ≤ 2 ^ (5 + v) := by
        calc
          4 ≤ 2 ^ 5 := by norm_num
          _ ≤ 2 ^ (5 + v) := Nat.pow_le_pow_right (by omega) (by omega)
      nlinarith
  have hr : 4 + 4 * t ≤ 2 ^ t := hrall t ht
  let m := 2 ^ t
  let Q := 2 ^ (4 * m)
  let r := 4 + 4 * t
  have hm : 0 < m := by simp [m]
  have hQ : 2 ≤ Q := by
    dsimp [Q]
    exact Nat.one_lt_two_pow (by positivity)
  have heven : 2 ∣ Q := by
    dsimp [Q]
    exact dvd_pow_self 2 (by positivity)
  have hN : Q ^ m = 2 ^ (4 * (2 ^ t) ^ 2) := by
    simp only [Q, m, ← pow_mul]
    congr 1
    ring
  have hpart := complemented_digit_partition Q m r hQ heven (by simpa [m, r])
  rw [hN] at hpart
  obtain ⟨P, hcard, hsum⟩ := hpart
  refine ⟨P, ?_, ?_⟩
  · rw [candidate25_special t ht, hcard]
    simp only [r]
    have hle : 4 + 4 * t ≤ 4 * (2 ^ t) ^ 2 := by
      apply hr.trans
      have hp : 1 ≤ 2 ^ t := one_le_pow₀ (by omega)
      nlinarith
    rw [Nat.pow_div hle (by omega)]
  · calc
      20 * #(P.parts.biUnion Finset.restrictedSumset) ≤
          20 * (r * (2 * Q) ^ (m - 1)) := Nat.mul_le_mul_left 20 hsum
      _ < Q ^ m := by
        have hm6 : 6 ≤ 2 ^ t := by
          calc
            6 ≤ 2 ^ 5 := by norm_num
            _ ≤ 2 ^ t := Nat.pow_le_pow_right (by omega) ht
        have hten : ∀ n : ℕ, 6 ≤ n → 10 * n < 2 ^ n := by
          intro n hn
          induction n, hn using Nat.le_induction with
          | base => norm_num
          | succ n hn ih =>
            rw [pow_succ]
            have hp : 10 ≤ 2 ^ n := by
              calc
                10 ≤ 2 ^ 6 := by norm_num
                _ ≤ 2 ^ n := Nat.pow_le_pow_right (by omega) hn
            omega
        have hcoef : 20 * (4 + 4 * t) < 2 ^ (3 * 2 ^ t + 1) := by
          have hsmall := hten (2 ^ t) hm6
          have hrle : 4 + 4 * t ≤ 2 ^ t := hrall t ht
          have hfirst : 20 * (4 + 4 * t) < 2 ^ (2 ^ t + 1) := by
            rw [pow_succ]
            nlinarith
          exact hfirst.trans_le (Nat.pow_le_pow_right (by omega) (by omega))
        have hmul := Nat.mul_lt_mul_of_pos_right hcoef
          (show 0 < 2 ^ ((4 * 2 ^ t + 1) * (2 ^ t - 1)) by positivity)
        have hmpos : 0 < 2 ^ t := by positivity
        have hexp : (3 * 2 ^ t + 1) + (4 * 2 ^ t + 1) * (2 ^ t - 1) =
            4 * (2 ^ t) ^ 2 := by
          obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hmpos.ne'
          rw [hk]
          simp
          ring
        have hbase : 2 * 2 ^ (4 * 2 ^ t) = 2 ^ (4 * 2 ^ t + 1) := by
          rw [pow_succ]
          omega
        simp only [r, Q, m]
        rw [hbase]
        rw [mul_assoc] at hmul
        rw [← pow_add, hexp] at hmul
        simpa [← pow_mul, pow_two, mul_assoc] using hmul
      _ = 2 ^ (4 * (2 ^ t) ^ 2) := hN

end Green25
