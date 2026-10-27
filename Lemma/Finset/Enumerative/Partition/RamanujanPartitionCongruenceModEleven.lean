import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.Partition.RamanujanPartitionCongruenceModEleven.Part2
open MetaMathlibExt


namespace MetaMathlibExt

/--
[ramanujanElevenEuler_pow_three](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/RamanujanPartitionCongruenceModEleven.lean)
-/
@[path]
private lemma ramanujanElevenEuler_pow_three :
  ramanujanElevenEuler ^ 3 = ramanujanElevenJacobi := by
  rw [ramanujanElevenEuler, ramanujanElevenJacobi, ← map_pow,
    pentagonalSeries_pow_three]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ramanujanElevenEuler_pow_eleven](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/RamanujanPartitionCongruenceModEleven.lean)
-/
@[path]
private lemma ramanujanElevenEuler_pow_eleven :
  ramanujanElevenEuler ^ 11 =
    PowerSeries.expand 11 (by decide) ramanujanElevenEuler := by
  have hF : PowerSeries.map (frobenius (ZMod 11) 11)
    (PowerSeries.expand 11 (by decide) ramanujanElevenEuler) =
    ramanujanElevenEuler ^ 11 :=
    PowerSeries.map_frobenius_expand 11 (by decide)
  rwa [ZMod.frobenius_zmod 11, PowerSeries.map_id] at hF

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ramanujanElevenJacobi_pow_four](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/RamanujanPartitionCongruenceModEleven.lean)
-/
@[path]
private lemma ramanujanElevenJacobi_pow_four :
  ramanujanElevenJacobi ^ 4 =
    PowerSeries.expand 11 (by decide) ramanujanElevenEuler * ramanujanElevenEuler := by
  rw [← ramanujanElevenEuler_pow_three, ← pow_mul]
  rw [show 3 * 4 = 11 + 1 by decide, pow_add, ramanujanElevenEuler_pow_eleven,
    pow_one]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ramanujanElevenJacobi_pow_seven](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/RamanujanPartitionCongruenceModEleven.lean)
-/
@[path]
private lemma ramanujanElevenJacobi_pow_seven :
  ramanujanElevenJacobi ^ 7 =
    PowerSeries.expand 11 (by decide) ramanujanElevenEuler *
      ramanujanElevenEuler ^ 10 := by
  rw [← ramanujanElevenEuler_pow_three, ← pow_mul]
  rw [show 3 * 7 = 11 + 10 by decide, pow_add, ramanujanElevenEuler_pow_eleven]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ramanujanElevenCoeff_section](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/RamanujanPartitionCongruenceModEleven.lean)
-/
@[path]
private lemma ramanujanElevenCoeff_section (r n : ℕ) (f : PowerSeries (ZMod 11)) :
  PowerSeries.coeff n (ramanujanElevenSection r f) =
    if n ≡ r [MOD 11] then PowerSeries.coeff n f else 0 := by
  simp [ramanujanElevenSection]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ramanujanElevenExpandEuler_supported](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/RamanujanPartitionCongruenceModEleven.lean)
-/
@[path]
private lemma ramanujanElevenExpandEuler_supported :
  ramanujanElevenSupported 0
    (PowerSeries.expand 11 (by decide) ramanujanElevenEuler) := by
  intro n hn
  apply PowerSeries.coeff_expand_of_not_dvd 11 (by decide)
  intro hdiv
  exact hn (Nat.modEq_zero_iff_dvd.mpr hdiv)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ramanujanElevenPentagonal_residue](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/RamanujanPartitionCongruenceModEleven.lean)
-/
@[path]
private lemma ramanujanElevenPentagonal_residue (k : ℤ) :
  pentagonal k ≡ 0 [MOD 11] ∨ pentagonal k ≡ 1 [MOD 11] ∨
    pentagonal k ≡ 2 [MOD 11] ∨ pentagonal k ≡ 4 [MOD 11] ∨
      pentagonal k ≡ 5 [MOD 11] ∨ pentagonal k ≡ 7 [MOD 11] := by
  have hpk := two_mul_natCast_pentagonal k
  have hcast : (2 : ZMod 11) * (pentagonal k : ZMod 11) =
    (k : ZMod 11) * (3 * (k : ZMod 11) - 1) := by
    have hcc : (((2 * (pentagonal k : ℤ) : ℤ)) : ZMod 11) =
      (((k * (3 * k - 1) : ℤ)) : ZMod 11) := by
      rw [hpk]
    push_cast at hcc
    simpa using hcc
  have key : ∀ x y : ZMod 11, 2 * y = x * (3 * x - 1) →
    y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 4 ∨ y = 5 ∨ y = 7 := by
    decide
  rcases key (k : ZMod 11) (pentagonal k : ZMod 11) hcast with
    h | h | h | h | h | h
  · exact Or.inl ((ZMod.natCast_eq_natCast_iff _ _ _).mp h)
  · exact Or.inr <| Or.inl ((ZMod.natCast_eq_natCast_iff _ _ _).mp h)
  · exact Or.inr <| Or.inr <| Or.inl ((ZMod.natCast_eq_natCast_iff _ _ _).mp h)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl
    ((ZMod.natCast_eq_natCast_iff _ _ _).mp h)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
    ((ZMod.natCast_eq_natCast_iff _ _ _).mp h)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
    ((ZMod.natCast_eq_natCast_iff _ _ _).mp h)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ramanujanElevenEuler_coeff_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/RamanujanPartitionCongruenceModEleven.lean)
-/
@[path]
private lemma ramanujanElevenEuler_coeff_eq_zero {n : ℕ}
  (hn : ¬(n ≡ 0 [MOD 11] ∨ n ≡ 1 [MOD 11] ∨ n ≡ 2 [MOD 11] ∨
    n ≡ 4 [MOD 11] ∨ n ≡ 5 [MOD 11] ∨ n ≡ 7 [MOD 11])) :
  PowerSeries.coeff n ramanujanElevenEuler = 0 := by
  rw [ramanujanElevenEuler, PowerSeries.coeff_map]
  by_cases hp : n ∈ Set.range pentagonal
  · obtain ⟨k, rfl⟩ := hp
    exfalso
    exact hn (ramanujanElevenPentagonal_residue k)
  · rw [PowerSeries.coeff_pentagonalSeries_eq_zero ℤ hp, map_zero]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ramanujanElevenSection_euler_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/RamanujanPartitionCongruenceModEleven.lean)
-/
@[path]
private lemma ramanujanElevenSection_euler_eq_zero (r : ℕ)
  (hr : ¬(r ≡ 0 [MOD 11] ∨ r ≡ 1 [MOD 11] ∨ r ≡ 2 [MOD 11] ∨
    r ≡ 4 [MOD 11] ∨ r ≡ 5 [MOD 11] ∨ r ≡ 7 [MOD 11])) :
  ramanujanElevenSection r ramanujanElevenEuler = 0 := by
  ext n
  by_cases hn : n ≡ r [MOD 11]
  · have hn' : ¬(n ≡ 0 [MOD 11] ∨ n ≡ 1 [MOD 11] ∨ n ≡ 2 [MOD 11] ∨
    n ≡ 4 [MOD 11] ∨ n ≡ 5 [MOD 11] ∨ n ≡ 7 [MOD 11]) := by
    intro h
    apply hr
    obtain h | h | h | h | h | h := h
    · exact Or.inl (hn.symm.trans h)
    · exact Or.inr <| Or.inl (hn.symm.trans h)
    · exact Or.inr <| Or.inr <| Or.inl (hn.symm.trans h)
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inl (hn.symm.trans h)
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl (hn.symm.trans h)
    · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr (hn.symm.trans h)
    simp [hn, ramanujanElevenEuler_coeff_eq_zero hn']
  · simp [hn]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ramanujanElevenSection_eq_self](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/RamanujanPartitionCongruenceModEleven.lean)
-/
@[path]
private lemma ramanujanElevenSection_eq_self {r : ℕ} {f : PowerSeries (ZMod 11)}
  (hf : ramanujanElevenSupported r f) : ramanujanElevenSection r f = f := by
  ext n
  by_cases hn : n ≡ r [MOD 11]
  · simp [hn]
  · simp [hn, hf n hn]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ramanujanElevenSection_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/RamanujanPartitionCongruenceModEleven.lean)
-/
@[path]
private lemma ramanujanElevenSection_eq_zero {r s : ℕ} {f : PowerSeries (ZMod 11)}
  (hf : ramanujanElevenSupported s f) (hrs : ¬r ≡ s [MOD 11]) :
  ramanujanElevenSection r f = 0 := by
  ext n
  by_cases hn : n ≡ r [MOD 11]
  · have hns : ¬n ≡ s [MOD 11] := fun h => hrs (hn.symm.trans h)
    simp [hn, hf n hns]
  · simp [hn]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ramanujanElevenSection_homogeneous](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/RamanujanPartitionCongruenceModEleven.lean)
-/
@[path]
private lemma ramanujanElevenSection_homogeneous (r : ℕ) {s : ℕ}
  (f : PowerSeries (ZMod 11)) [hf : RamanujanElevenHomogeneous s f] :
  ramanujanElevenSection r f = if r ≡ s [MOD 11] then f else 0 := by
  by_cases hrs : r ≡ s [MOD 11]
  · rw [ite_eq_left hrs]
    apply ramanujanElevenSection_eq_self
    intro n hn
    apply hf.supported n
    intro hns
    exact hn (hns.trans hrs.symm)
  · rw [ite_eq_right hrs]
    exact ramanujanElevenSection_eq_zero hf.supported hrs

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ramanujanElevenSection_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/RamanujanPartitionCongruenceModEleven.lean)
-/
@[path]
private lemma ramanujanElevenSection_add (r : ℕ) (f g : PowerSeries (ZMod 11)) :
  ramanujanElevenSection r (f + g) =
    ramanujanElevenSection r f + ramanujanElevenSection r g := by
  ext n
  by_cases hn : n ≡ r [MOD 11]
  · simp [hn]
  · simp [hn]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ramanujanElevenSection_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/RamanujanPartitionCongruenceModEleven.lean)
-/
@[path]
private lemma ramanujanElevenSection_zero (r : ℕ) :
  ramanujanElevenSection r (0 : PowerSeries (ZMod 11)) = 0 := by
  ext n
  simp

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ramanujanElevenSection_C_mul](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/RamanujanPartitionCongruenceModEleven.lean)
-/
@[path]
private lemma ramanujanElevenSection_C_mul (r : ℕ) (a : ZMod 11)
  (f : PowerSeries (ZMod 11)) :
  ramanujanElevenSection r (PowerSeries.C a * f) =
    PowerSeries.C a * ramanujanElevenSection r f := by
  ext n
  by_cases hn : n ≡ r [MOD 11]
  · simp [hn, PowerSeries.coeff_C_mul]
  · simp [hn, PowerSeries.coeff_C_mul]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ramanujanElevenSection_mul_C](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/RamanujanPartitionCongruenceModEleven.lean)
-/
@[path]
private lemma ramanujanElevenSection_mul_C (r : ℕ) (f : PowerSeries (ZMod 11))
  (a : ZMod 11) :
  ramanujanElevenSection r (f * PowerSeries.C a) =
    ramanujanElevenSection r f * PowerSeries.C a := by
  ext n
  by_cases hn : n ≡ r [MOD 11]
  · simp [hn, PowerSeries.coeff_mul_C]
  · simp [hn, PowerSeries.coeff_mul_C]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ramanujanElevenSection_mul_of_supported_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/RamanujanPartitionCongruenceModEleven.lean)
-/
@[path]
private lemma ramanujanElevenSection_mul_of_supported_zero (r : ℕ)
  {g : PowerSeries (ZMod 11)} (hg : ramanujanElevenSupported 0 g)
  (f : PowerSeries (ZMod 11)) :
  ramanujanElevenSection r (g * f) = g * ramanujanElevenSection r f := by
  ext n
  rw [ramanujanElevenCoeff_section, PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  by_cases hn : n ≡ r [MOD 11]
  · rw [ite_eq_left hn]
    apply Finset.sum_congr rfl
    intro ab hab
    obtain ⟨a, b⟩ := ab
    have habn : a + b = n := Finset.mem_antidiagonal.mp hab
    by_cases ha : a ≡ 0 [MOD 11]
    · have hb : b ≡ r [MOD 11] := by
      have h0b : 0 + b ≡ a + b [MOD 11] := (ha.add (Nat.ModEq.refl b)).symm
      have habr : a + b ≡ r [MOD 11] := by simpa [habn] using hn
      simpa using h0b.trans habr
      simp [hb]
    · rw [hg a ha, zero_mul, zero_mul]
  · rw [ite_eq_right hn]
    symm
    apply Finset.sum_eq_zero
    intro ab hab
    obtain ⟨a, b⟩ := ab
    have habn : a + b = n := Finset.mem_antidiagonal.mp hab
    by_cases ha : a ≡ 0 [MOD 11]
    · have hb : ¬b ≡ r [MOD 11] := by
      intro hb
      apply hn
      rw [← habn]
      simpa using ha.add hb
      simp [hb]
    · rw [hg a ha, zero_mul]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ramanujanElevenSection_jacobi_pow_four_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/RamanujanPartitionCongruenceModEleven.lean)
-/
@[path]
private lemma ramanujanElevenSection_jacobi_pow_four_eq_zero (r : ℕ)
  (hr : ¬(r ≡ 0 [MOD 11] ∨ r ≡ 1 [MOD 11] ∨ r ≡ 2 [MOD 11] ∨
    r ≡ 4 [MOD 11] ∨ r ≡ 5 [MOD 11] ∨ r ≡ 7 [MOD 11])) :
  ramanujanElevenSection r (ramanujanElevenJacobi ^ 4) = 0 := by
  rw [ramanujanElevenJacobi_pow_four,
    ramanujanElevenSection_mul_of_supported_zero r ramanujanElevenExpandEuler_supported,
    ramanujanElevenSection_euler_eq_zero r hr, mul_zero]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ramanujanElevenTriangle_residue_or_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/RamanujanPartitionCongruenceModEleven.lean)
-/
@[path]
private lemma ramanujanElevenTriangle_residue_or_dvd (t : ℕ) :
  (t + 1).choose 2 ≡ 0 [MOD 11] ∨ (t + 1).choose 2 ≡ 1 [MOD 11] ∨
    (t + 1).choose 2 ≡ 3 [MOD 11] ∨ (t + 1).choose 2 ≡ 6 [MOD 11] ∨
      (t + 1).choose 2 ≡ 10 [MOD 11] ∨ 11 ∣ 2 * t + 1 := by
  have h2T := two_mul_choose_two_succ t
  have hcast : (2 : ZMod 11) * (((t + 1).choose 2 : ℕ) : ZMod 11) =
    (t : ZMod 11) * ((t : ZMod 11) + 1) := by
    have hcc : (((2 * (t + 1).choose 2 : ℕ)) : ZMod 11) =
      (((t * (t + 1) : ℕ)) : ZMod 11) := by
      rw [h2T]
    push_cast at hcc
    simpa using hcc
  have key : ∀ x y : ZMod 11, 2 * y = x * (x + 1) →
    y = 0 ∨ y = 1 ∨ y = 3 ∨ y = 6 ∨ y = 10 ∨ 2 * x + 1 = 0 := by
    decide
  rcases key (t : ZMod 11) (((t + 1).choose 2 : ℕ) : ZMod 11) hcast with
    h | h | h | h | h | h
  · exact Or.inl ((ZMod.natCast_eq_natCast_iff _ _ _).mp h)
  · exact Or.inr <| Or.inl ((ZMod.natCast_eq_natCast_iff _ _ _).mp h)
  · exact Or.inr <| Or.inr <| Or.inl ((ZMod.natCast_eq_natCast_iff _ _ _).mp h)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl
    ((ZMod.natCast_eq_natCast_iff _ _ _).mp h)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
    ((ZMod.natCast_eq_natCast_iff _ _ _).mp h)
  · right
    right
    right
    right
    right
    have hzero : (((2 * t + 1 : ℕ)) : ZMod 11) = 0 := by
      push_cast
      simpa using h
    rwa [ZMod.natCast_eq_zero_iff] at hzero

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ramanujanElevenJacobi_coeff_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/RamanujanPartitionCongruenceModEleven.lean)
-/
@[path]
private lemma ramanujanElevenJacobi_coeff_eq_zero {n : ℕ}
  (hn : ¬(n ≡ 0 [MOD 11] ∨ n ≡ 1 [MOD 11] ∨ n ≡ 3 [MOD 11] ∨
    n ≡ 6 [MOD 11] ∨ n ≡ 10 [MOD 11])) :
  PowerSeries.coeff n ramanujanElevenJacobi = 0 := by
  rw [ramanujanElevenJacobi, PowerSeries.coeff_map]
  by_cases ht : ∃ t : ℕ, (t + 1).choose 2 = n
  · obtain ⟨t, rfl⟩ := ht
    rcases ramanujanElevenTriangle_residue_or_dvd t with
      h | h | h | h | h | hdiv
    · exact False.elim (hn (Or.inl h))
    · exact False.elim (hn (Or.inr <| Or.inl h))
    · exact False.elim (hn (Or.inr <| Or.inr <| Or.inl h))
    · exact False.elim (hn (Or.inr <| Or.inr <| Or.inr <| Or.inl h))
    · exact False.elim (hn (Or.inr <| Or.inr <| Or.inr <| Or.inr h))
    · rw [coeff_jacobiCubeSeries_triangle, map_mul]
      have h11 : (11 : ℤ) ∣ 2 * (t : ℤ) + 1 := by
        have h11' : (11 : ℤ) ∣ (((2 * t + 1 : ℕ)) : ℤ) :=
          Int.natCast_dvd_natCast.mpr hdiv
        have hcast : (((2 * t + 1 : ℕ)) : ℤ) = 2 * (t : ℤ) + 1 := by
          push_cast
          ring
        rwa [hcast] at h11'
      have hzero : (((2 * (t : ℤ) + 1 : ℤ)) : ZMod 11) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h11
      have hzero' : (Int.castRingHom (ZMod 11)) (2 * (t : ℤ) + 1) = 0 := hzero
      rw [hzero', mul_zero]
  · rw [coeff_jacobiCubeSeries_eq_zero (fun t h => ht ⟨t, h⟩), map_zero]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ramanujanElevenJacobi_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/RamanujanPartitionCongruenceModEleven.lean)
-/
@[path]
private lemma ramanujanElevenJacobi_decomposition :
  ramanujanElevenJacobi =
    ramanujanElevenJ 0 + ramanujanElevenJ 1 + ramanujanElevenJ 3 +
      ramanujanElevenJ 6 + ramanujanElevenJ 10 := by
  ext n
  simp only [ramanujanElevenJ, map_add, ramanujanElevenCoeff_section]
  by_cases h0 : n ≡ 0 [MOD 11]
  · have h1 : ¬n ≡ 1 [MOD 11] := fun h =>
    (by decide : ¬0 ≡ 1 [MOD 11]) (h0.symm.trans h)
    have h3 : ¬n ≡ 3 [MOD 11] := fun h =>
      (by decide : ¬0 ≡ 3 [MOD 11]) (h0.symm.trans h)
    have h6 : ¬n ≡ 6 [MOD 11] := fun h =>
      (by decide : ¬0 ≡ 6 [MOD 11]) (h0.symm.trans h)
    have h10 : ¬n ≡ 10 [MOD 11] := fun h =>
      (by decide : ¬0 ≡ 10 [MOD 11]) (h0.symm.trans h)
    simp [h0, h1, h3, h6, h10]
  · by_cases h1 : n ≡ 1 [MOD 11]
    · have h3 : ¬n ≡ 3 [MOD 11] := fun h =>
      (by decide : ¬1 ≡ 3 [MOD 11]) (h1.symm.trans h)
      have h6 : ¬n ≡ 6 [MOD 11] := fun h =>
        (by decide : ¬1 ≡ 6 [MOD 11]) (h1.symm.trans h)
      have h10 : ¬n ≡ 10 [MOD 11] := fun h =>
        (by decide : ¬1 ≡ 10 [MOD 11]) (h1.symm.trans h)
      simp [h0, h1, h3, h6, h10]
    · by_cases h3 : n ≡ 3 [MOD 11]
      · have h6 : ¬n ≡ 6 [MOD 11] := fun h =>
        (by decide : ¬3 ≡ 6 [MOD 11]) (h3.symm.trans h)
        have h10 : ¬n ≡ 10 [MOD 11] := fun h =>
          (by decide : ¬3 ≡ 10 [MOD 11]) (h3.symm.trans h)
        simp [h0, h1, h3, h6, h10]
      · by_cases h6 : n ≡ 6 [MOD 11]
        · have h10 : ¬n ≡ 10 [MOD 11] := fun h =>
          (by decide : ¬6 ≡ 10 [MOD 11]) (h6.symm.trans h)
          simp [h0, h1, h3, h6, h10]
        · by_cases h10 : n ≡ 10 [MOD 11]
          · simp [h0, h1, h3, h6, h10]
          · have hz := ramanujanElevenJacobi_coeff_eq_zero
            (n := n) (by tauto)
            simp [h0, h1, h3, h6, h10, hz]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ramanujanElevenR3_eq_three_mul_section](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/RamanujanPartitionCongruenceModEleven.lean)
-/
@[path]
private lemma ramanujanElevenR3_eq_three_mul_section :
  ramanujanElevenR3 =
    3 * ramanujanElevenSection 3 (ramanujanElevenJacobi ^ 4) := by
  rw [ramanujanElevenJacobi_decomposition]
  unfold ramanujanElevenR3
  have : CharP (PowerSeries (ZMod 11)) 11 := inferInstance
  ring_nf
  simp +decide only [ramanujanElevenSection_add, ramanujanElevenSection_homogeneous,
    ite_true, ite_false]
  ring_nf
  reduce_mod_char!

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ramanujanElevenR3_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/RamanujanPartitionCongruenceModEleven.lean)
-/
@[path]
private lemma ramanujanElevenR3_eq_zero : ramanujanElevenR3 = 0 := by
  rw [ramanujanElevenR3_eq_three_mul_section,
    ramanujanElevenSection_jacobi_pow_four_eq_zero 3 (by decide), mul_zero]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ramanujanElevenR6_eq_three_mul_section](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/RamanujanPartitionCongruenceModEleven.lean)
-/
@[path]
private lemma ramanujanElevenR6_eq_three_mul_section :
  ramanujanElevenR6 =
    3 * ramanujanElevenSection 6 (ramanujanElevenJacobi ^ 4) := by
  rw [ramanujanElevenJacobi_decomposition]
  unfold ramanujanElevenR6
  have : CharP (PowerSeries (ZMod 11)) 11 := inferInstance
  ring_nf
  simp +decide only [ramanujanElevenSection_add, ramanujanElevenSection_homogeneous,
    ite_true, ite_false]
  ring_nf
  reduce_mod_char!

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ramanujanElevenR6_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/RamanujanPartitionCongruenceModEleven.lean)
-/
@[path]
private lemma ramanujanElevenR6_eq_zero : ramanujanElevenR6 = 0 := by
  rw [ramanujanElevenR6_eq_three_mul_section,
    ramanujanElevenSection_jacobi_pow_four_eq_zero 6 (by decide), mul_zero]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ramanujanElevenR8_eq_three_mul_section](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/RamanujanPartitionCongruenceModEleven.lean)
-/
@[path]
private lemma ramanujanElevenR8_eq_three_mul_section :
  ramanujanElevenR8 =
    3 * ramanujanElevenSection 8 (ramanujanElevenJacobi ^ 4) := by
  rw [ramanujanElevenJacobi_decomposition]
  unfold ramanujanElevenR8
  have : CharP (PowerSeries (ZMod 11)) 11 := inferInstance
  ring_nf
  simp +decide only [ramanujanElevenSection_add, ramanujanElevenSection_homogeneous,
    ite_true, ite_false]
  ring_nf
  reduce_mod_char!

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ramanujanElevenR8_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/RamanujanPartitionCongruenceModEleven.lean)
-/
@[path]
private lemma ramanujanElevenR8_eq_zero : ramanujanElevenR8 = 0 := by
  rw [ramanujanElevenR8_eq_three_mul_section,
    ramanujanElevenSection_jacobi_pow_four_eq_zero 8 (by decide), mul_zero]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ramanujanElevenR9_eq_three_mul_section](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/RamanujanPartitionCongruenceModEleven.lean)
-/
@[path]
private lemma ramanujanElevenR9_eq_three_mul_section :
  ramanujanElevenR9 =
    3 * ramanujanElevenSection 9 (ramanujanElevenJacobi ^ 4) := by
  rw [ramanujanElevenJacobi_decomposition]
  unfold ramanujanElevenR9
  have : CharP (PowerSeries (ZMod 11)) 11 := inferInstance
  ring_nf
  simp +decide only [ramanujanElevenSection_add, ramanujanElevenSection_homogeneous,
    ite_true, ite_false]
  ring_nf
  reduce_mod_char!

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ramanujanElevenR9_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/RamanujanPartitionCongruenceModEleven.lean)
-/
@[path]
private lemma ramanujanElevenR9_eq_zero : ramanujanElevenR9 = 0 := by
  rw [ramanujanElevenR9_eq_three_mul_section,
    ramanujanElevenSection_jacobi_pow_four_eq_zero 9 (by decide), mul_zero]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ramanujanElevenR10_eq_three_mul_section](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/RamanujanPartitionCongruenceModEleven.lean)
-/
@[path]
private lemma ramanujanElevenR10_eq_three_mul_section :
  ramanujanElevenR10 =
    3 * ramanujanElevenSection 10 (ramanujanElevenJacobi ^ 4) := by
  rw [ramanujanElevenJacobi_decomposition]
  unfold ramanujanElevenR10
  have : CharP (PowerSeries (ZMod 11)) 11 := inferInstance
  ring_nf
  simp +decide only [ramanujanElevenSection_add, ramanujanElevenSection_homogeneous,
    ite_true, ite_false]
  ring_nf
  reduce_mod_char!

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ramanujanElevenR10_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/RamanujanPartitionCongruenceModEleven.lean)
-/
@[path]
private lemma ramanujanElevenR10_eq_zero : ramanujanElevenR10 = 0 := by
  rw [ramanujanElevenR10_eq_three_mul_section,
    ramanujanElevenSection_jacobi_pow_four_eq_zero 10 (by decide), mul_zero]
set_option maxRecDepth 10000 in

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ramanujanElevenHirschhorn_identity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/RamanujanPartitionCongruenceModEleven.lean)
-/
@[path]
private lemma ramanujanElevenHirschhorn_identity :
  ramanujanElevenSection 6 (ramanujanElevenJacobi ^ 7) =
    (7 * (ramanujanElevenJ 1 * ramanujanElevenJ 3 * ramanujanElevenJ 10) +
      5 * (ramanujanElevenJ 0 ^ 2 * ramanujanElevenJ 3) +
      7 * ramanujanElevenJ 1 ^ 3) * ramanujanElevenR3 +
      (7 * ramanujanElevenJ 0 ^ 3 +
        7 * (ramanujanElevenJ 0 * ramanujanElevenJ 1 * ramanujanElevenJ 10) +
        5 * (ramanujanElevenJ 6 ^ 2 * ramanujanElevenJ 10)) * ramanujanElevenR6 +
      (7 * (ramanujanElevenJ 0 * ramanujanElevenJ 3 * ramanujanElevenJ 6) +
        5 * (ramanujanElevenJ 0 * ramanujanElevenJ 10 ^ 2) +
        7 * ramanujanElevenJ 3 ^ 3) * ramanujanElevenR8 +
      (5 * (ramanujanElevenJ 1 ^ 2 * ramanujanElevenJ 6) +
        7 * (ramanujanElevenJ 3 * ramanujanElevenJ 6 * ramanujanElevenJ 10) +
        7 * ramanujanElevenJ 10 ^ 3) * ramanujanElevenR9 +
      (7 * (ramanujanElevenJ 0 * ramanujanElevenJ 1 * ramanujanElevenJ 6) +
        5 * (ramanujanElevenJ 1 * ramanujanElevenJ 3 ^ 2) +
        7 * ramanujanElevenJ 6 ^ 3) * ramanujanElevenR10 := by
  rw [ramanujanElevenJacobi_decomposition]
  unfold ramanujanElevenR3 ramanujanElevenR6 ramanujanElevenR8
    ramanujanElevenR9 ramanujanElevenR10
  have : CharP (PowerSeries (ZMod 11)) 11 := inferInstance
  ring_nf
  simp +decide only [ramanujanElevenSection_add, ramanujanElevenSection_homogeneous,
    ite_true, ite_false]
  ring_nf
  have h11 : (11 : PowerSeries (ZMod 11)) = 0 := CharP.cast_eq_zero _ 11
  have h21 : (21 : PowerSeries (ZMod 11)) = 54 := by
    linear_combination -3 * h11
  have h140 : (140 : PowerSeries (ZMod 11)) = 19 := by
    linear_combination 11 * h11
  have h210 : (210 : PowerSeries (ZMod 11)) = 56 := by
    linear_combination 14 * h11
  have h420 : (420 : PowerSeries (ZMod 11)) = 112 := by
    linear_combination 28 * h11
  have h630 : (630 : PowerSeries (ZMod 11)) = 113 := by
    linear_combination 47 * h11
  rw [h21, h140, h210, h420, h630]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ramanujanElevenSection_jacobi_pow_seven_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/RamanujanPartitionCongruenceModEleven.lean)
-/
@[path]
private lemma ramanujanElevenSection_jacobi_pow_seven_eq_zero :
  ramanujanElevenSection 6 (ramanujanElevenJacobi ^ 7) = 0 := by
  rw [ramanujanElevenHirschhorn_identity, ramanujanElevenR3_eq_zero,
    ramanujanElevenR6_eq_zero, ramanujanElevenR8_eq_zero,
    ramanujanElevenR9_eq_zero, ramanujanElevenR10_eq_zero]
  simp only [mul_zero, add_zero]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ramanujanElevenSection_euler_pow_ten_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/RamanujanPartitionCongruenceModEleven.lean)
-/
@[path]
private lemma ramanujanElevenSection_euler_pow_ten_eq_zero :
  ramanujanElevenSection 6 (ramanujanElevenEuler ^ 10) = 0 := by
  have hprod : PowerSeries.expand 11 (by decide) ramanujanElevenEuler *
    ramanujanElevenSection 6 (ramanujanElevenEuler ^ 10) = 0 := by
    rw [← ramanujanElevenSection_mul_of_supported_zero 6
      ramanujanElevenExpandEuler_supported, ← ramanujanElevenJacobi_pow_seven,
      ramanujanElevenSection_jacobi_pow_seven_eq_zero]
  have hexpand : PowerSeries.expand 11 (by decide) ramanujanElevenEuler ≠ 0 := by
    intro hzero
    have hcoeff := congrArg (PowerSeries.coeff 0) hzero
    have hcoeff' : PowerSeries.coeff 0 ramanujanElevenEuler = 0 := by
      simpa using hcoeff
    have heuler : PowerSeries.coeff 0 ramanujanElevenEuler = 1 := by
      have hpentagonal : pentagonal (0 : ℤ) = 0 := by
        have h := two_mul_natCast_pentagonal (0 : ℤ)
        norm_num at h
        omega
      rw [ramanujanElevenEuler, PowerSeries.coeff_map]
      rw [← hpentagonal, PowerSeries.coeff_pentagonalSeries_pentagonal]
      norm_num
    rw [heuler] at hcoeff'
    exact one_ne_zero hcoeff'
  exact (mul_eq_zero.mp hprod).resolve_left hexpand

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ramanujanEleven_dvd_coeff_pentagonalSeries_pow_ten](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/RamanujanPartitionCongruenceModEleven.lean)
-/
@[path]
private lemma ramanujanEleven_dvd_coeff_pentagonalSeries_pow_ten (m : ℕ) :
  (11 : ℤ) ∣ PowerSeries.coeff (11 * m + 6)
    (PowerSeries.pentagonalSeries ℤ ^ 10) := by
  have hn : 11 * m + 6 ≡ 6 [MOD 11] := by
    simp [Nat.ModEq]
  have hcoeff : PowerSeries.coeff (11 * m + 6)
    (ramanujanElevenEuler ^ 10) = 0 := by
    have hzero := congrArg (PowerSeries.coeff (11 * m + 6))
      ramanujanElevenSection_euler_pow_ten_eq_zero
    simpa [hn] using hzero
  rw [ramanujanElevenEuler, ← map_pow, PowerSeries.coeff_map] at hcoeff
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hcoeff

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ramanujan_partition_congruence_mod_eleven](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/RamanujanPartitionCongruenceModEleven.lean)
-/
@[path]
lemma ramanujan_partition_congruence_mod_eleven
  {m : ℕ} :
-- imply
  Fintype.card (Nat.Partition (11 * m + 6)) ≡ 0 [MOD 11] := by
-- proof
  rw [Nat.modEq_zero_iff_dvd]
  apply dvd_partitionFunction_of_dvd_coeff_pentagonalSeries_pow 11 6 (by decide) ?_ m
  intro n
  simpa using ramanujanEleven_dvd_coeff_pentagonalSeries_pow_ten n

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
