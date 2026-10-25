import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.AlgebraicGeometryI.code.SheafCohomology.Part2
open SheafCohomology
open CohomologyP1


namespace SheafCohomology

/--
[locProductMap_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafCohomology.lean)
-/
@[path]
lemma locProductMap_injective
  [CommRing A]
  [AddCommGroup M]
  [Module A M]
  {f g : A}
-- given
  (hfg : Ideal.span {f, g} = ⊤) :
-- imply
  Function.Injective (locProductMap (M := M) f g) := by
-- proof
  rw [← LinearMap.ker_eq_bot]
  ext m
  simp only [LinearMap.mem_ker, Submodule.mem_bot]
  constructor
  · intro hm
    have hf : (LocalizedModule.mkLinearMap (Submonoid.powers f) M) m = 0 := by
      have := congr_arg Prod.fst hm; simp [locProductMap] at this; exact this
    have hg : (LocalizedModule.mkLinearMap (Submonoid.powers g) M) m = 0 := by
      have := congr_arg Prod.snd hm; simp [locProductMap] at this; exact this
    have hf_ker : m ∈ (LocalizedModule.mkLinearMap (Submonoid.powers f) M).ker :=
      LinearMap.mem_ker.mpr hf
    have hg_ker : m ∈ (LocalizedModule.mkLinearMap (Submonoid.powers g) M).ker :=
      LinearMap.mem_ker.mpr hg
    rw [LocalizedModule.mem_ker_mkLinearMap_iff] at hf_ker hg_ker
    obtain ⟨_, ⟨n, rfl⟩, hrf⟩ := hf_ker
    obtain ⟨_, ⟨k, rfl⟩, hrg⟩ := hg_ker
    change f ^ n • m = 0 at hrf
    change g ^ k • m = 0 at hrg
    have h_pow : Ideal.span ((fun x => x ^ (n + k)) '' {f, g}) = ⊤ :=
      Ideal.span_pow_eq_top {f, g} hfg (n + k)
    have h1 : (1 : A) ∈ Ideal.span ((fun x => x ^ (n + k)) '' {f, g}) := by
      rw [h_pow]; exact Submodule.mem_top
    simp only [Set.image_insert_eq, Set.image_singleton] at h1
    rw [Ideal.mem_span_pair] at h1
    obtain ⟨a, b, hab⟩ := h1
    have hfN : f ^ (n + k) • m = 0 := by
      rw [show f ^ (n + k) = f ^ k * f ^ n from by ring, mul_smul, hrf, smul_zero]
    have hgN : g ^ (n + k) • m = 0 := by
      rw [show g ^ (n + k) = g ^ n * g ^ k from by ring, mul_smul, hrg, smul_zero]
    have : (1 : A) • m = 0 := by
      rw [← hab, add_smul, mul_smul, mul_smul, hfN, hgN, smul_zero, smul_zero, add_zero]
    rwa [one_smul] at this
  · intro hm; simp [hm, locProductMap, map_zero]

end SheafCohomology

namespace SheafCohomology

/--
[localization_away_flat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafCohomology.lean)
-/
@[path]
lemma localization_away_flat
  {A : Type*}
  [CommRing A]
  {f : A} :
-- imply
  Module.Flat A (Localization.Away f) :=
-- proof
  IsLocalization.flat (Localization.Away f) (Submonoid.powers f)

end SheafCohomology

namespace SheafCohomology

/--
[cech_dsquared_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafCohomology.lean)
-/
@[path]
lemma cech_dsquared_zero
  {A : Type*}
  [CommRing A]
  {f g : A}
  {a : A} :
-- imply
  cechMapFromF A f g (algebraMap A (Localization.Away f) a) - cechMapFromG A f g (algebraMap A (Localization.Away g) a) = 0 := by
-- proof
  simp only [cechMapFromF, cechMapFromG, Localization.awayLift,
    IsLocalization.Away.lift_eq]
  ring

end SheafCohomology

namespace SheafCohomology

/--
[cechMapFromF_algebraMap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafCohomology.lean)
-/
@[path]
lemma cechMapFromF_algebraMap
  {A : Type*}
  [CommRing A]
  {f g : A}
  {a : A} :
-- imply
  cechMapFromF A f g (algebraMap A _ a) = algebraMap A _ a := by
-- proof
  simp [cechMapFromF, Localization.awayLift, IsLocalization.Away.lift_eq]

end SheafCohomology

namespace SheafCohomology

/--
[cechMapFromG_algebraMap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafCohomology.lean)
-/
@[path]
lemma cechMapFromG_algebraMap
  {A : Type*}
  [CommRing A]
  {f g : A}
  {a : A} :
-- imply
  cechMapFromG A f g (algebraMap A _ a) = algebraMap A _ a := by
-- proof
  simp [cechMapFromG, Localization.awayLift, IsLocalization.Away.lift_eq]

end SheafCohomology

namespace SheafCohomology

/--
[cechMapFromF_invSelf_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafCohomology.lean)
-/
@[path]
lemma cechMapFromF_invSelf_mul
  {A : Type*}
  [CommRing A]
  {f g : A} :
-- imply
  cechMapFromF A f g (IsLocalization.Away.invSelf (S := Localization.Away f) f) * algebraMap A (Localization.Away (f * g)) f = 1 := by
-- proof
  conv_lhs => rw [← cechMapFromF_algebraMap A f g f]
  rw [← map_mul, show IsLocalization.Away.invSelf f *
    algebraMap A (Localization.Away f) f = 1 from by
    rw [mul_comm]; exact IsLocalization.Away.mul_invSelf f]
  exact map_one _

end SheafCohomology

namespace SheafCohomology

/--
[cechMapFromG_invSelf_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafCohomology.lean)
-/
@[path]
lemma cechMapFromG_invSelf_mul
  {A : Type*}
  [CommRing A]
  {f g : A} :
-- imply
  cechMapFromG A f g (IsLocalization.Away.invSelf (S := Localization.Away g) g) * algebraMap A (Localization.Away (f * g)) g = 1 := by
-- proof
  conv_lhs => rw [← cechMapFromG_algebraMap A f g g]
  rw [← map_mul, show IsLocalization.Away.invSelf g *
    algebraMap A (Localization.Away g) g = 1 from by
    rw [mul_comm]; exact IsLocalization.Away.mul_invSelf g]
  exact map_one _

end SheafCohomology

namespace SheafCohomology

/--
[cechMapFromF_invSelf_pow_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafCohomology.lean)
-/
@[path]
lemma cechMapFromF_invSelf_pow_mul
  {A : Type*}
  [CommRing A]
  {f g : A}
  {n : ℕ} :
-- imply
  cechMapFromF A f g (IsLocalization.Away.invSelf (S := Localization.Away f) f ^ n) * algebraMap A (Localization.Away (f * g)) (f ^ n) = 1 := by
-- proof
  conv_lhs => rw [map_pow (algebraMap A _)]
  rw [map_pow (cechMapFromF A f g), ← mul_pow,
    cechMapFromF_invSelf_mul A f g, one_pow]

end SheafCohomology

namespace SheafCohomology

/--
[cechMapFromG_invSelf_pow_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafCohomology.lean)
-/
@[path]
lemma cechMapFromG_invSelf_pow_mul
  {A : Type*}
  [CommRing A]
  {f g : A}
  {n : ℕ} :
-- imply
  cechMapFromG A f g (IsLocalization.Away.invSelf (S := Localization.Away g) g ^ n) * algebraMap A (Localization.Away (f * g)) (g ^ n) = 1 := by
-- proof
  conv_lhs => rw [map_pow (algebraMap A _)]
  rw [map_pow (cechMapFromG A f g), ← mul_pow,
    cechMapFromG_invSelf_mul A f g, one_pow]

end SheafCohomology

namespace SheafCohomology

/--
[cechMapFromF_mul_fgpow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafCohomology.lean)
-/
@[path]
lemma cechMapFromF_mul_fgpow
  {A : Type*}
  [CommRing A]
  {f g : A}
  {c : A}
  {n : ℕ} :
-- imply
  cechMapFromF A f g (algebraMap A _ c * IsLocalization.Away.invSelf (S := Localization.Away f) f ^ n) * algebraMap A _ ((f * g) ^ n) = algebraMap A _ c * algebraMap A _ (g ^ n) := by
-- proof
  rw [map_mul, cechMapFromF_algebraMap, mul_assoc,
    show (f * g) ^ n = f ^ n * g ^ n from mul_pow f g n, map_mul,
    show cechMapFromF A f g _ *
      (algebraMap A _ (f ^ n) * algebraMap A _ (g ^ n)) =
      (cechMapFromF A f g _ * algebraMap A _ (f ^ n)) *
        algebraMap A _ (g ^ n) from by ring,
    cechMapFromF_invSelf_pow_mul A f g n, one_mul]

end SheafCohomology

namespace SheafCohomology

/--
[cechMapFromG_mul_fgpow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafCohomology.lean)
-/
@[path]
lemma cechMapFromG_mul_fgpow
  {A : Type*}
  [CommRing A]
  {f g : A}
  {c : A}
  {n : ℕ} :
-- imply
  cechMapFromG A f g (algebraMap A _ c * IsLocalization.Away.invSelf (S := Localization.Away g) g ^ n) * algebraMap A _ ((f * g) ^ n) = algebraMap A _ c * algebraMap A _ (f ^ n) := by
-- proof
  rw [map_mul, cechMapFromG_algebraMap, mul_assoc,
    show (f * g) ^ n = f ^ n * g ^ n from mul_pow f g n, map_mul,
    show cechMapFromG A f g _ *
      (algebraMap A _ (f ^ n) * algebraMap A _ (g ^ n)) =
      algebraMap A _ (f ^ n) *
        (cechMapFromG A f g _ * algebraMap A _ (g ^ n)) from by ring,
    cechMapFromG_invSelf_pow_mul A f g n, mul_one]

end SheafCohomology

namespace SheafCohomology

/--
[cech_H1_vanishes](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafCohomology.lean)
-/
@[path]
lemma cech_H1_vanishes
  {A : Type*}
  [CommRing A]
  {f g : A}
-- given
  (hfg : Ideal.span ({f, g} : Set A) = ⊤) :
-- imply
  Function.Surjective (cechDifferential A f g) := by
-- proof
  have hcop : IsCoprime f g := by
    have h1 : (1 : A) ∈ Ideal.span ({f, g} : Set A) := by
      rw [hfg]; exact Submodule.mem_top
    rw [Ideal.mem_span_pair] at h1
    obtain ⟨a, b, hab⟩ := h1
    exact ⟨a, b, hab⟩
  intro z
  obtain ⟨⟨a, ⟨_, ⟨n, rfl⟩⟩⟩, hz⟩ :=
    IsLocalization.surj (Submonoid.powers (f * g)) z
  simp only at hz
  obtain ⟨α, β, hαβ⟩ := hcop.pow (m := n) (n := n)
  let x_f := algebraMap A (Localization.Away f) (a * β) *
    IsLocalization.Away.invSelf (S := Localization.Away f) f ^ n
  let x_g := algebraMap A (Localization.Away g) (-(a * α)) *
    IsLocalization.Away.invSelf (S := Localization.Away g) g ^ n
  refine ⟨(x_f, x_g), ?_⟩
  show cechMapFromF A f g x_f - cechMapFromG A f g x_g = z
  have hunit : IsUnit (algebraMap A (Localization.Away (f * g))
    ((f * g) ^ n)) :=
    IsLocalization.map_units _
      (⟨(f * g) ^ n, n, rfl⟩ : Submonoid.powers (f * g))
  apply hunit.mul_right_cancel
  rw [hz, sub_mul, cechMapFromF_mul_fgpow A f g (a * β) n,
    cechMapFromG_mul_fgpow A f g (-(a * α)) n]
  simp only [← map_mul, ← map_sub]
  congr 1
  calc a * β * g ^ n - -(a * α) * f ^ n
    = a * β * g ^ n + a * α * f ^ n := by ring
    _ = a * 1 := by rw [← hαβ]; ring
    _ = a := mul_one _
section SerreDuality
open CohomologyP1

end SheafCohomology

/--
[isUnit_algebraMap_of_away_mul_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafCohomology.lean)
-/
@[path]
private lemma isUnit_algebraMap_of_away_mul_left_eq
  {A : Type*}
  [CommRing A]
  {f g : A} :
-- imply
  IsUnit (algebraMap A (Localization.Away (f * g)) f) := by
-- proof
  apply SheafCohomology.isUnit_algebraMap_of_away_mul_left A f g

/--
[isUnit_algebraMap_of_away_mul_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafCohomology.lean)
-/
@[path]
private lemma isUnit_algebraMap_of_away_mul_right_eq
  {A : Type*}
  [CommRing A]
  {f g : A} :
-- imply
  IsUnit (algebraMap A (Localization.Away (f * g)) g) := by
-- proof
  apply SheafCohomology.isUnit_algebraMap_of_away_mul_right A f g

/--
[finrank_H0_of_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafCohomology.lean)
-/
@[path]
private lemma finrank_H0_of_neg_eq
  {k : Type}
  [Field k]
  {n : ℤ}
-- given
  (hn : n < 0) :
-- imply
  Module.finrank k (H0 k n) = 0 := by
-- proof
  apply SheafCohomology.finrank_H0_of_neg k n hn

/--
[finrank_H0_of_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafCohomology.lean)
-/
@[path]
private lemma finrank_H0_of_nonneg_eq
  {k : Type}
  [Field k]
  {n : ℤ}
-- given
  (hn : 0 ≤ n) :
-- imply
  Module.finrank k (H0 k n) = (n + 1).toNat := by
-- proof
  apply SheafCohomology.finrank_H0_of_nonneg k n hn

/--
[finrank_H1_of_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafCohomology.lean)
-/
@[path]
private lemma finrank_H1_of_nonneg_eq
  {k : Type}
  [Field k]
  {n : ℤ}
-- given
  (hn : 0 ≤ n) :
-- imply
  Module.finrank k (H1 k n) = 0 := by
-- proof
  apply SheafCohomology.finrank_H1_of_nonneg k n hn

/--
[finrank_H1_of_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafCohomology.lean)
-/
@[path]
private lemma finrank_H1_of_neg_eq
  {k : Type}
  [Field k]
  {n : ℤ}
-- given
  (hn : n < 0) :
-- imply
  Module.finrank k (H1 k n) = (-n - 1).toNat := by
-- proof
  apply SheafCohomology.finrank_H1_of_neg k n hn

/--
[serre_duality_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafCohomology.lean)
-/
@[path]
private lemma serre_duality_nonneg_eq
  {k : Type}
  [Field k]
  {n : ℤ}
-- given
  (hn : 0 ≤ n) :
-- imply
  Module.finrank k (H1 k n) = Module.finrank k (H0 k (-2 - n)) := by
-- proof
  apply SheafCohomology.serre_duality_nonneg k n hn

/--
[serre_duality_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafCohomology.lean)
-/
@[path]
private lemma serre_duality_neg_eq
  {k : Type}
  [Field k]
  {n : ℤ}
-- given
  (hn : n < 0) :
-- imply
  Module.finrank k (H1 k n) = Module.finrank k (H0 k (-2 - n)) := by
-- proof
  apply SheafCohomology.serre_duality_neg k n hn

/--
[euler_characteristic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SheafCohomology.lean)
-/
@[path]
private lemma euler_characteristic_eq
  {k : Type}
  [Field k]
  {n : ℤ} :
-- imply
  (Module.finrank k (H0 k n) : ℤ) - (Module.finrank k (H1 k n) : ℤ) = n + 1 := by
-- proof
  apply SheafCohomology.euler_characteristic k n


-- created on 2026-10-23
