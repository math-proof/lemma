import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.Buildings.code.AffineCoxeter.TitsCone.Part3
open Finset BigOperators CoxeterGroup TitsCone


namespace TitsCone

/--
[dualSigma_on_s](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsCone.lean)
-/
@[path]
private lemma dualSigma_on_s
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s : B}
  {x : B → ℝ} :
-- imply
  dualSigma M s x s = -x s := by
-- proof
  simp only [dualSigma, formVal_diag]
  ring

end TitsCone

namespace CoxeterGroup

/--
[bilinForm_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsCone.lean)
-/
@[path]
private lemma bilinForm_zero
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B} :
-- imply
  bilinForm M 0 0 = 0 := by
-- proof
  simp [bilinForm]

end CoxeterGroup

namespace CoxeterGroup

/--
[IsAffineCoxeterForm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsCone.lean)
-/
@[path]
private lemma IsAffineCoxeterForm
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B} :
-- imply
  (FormIndecomposable (fun s t => formVal M s t) ∧ (∀ v : B → ℝ, bilinForm M v v ≥ 0) ∧ ¬((∀ v : B → ℝ, bilinForm M v v ≥ 0) ∧ (∀ v : B → ℝ, bilinForm M v v = 0 → v = 0))) ↔ (FormIndecomposable (fun s t => formVal M s t) ∧ (∀ v : B → ℝ, bilinForm M v v ≥ 0) ∧ (∃ v : B → ℝ, v ≠ 0 ∧ bilinForm M v v = 0)) := by
-- proof
  constructor
  ·
    rintro ⟨hI, hPSD, hNotPD⟩
    refine ⟨hI, hPSD, ?_⟩
    push Not at hNotPD
    obtain ⟨v, hv1, hv2⟩ := hNotPD hPSD
    exact ⟨v, hv2, le_antisymm (by linarith [hPSD v]) (hPSD v)⟩
  ·
    rintro ⟨hI, hPSD, v, hv, hfv⟩
    refine ⟨hI, hPSD, ?_⟩
    rintro ⟨_, hPD⟩
    exact hv (hPD v hfv)
end CoxeterGroup
section PerronFrobenius


/--
[perronFrobenius_kernel_dim_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsCone.lean)
-/
@[path]
private lemma perronFrobenius_kernel_dim_one
  [DecidableEq B]
  [Fintype B]
  [Nonempty B]
  {f : B → B → ℝ} [hPF : PerronFrobeniusProperty f]
-- given
  (hIndecomp : CoxeterGroup.FormIndecomposable f)
  (hPSD : ∀ v : B → ℝ, ∑ s, ∑ t, v s * f s t * v t ≥ 0)
  (hNotPD : ∃ v : B → ℝ, v ≠ 0 ∧ ∑ s, ∑ t, v s * f s t * v t = 0)
  (hOffDiag : ∀ s t, s ≠ t → f s t ≤ 0) :
-- imply
  ∃ v : B → ℝ, (∀ s, v s > 0) ∧ (∀ w : B → ℝ, (∑ s, ∑ t, w s * f s t * w t = 0) → ∃ c : ℝ, w = fun b => c * v b) :=
-- proof
  hPF.kernel_span hIndecomp hPSD hNotPD hOffDiag

/--
[perronFrobenius_submatrix_pos_def](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsCone.lean)
-/
@[path]
private lemma perronFrobenius_submatrix_pos_def
  [DecidableEq B]
  [Fintype B]
  [Nonempty B]
  {f : B → B → ℝ} [hPF : PerronFrobeniusProperty f]
  {b₀ : B}
-- given
  (hIndecomp : CoxeterGroup.FormIndecomposable f)
  (hPSD : ∀ v : B → ℝ, ∑ s, ∑ t, v s * f s t * v t ≥ 0)
  (hOffDiag : ∀ s t, s ≠ t → f s t ≤ 0) :
-- imply
  ∀ w : B → ℝ, w b₀ = 0 → w ≠ 0 → ∑ s, ∑ t, w s * f s t * w t > 0 := by
-- proof
  intro w hw hne
  by_contra hle
  simp only [not_lt] at hle
  have hpsd_w := hPSD w
  have hw_zero : ∑ s, ∑ t, w s * f s t * w t = 0 := le_antisymm hle hpsd_w
  if hPD : ∀ v : B → ℝ, v ≠ 0 → ∑ s, ∑ t, v s * f s t * v t > 0 then
    exact absurd hw_zero (ne_of_gt (hPD w hne))
  else
    simp only [not_forall, not_lt, exists_prop] at hPD
    obtain ⟨v₀, hv₀_ne, hv₀_le⟩ := hPD
    have hNotPD : ∃ v : B → ℝ, v ≠ 0 ∧ ∑ s, ∑ t, v s * f s t * v t = 0 :=
      ⟨v₀, hv₀_ne, le_antisymm hv₀_le (hPSD v₀)⟩
    obtain ⟨v, hv_pos, hv_span⟩ := hPF.kernel_span hIndecomp hPSD hNotPD hOffDiag
    obtain ⟨c, hc⟩ := hv_span w hw_zero
    have hcv : w b₀ = c * v b₀ := congr_fun hc b₀
    rw [hw] at hcv
    have hc_zero : c = 0 := by
      obtain h | h := mul_eq_zero.mp hcv.symm
      · exact h
      · linarith [hv_pos b₀]
    have : w = 0 := by
      ext b; have := congr_fun hc b; simp [this, hc_zero]
    exact hne this
end PerronFrobenius
section Spherical

/--
[spherical_implies_finite_group](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsCone.lean)
-/
@[path]
private lemma spherical_implies_finite_group
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B} [hSF : SphericalFiniteProperty M]
-- given
  (h : ∀ v : B → ℝ, v ≠ 0 → CoxeterGroup.bilinForm M v v > 0) :
-- imply
  Finite M.Group :=
-- proof
  hSF.finite_of_pos_def h
end Spherical
section AffineProper

/--
[extendByZero_outside](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsCone.lean)
-/
@[path]
private lemma extendByZero_outside
  [DecidableEq B]
  [Fintype B]
  [Nonempty B]
  {I : Finset B}
  {b : B}
  {v : ↥I → ℝ}
-- given
  (hb : b ∉ I) :
-- imply
  extendByZero I v b = 0 := by
-- proof
  simp [extendByZero, hb]

/--
[extendByZero_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsCone.lean)
-/
@[path]
private lemma extendByZero_ne_zero
  [DecidableEq B]
  [Fintype B]
  [Nonempty B]
  {I : Finset B}
  {v : ↥I → ℝ}
-- given
  (hv : v ≠ 0) :
-- imply
  extendByZero I v ≠ 0 := by
-- proof
  intro h
  apply hv
  ext ⟨b, hb⟩
  have := congr_fun h b
  simp [extendByZero, hb] at this
  exact this

/--
[sum_restrict_of_vanish](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsCone.lean)
-/
@[path]
private lemma sum_restrict_of_vanish
  [DecidableEq B]
  [Fintype B]
  [Nonempty B]
  {I : Finset B}
  {f : B → ℝ}
-- given
  (hf : ∀ b, b ∉ I → f b = 0) :
-- imply
  ∑ b : B, f b = ∑ b : ↥I, f b.1 := by
-- proof
  rw [Finset.sum_coe_sort]
  symm
  apply Finset.sum_subset (Finset.subset_univ I)
  intro x _ hxI; exact hf x hxI

end AffineProper

namespace GeomRealization

/--
[titsFundamentalClosure_subset_titsCone](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsCone.lean)
-/
@[path]
private lemma titsFundamentalClosure_subset_titsCone_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B} :
-- imply
  titsFundamentalClosure M ⊆ titsConeSet M := by
-- proof
  apply TitsCone.titsFundamentalClosure_subset_titsCone M

/--
[dualSigma_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsCone.lean)
-/
@[path]
private lemma dualSigma_involutive_eq
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {s : B}
  {x : B → ℝ} :
-- imply
  dualSigma M s (dualSigma M s x) = x := by
-- proof
  apply TitsCone.dualSigma_involutive M s x


-- created on 2026-10-23
-- updated on 2026-10-26
