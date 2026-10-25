import Mathlib
import sympy.Basic
import Lemma.AlgebraicCurve.GluedPic0
import Lemma.AlgebraicCurve.AdelicIndex
import Lemma.Int.P2MUtil

open AlgebraicCurve AlgebraicCurve.GluedPic0

/--
[AlgebraicCurve_GluedPic0_nodeUnit_eq_zero_iff_of_constantsAreBase](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_GluedPic0_nodeUnit_eq_zero_iff_of_constantsAreBase.lean)
-/

private lemma aux_unglue {K F : Type*} [Field K] [Field F] [Algebra K F]
  (S : Finset (Place K F × Place K F))
  (hconst : ∀ g : F, g ≠ 0 → (∀ v : Place K F, v.ord g = 0) → ∃ c : K, algebraMap K F c = g)
  (w : ↥S → Additive Kˣ) :
  nodeUnit S w = 0 ↔ ∃ c : Kˣ, w = fun _ => Additive.ofMul c := by
  constructor
  ·
    rw [nodeUnit_apply, mk_eq_zero_iff]
    rintro ⟨g₁, g₂, a, b, hg₁, hg₂, h₁, h₂, hv, hw⟩
    obtain ⟨c₁, hc₁⟩ := hconst g₁ hg₁ fun v => by simpa using (h₁ v).symm
    obtain ⟨c₂, hc₂⟩ := hconst g₂ hg₂ fun v => by simpa using (h₂ v).symm
    have hc₁0 : c₁ ≠ 0 := by
      rintro rfl
      exact hg₁ (by rw [← hc₁, map_zero])
    have hc₂0 : c₂ ≠ 0 := by
      rintro rfl
      exact hg₂ (by rw [← hc₂, map_zero])
    have hv₁ : ∀ s : ↥S, (s : Place K F × Place K F).1.HasValue g₁ c₁ := fun s => by
      simpa only [hc₁] using (s : Place K F × Place K F).1.hasValue_algebraMap c₁
    have hv₂ : ∀ s : ↥S, (s : Place K F × Place K F).2.HasValue g₂ c₂ := fun s => by
      simpa only [hc₂] using (s : Place K F × Place K F).2.hasValue_algebraMap c₂
    have ha : ∀ s, a s = Units.mk0 c₁ hc₁0 := fun s =>
      Units.ext (((hv s).1.unique (hv₁ s)).trans (Units.val_mk0 hc₁0).symm)
    have hb : ∀ s, b s = Units.mk0 c₂ hc₂0 := fun s =>
      Units.ext (((hv s).2.unique (hv₂ s)).trans (Units.val_mk0 hc₂0).symm)
    refine ⟨Units.mk0 c₁ hc₁0 / Units.mk0 c₂ hc₂0, ?_⟩
    have hw' : w = fun s => Additive.ofMul (a s / b s) := hw
    rw [hw']
    funext s
    rw [ha s, hb s]
  ·
    rintro ⟨c, rfl⟩
    exact nodeUnit_const S c
@[path]
private lemma main
  {K F : Type*} [Field K] [Field F] [Algebra K F]
  {S : Finset (Place K F × Place K F)}
  {w : ↥S → Additive Kˣ}
-- given
  (hCB : ConstantsAreBase K F) :
-- imply
  nodeUnit S w = 0 ↔ ∃ c : Kˣ, w = fun _ => Additive.ofMul c := by
  refine aux_unglue S ?_ w
  intro g hg hgord
  have heq : LSpace (0 : Divisor K F) = LinearMap.range (Algebra.linearMap K F) := hCB
  have hmem : g ∈ LSpace (0 : Divisor K F) := by
-- proof
    rw [mem_lSpace_iff_ord]
    exact Or.inr fun v => by simp [hgord v]
  rw [heq] at hmem
  obtain ⟨c, hc⟩ := LinearMap.mem_range.mp hmem
  exact ⟨c, by simpa [Algebra.linearMap_apply] using hc⟩


-- created on 2026-10-23
