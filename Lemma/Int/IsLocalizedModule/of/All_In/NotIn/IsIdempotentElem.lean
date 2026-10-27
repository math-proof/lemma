import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.IharaLemma.IdempotentSplitting
open IharaLemma


/--
[IharaLemma_isLocalizedModule_toCorner](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IharaLemma_isLocalizedModule_toCorner.lean)
-/
@[path]
private lemma main
  [CommRing B] [AddCommGroup M] [Module B M]
  {𝔪 : Ideal B} [h𝔪 : 𝔪.IsMaximal]
  {e : B}
-- given
  (he : IsIdempotentElem e)
  (hem : e ∉ 𝔪)
  (hother : ∀ J : Ideal B, J.IsMaximal → J ≠ 𝔪 → e ∈ J) :
-- imply
  IsLocalizedModule 𝔪.primeCompl (toCorner (M := M) e) := {
-- proof
  map_units := fun s => by
    obtain ⟨t, ht⟩ := exists_mul_mul_eq_of_notMem he 𝔪 hother s.2
    have hfix : ∀ z : cornerSubmodule (M := M) e, e • (z : M) = z := by
      intro z
      obtain ⟨z0, hz0⟩ := z.2
      rw [← hz0]
      simp [LinearMap.smul_apply, smul_smul, he.eq]
    have hact : ∀ z : cornerSubmodule (M := M) e,
        ((algebraMap B (Module.End B (cornerSubmodule (M := M) e)) (s : B) z :
          cornerSubmodule e) : M) =
          (s : B) • (z : M) := fun z => rfl
    rw [Module.End.isUnit_iff]
    constructor
    ·
      intro x y hxy
      apply Subtype.ext
      have hM : (s : B) • (x : M) = (s : B) • (y : M) := by
        rw [← hact x, ← hact y, hxy]
      calc
        _ = e • (x : M) := (hfix x).symm
        _ = (t * s * e) • (x : M) := by rw [ht]
        _ = t • ((s : B) • (e • (x : M))) := by rw [mul_smul, mul_smul]
        _ = t • ((s : B) • (x : M)) := by rw [hfix x]
        _ = t • ((s : B) • (y : M)) := by rw [hM]
        _ = t • ((s : B) • (e • (y : M))) := by rw [hfix y]
        _ = (t * s * e) • (y : M) := by rw [mul_smul, mul_smul]
        _ = e • (y : M) := by rw [ht]
        _ = y := hfix y
    ·
      intro y
      refine ⟨t • y, ?_⟩
      apply Subtype.ext
      rw [hact]
      show (s : B) • (t • (y : M)) = y
      calc
        _ = ((s : B) * t) • (e • (y : M)) := by rw [hfix y, mul_smul]
        _ = ((s : B) * t * e) • (y : M) := (mul_smul _ _ _).symm
        _ = e • (y : M) := by rw [mul_comm (s : B) t, ht]
        _ = y := hfix y
  surj := fun y => by
    refine ⟨((y : M), 1), ?_⟩
    apply Subtype.ext
    obtain ⟨y0, hy0⟩ := y.2
    simp only [one_smul, toCorner_apply]
    rw [← hy0]
    simp [LinearMap.smul_apply, smul_smul, he.eq]
  exists_of_eq := fun {x₁ x₂} h => by
    refine ⟨⟨e, hem⟩, ?_⟩
    have := congrArg (fun z : cornerSubmodule (M := M) e => (z : M)) h
    simp at this
    exact this
}


-- created on 2026-10-24
-- updated on 2026-10-26
