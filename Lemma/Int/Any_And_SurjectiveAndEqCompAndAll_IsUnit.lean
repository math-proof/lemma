import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[CerednikDrinfeld_exists_torsionFree_surjective_comp_eq_forall_isUnit](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_CerednikDrinfeld_exists_torsionFree_surjective_comp_eq_forall_isUnit.lean)
-/
@[path]
private lemma main
  (p : ℕ)
  {S B : Type} [CommRing S] [CommRing B]
  (q : RingHom S B) (hq : Function.Surjective q) (hS : ∀ s : S, (p : S) * s = 0 → s = 0) :
  -- imply
  ∃ (S' : Type) (_ : CommRing S') (ι : RingHom S S') (q' : RingHom S' B), (∀ s : S', (p : S') * s = 0 → s = 0) ∧ Function.Surjective q' ∧ q'.comp ι = q ∧ ∀ s : S', IsUnit (q' s) → IsUnit s := by
  -- proof
  classical
  let M : Submonoid S := (IsUnit.submonoid B).comap q
  have hM : ∀ m : M, IsUnit (q (m : S)) := fun m => m.2
  let L : Type := Localization M
  let q' : RingHom L B := IsLocalization.lift (M := M) (S := L) hM
  refine ⟨L, inferInstance, algebraMap S L, q', ?_, ?_, ?_, ?_⟩
  ·
    intro x hx
    obtain ⟨⟨s, m⟩, rfl⟩ := IsLocalization.mk'_surjective M x
    dsimp at *
    have h1 : (p : L) * IsLocalization.mk' L s m = IsLocalization.mk' L ((p : S) * s) m := by
      rw [IsLocalization.mk'_eq_mul_mk'_one, IsLocalization.mk'_eq_mul_mk'_one (x := (p : S) * s), map_mul, map_natCast, mul_assoc]
    rw [h1, IsLocalization.mk'_eq_zero_iff] at hx
    obtain ⟨c, hc⟩ := hx
    rw [IsLocalization.mk'_eq_zero_iff]
    refine ⟨c, hS _ ?_⟩
    rw [← hc]
    ring
  ·
    intro b
    obtain ⟨s, rfl⟩ := hq b
    refine ⟨algebraMap S L s, IsLocalization.lift_eq hM s⟩
  ·
    apply RingHom.ext
    intro s
    apply IsLocalization.lift_eq hM s
  ·
    intro x hx
    obtain ⟨⟨s, m⟩, rfl⟩ := IsLocalization.mk'_surjective M x
    dsimp at *
    have hspec : q s = q (m : S) * q' (IsLocalization.mk' L s m) := (IsLocalization.lift_mk'_spec (M := M) (S := L) hM s _ m).mp rfl
    have hs : IsUnit (q s) := by
      rw [hspec]
      apply (hM m).mul hx
    have hsM : s ∈ M := hs
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    refine (IsLocalization.map_units L (⟨s, hsM⟩ : M)).mul ?_
    refine IsUnit.of_mul_eq_one (algebraMap S L (m : S)) ?_
    rw [IsLocalization.mk'_spec, map_one]


-- created on 2026-10-20
