import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[IharaLemma_injective_of_ker_le_torsion](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IharaLemma_injective_of_ker_le_torsion.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R] (S : Submonoid R)
  {V W : Type u} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  {V' W' : Type u} [AddCommGroup V'] [Module R V'] [AddCommGroup W'] [Module R W']
  (g : V →ₗ[R] V') [IsLocalizedModule S g] (h : W →ₗ[R] W') [IsLocalizedModule S h]
  (f : V →ₗ[R] W) (F : V' →ₗ[R] W') (hcomm : ∀ v, F (g v) = h (f v))
  (E : Submodule R V) (hE : ∀ e ∈ E, ∃ s : S, (s : R) • e = 0) (hker : ∀ v, f v = 0 → v ∈ E) :
  -- imply
  Function.Injective F := by
  -- proof
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨⟨v, s⟩, hv⟩ := IsLocalizedModule.surj S g x
  have hv' : (s : R) • x = g v := hv
  have hfv : h (f v) = 0 := by
    rw [← hcomm, ← hv', map_smul, hx, smul_zero]
  obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_zero_iff S h).mp hfv
  have hcv : f ((c : R) • v) = 0 := by
    rw [map_smul]
    apply hc
  obtain ⟨s', hs'⟩ := hE _ (hker _ hcv)
  apply IsLocalizedModule.smul_injective g (s' * c * s)
  show ((s' * c * s : S) : R) • x = ((s' * c * s : S) : R) • 0
  rw [smul_zero, Submonoid.coe_mul, Submonoid.coe_mul, mul_smul, mul_smul]
  rw [hv', ← map_smul, ← map_smul, hs', map_zero]


-- created on 2026-10-20
