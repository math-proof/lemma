import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false


/--
[CerednikDrinfeld_ringHom_comp_eq_of_fstHom_comp_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_CerednikDrinfeld_ringHom_comp_eq_of_fstHom_comp_eq.lean)
-/
@[path]
private lemma main
  (p : ℕ) [Fact p.Prime]
  (k : Type) [Field k] [CharP k p] [PerfectRing k p]
  (κ : Type) [Field κ] [CharP κ p]
  (ψ : RingHom (WittVector p k) (DualNumber κ))
  (s : AlgHom κ (DualNumber κ) (DualNumber κ))
  (hs : (TrivSqZeroExt.fstHom κ κ κ).comp s = TrivSqZeroExt.fstHom κ κ κ) :
  -- imply
  (s : RingHom (DualNumber κ) (DualNumber κ)).comp ψ = ψ := by
  -- proof
  classical
  have hp : ψ (p : WittVector p k) = 0 := by
    rw [map_natCast]
    apply TrivSqZeroExt.ext
    · rw [TrivSqZeroExt.fst_natCast, TrivSqZeroExt.fst_zero, CharP.cast_eq_zero]
    · rw [TrivSqZeroExt.snd_natCast, TrivSqZeroExt.snd_zero]
  have hred : ∀ x : WittVector p k, ψ x = ψ (WittVector.teichmuller p (x.coeff 0)) := by
    intro x
    have hmem : x - WittVector.teichmuller p (x.coeff 0) ∈ Ideal.span {(p : WittVector p k)} := by
      rw [WittVector.mem_span_p_iff_coeff_zero_eq_zero]
      have h := map_sub (WittVector.constantCoeff : RingHom (WittVector p k) k) x (WittVector.teichmuller p (x.coeff 0))
      change (x - WittVector.teichmuller p (x.coeff 0)).coeff 0 = x.coeff 0 - (WittVector.teichmuller p (x.coeff 0)).coeff 0 at h
      rw [h, WittVector.teichmuller_coeff_zero, sub_self]
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hmem
    rw [← sub_eq_zero, ← map_sub, ← hy, map_mul, hp, mul_zero]
  have hsnd : ∀ a : k, (ψ (WittVector.teichmuller p a)).snd = 0 := by
    intro a
    obtain ⟨b, rfl⟩ := surjective_frobenius k p a
    rw [frobenius_def, map_pow (WittVector.teichmuller p), map_pow, TrivSqZeroExt.snd_pow, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
  refine RingHom.ext (fun x => ?_)
  rw [RingHom.comp_apply, hred x]
  have hu : ψ (WittVector.teichmuller p (x.coeff 0)) = algebraMap κ (DualNumber κ) (ψ (WittVector.teichmuller p (x.coeff 0))).fst := by
    conv_lhs => rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq (ψ (WittVector.teichmuller p (x.coeff 0)))]
    rw [hsnd, TrivSqZeroExt.inr_zero, add_zero, TrivSqZeroExt.algebraMap_eq_inl]
  rw [hu]
  apply s.commutes _


-- created on 2026-10-20
