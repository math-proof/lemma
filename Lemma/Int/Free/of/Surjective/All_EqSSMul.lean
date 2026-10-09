import Mathlib
import sympy.Basic


/--
[Module_Free_of_surjective_of_smul_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Module_Free_of_surjective_of_smul_eq.lean)
-/

private lemma  FrobChareqDock.bijective_aux {S T N : Type*} [CommRing S] [Ring T]
    [AddCommGroup N] [Module S N] [Module T N] [Module.Free S N] [Nontrivial N]
    (g : S →+* T) (hg : ∀ (s : S) (n : N), g s • n = s • n) (hsurj : Function.Surjective g) :
    Function.Bijective g := by
  refine ⟨?_, hsurj⟩
  rw [RingHom.injective_iff_ker_eq_bot, eq_bot_iff]
  intro s hs
  have hann : s ∈ Module.annihilator S N := Module.mem_annihilator.mpr fun n => by
    rw [← hg s n, RingHom.mem_ker.mp hs, zero_smul]
  rwa [(Module.annihilator_eq_bot (R := S) (M := N)).mpr inferInstance] at hann
@[path]
private lemma main
  {S T N : Type*} [CommRing S] [Ring T] [AddCommGroup N] [Module S N] [Module T N] [Module.Free S N]
  {g : S →+* T}
-- given
  (hg : ∀ (s : S) (n : N), g s • n = s • n)
  (hsurj : Function.Surjective g) :
-- imply
  Module.Free T N := by
-- proof
  rcases subsingleton_or_nontrivial N with _ | _
  · infer_instance
  · exact Module.Free.of_basis <| (Module.Free.chooseBasis S N).mapCoeffs
      (RingEquiv.ofBijective g (FrobChareqDock.bijective_aux g hg hsurj)) (fun c x => hg c x)


-- created on 2026-10-05
