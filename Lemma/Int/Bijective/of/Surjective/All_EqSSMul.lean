import Mathlib
import sympy.Basic


/--
[RingHom_bijective_of_surjective_of_smul_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_RingHom_bijective_of_surjective_of_smul_eq.lean)
-/
@[path]
private lemma main
  [CommRing S] [Ring T] [AddCommGroup N] [Module S N] [Module T N] [Module.Free S N] [Nontrivial N]
  {g : S →+* T}
-- given
  (hg : ∀ (s : S) (n : N), g s • n = s • n)
  (hsurj : Function.Surjective g) :
-- imply
  Function.Bijective g := by
-- proof
  refine ⟨?_, hsurj⟩
  rw [RingHom.injective_iff_ker_eq_bot, eq_bot_iff]
  intro s hs
  have hann : s ∈ Module.annihilator S N := Module.mem_annihilator.mpr fun n => by
    rw [← hg s n, RingHom.mem_ker.mp hs, zero_smul]
  rwa [(Module.annihilator_eq_bot (R := S) (M := N)).mpr inferInstance] at hann


-- created on 2026-10-03
