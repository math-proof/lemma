import Mathlib
import sympy.Basic
open IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[Ideal_iInf_map_maximalIdeal_pow_eq_bot_of_moduleFinite](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Ideal_iInf_map_maximalIdeal_pow_eq_bot_of_moduleFinite.lean)
-/
@[path]
private lemma main
  (S : Type u) [CommRing S] [IsNoetherianRing S] [IsLocalRing S]
  (C : Type u) [CommRing C] [Algebra S C] [Module.Finite S C] [Nontrivial C] :
  -- imply
  ⨅ n : ℕ, (maximalIdeal S ^ n).map (algebraMap S C) = ⊥ := by
  -- proof
  have h := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (I := maximalIdeal S) (M := C) (maximalIdeal.isMaximal S).ne_top
  rw [eq_bot_iff]
  intro x hx
  have hx' : x ∈ (⨅ i : ℕ, (maximalIdeal S ^ i • ⊤ : Submodule S C)) := by
    rw [Submodule.mem_iInf]
    intro i
    rw [Ideal.smul_top_eq_map]
    apply (Submodule.mem_iInf _).mp hx i
  rw [h] at hx'
  apply hx'


-- created on 2026-10-20
