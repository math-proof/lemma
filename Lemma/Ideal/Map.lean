import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[Ideal_map_algebraMap_localization_atPrime_eq_of_map_comp_eq_of_faithfullyFlat](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Ideal_map_algebraMap_localization_atPrime_eq_of_map_comp_eq_of_faithfullyFlat.lean)
-/
@[path]
private lemma main
  {R S : Type} [CommRing R] [CommRing S] (𝔭 : Ideal R) [𝔭.IsPrime]
  (ψ : RingHom (Localization.AtPrime 𝔭) S)
  (I J : Ideal R)
  -- given
  (hψ : let _ : Algebra (Localization.AtPrime 𝔭) S := ψ.toAlgebra
    Module.FaithfullyFlat (Localization.AtPrime 𝔭) S)
  (h : I.map (ψ.comp (algebraMap R (Localization.AtPrime 𝔭))) = J.map (ψ.comp (algebraMap R (Localization.AtPrime 𝔭)))) :
  -- imply
  I.map (algebraMap R (Localization.AtPrime 𝔭)) = J.map (algebraMap R (Localization.AtPrime 𝔭)) := by
  -- proof
  let inst : Algebra (Localization.AtPrime 𝔭) S := ψ.toAlgebra
  let _ : Module.FaithfullyFlat (Localization.AtPrime 𝔭) S := hψ
  have hψeq : ψ = algebraMap (Localization.AtPrime 𝔭) S := rfl
  have h' : (I.map (algebraMap R (Localization.AtPrime 𝔭))).map (algebraMap (Localization.AtPrime 𝔭) S) = (J.map (algebraMap R (Localization.AtPrime 𝔭))).map (algebraMap (Localization.AtPrime 𝔭) S) := by
    rw [Ideal.map_map, Ideal.map_map, ← hψeq]
    apply h
  have hcomap := congrArg (Ideal.comap (algebraMap (Localization.AtPrime 𝔭) S)) h'
  simpa [Ideal.comap_map_eq_self_of_faithfullyFlat] using hcomap


-- created on 2026-10-20
