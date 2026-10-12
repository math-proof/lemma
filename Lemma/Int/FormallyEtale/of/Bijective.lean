import Mathlib
import sympy.Basic


private lemma subsingleton_kaehler_of_surjective
  [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
-- given
  (h : Function.Surjective (KaehlerDifferential.mapBaseChange R S T)) :
-- imply
  Subsingleton Ω[T⁄S] := by
-- proof
  have hex := KaehlerDifferential.exact_mapBaseChange_map R S T
  have hsurj := KaehlerDifferential.map_surjective R S T
  refine ⟨fun a b => ?_⟩
  obtain ⟨a', rfl⟩ := hsurj a
  obtain ⟨b', rfl⟩ := hsurj b
  have ha : KaehlerDifferential.map R S T T a' = 0 := by
    obtain ⟨x, rfl⟩ := h a'
    apply hex.apply_apply_eq_zero
  have hb : KaehlerDifferential.map R S T T b' = 0 := by
    obtain ⟨x, rfl⟩ := h b'
    apply hex.apply_apply_eq_zero
  rw [ha, hb]


/--
[Algebra_FormallyEtale_of_formallySmooth_of_bijective_mapBaseChange](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_FormallyEtale_of_formallySmooth_of_bijective_mapBaseChange.lean)
-/
@[path]
private lemma main
  [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  [Algebra.FormallySmooth R T]
-- given
  (h : Function.Bijective (KaehlerDifferential.mapBaseChange R S T)) :
-- imply
  Algebra.FormallyEtale S T := by
-- proof
  have hΩ : Subsingleton Ω[T⁄S] := subsingleton_kaehler_of_surjective h.2
  have : Algebra.FormallyUnramified S T := ⟨hΩ⟩
  have hδ : ∀ x, Algebra.H1Cotangent.δ R S T x = 0 := by
    intro x
    have hex := Algebra.H1Cotangent.exact_δ_mapBaseChange R S T
    have hmem : Algebra.H1Cotangent.δ R S T x ∈ LinearMap.ker (KaehlerDifferential.mapBaseChange R S T) := by
      rw [LinearMap.mem_ker]
      apply hex.apply_apply_eq_zero
    rwa [LinearMap.ker_eq_bot.mpr h.1, Submodule.mem_bot] at hmem
  have hH1 : Subsingleton (Algebra.H1Cotangent S T) := by
    refine ⟨fun a b => ?_⟩
    have hex := Algebra.H1Cotangent.exact_map_δ R S T
    have ha : a ∈ Set.range (Algebra.H1Cotangent.map R S T T) := (hex a).mp (hδ a)
    have hb : b ∈ Set.range (Algebra.H1Cotangent.map R S T T) := (hex b).mp (hδ b)
    obtain ⟨a', rfl⟩ := ha
    obtain ⟨b', rfl⟩ := hb
    rw [Subsingleton.elim a' b']
  have : Module.Projective T Ω[T⁄S] := Module.Projective.of_free
  have : Algebra.FormallySmooth S T := ⟨inferInstance, hH1⟩
  apply Algebra.FormallyEtale.of_formallyUnramified_and_formallySmooth


-- created on 2026-10-12
