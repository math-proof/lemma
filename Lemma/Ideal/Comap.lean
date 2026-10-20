import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/--
[AlgebraicGeometry_Scheme_isLocalization_atPrime_stalk_of_specializes](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_isLocalization_atPrime_stalk_of_specializes.lean)
-/
@[path]
private lemma main
    {X : Scheme.{u}} {x y : ↥X} (h : y ⤳ x) :
    let _ : Algebra ↑(X.presheaf.stalk x) ↑(X.presheaf.stalk y) := (X.presheaf.stalkSpecializes h).hom.toAlgebra
    IsLocalization.AtPrime ↑(X.presheaf.stalk y)
      (Ideal.comap (X.presheaf.stalkSpecializes h).hom (IsLocalRing.maximalIdeal ↑(X.presheaf.stalk y))) := by
  classical
  let instA : Algebra ↑(X.presheaf.stalk x) ↑(X.presheaf.stalk y) := (X.presheaf.stalkSpecializes h).hom.toAlgebra
  have halg : ∀ a, algebraMap ↑(X.presheaf.stalk x) ↑(X.presheaf.stalk y) a = (X.presheaf.stalkSpecializes h).hom a := fun a => rfl
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hyU : y ∈ U := h.mem_open U.2 hxU
  let algX := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hxU⟩ : U)
  let algY := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨y, hyU⟩ : U)
  have hLx := hU.isLocalization_stalk ⟨x, hxU⟩
  have halgX : ∀ r, algebraMap ↑(X.presheaf.obj (Opposite.op U)) ↑(X.presheaf.stalk x) r = (X.presheaf.germ U x hxU).hom r := fun r => rfl
  have halgY : ∀ r, algebraMap ↑(X.presheaf.obj (Opposite.op U)) ↑(X.presheaf.stalk y) r = (X.presheaf.germ U y hyU).hom r := fun r => rfl
  have hLy := hU.isLocalization_stalk ⟨y, hyU⟩
  have hgerm : ∀ r : ↑(X.presheaf.obj (Opposite.op U)),
      (X.presheaf.stalkSpecializes h).hom ((X.presheaf.germ U x hxU).hom r) = (X.presheaf.germ U y hyU).hom r := by
    intro r
    exact TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf hxU h r
  have hunit : ∀ s : ↑(X.presheaf.stalk x),
      s ∈ (Ideal.comap (X.presheaf.stalkSpecializes h).hom (IsLocalRing.maximalIdeal ↑(X.presheaf.stalk y))).primeCompl ↔
        IsUnit ((X.presheaf.stalkSpecializes h).hom s) := by
    intro s
    rw [Ideal.mem_primeCompl_iff, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
  show IsLocalization _ _
  rw [isLocalization_iff]
  refine ⟨fun s => (hunit s.1).mp s.2, fun z => ?_, fun {a b} hab => ?_⟩
  ·
    obtain ⟨⟨a₀, s₀⟩, e⟩ := IsLocalization.surj (M := (hU.primeIdealOf ⟨y, hyU⟩).asIdeal.primeCompl) z
    have hs₀ : IsUnit ((X.presheaf.germ U y hyU).hom s₀) :=
      IsLocalization.map_units (M := (hU.primeIdealOf ⟨y, hyU⟩).asIdeal.primeCompl) (X.presheaf.stalk y) s₀
    refine ⟨⟨(X.presheaf.germ U x hxU).hom a₀, ⟨(X.presheaf.germ U x hxU).hom s₀, (hunit _).mpr (by rw [hgerm]; exact hs₀)⟩⟩, ?_⟩
    simp only [halg, hgerm]
    simpa only [halgY] using e
  ·
    obtain ⟨⟨a₀, ua⟩, ea⟩ := IsLocalization.surj (M := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl) a
    obtain ⟨⟨b₀, ub⟩, eb⟩ := IsLocalization.surj (M := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl) b
    have hua : IsUnit ((X.presheaf.germ U x hxU).hom ua) :=
      IsLocalization.map_units (M := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl) (X.presheaf.stalk x) ua
    have hub : IsUnit ((X.presheaf.germ U x hxU).hom ub) :=
      IsLocalization.map_units (M := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl) (X.presheaf.stalk x) ub
    simp only [halgX] at ea eb
    have key : (X.presheaf.germ U y hyU).hom (a₀ * ub) = (X.presheaf.germ U y hyU).hom (b₀ * ua) := by
      rw [map_mul, map_mul, ← hgerm, ← hgerm, ← hgerm, ← hgerm, ← ea, ← eb]
      rw [map_mul, map_mul, ← halg a, ← halg b, hab]
      ring
    have key' : algebraMap ↑(X.presheaf.obj (Opposite.op U)) ↑(X.presheaf.stalk y) (a₀ * ub) =
        algebraMap ↑(X.presheaf.obj (Opposite.op U)) ↑(X.presheaf.stalk y) (b₀ * ua) := key
    obtain ⟨⟨c₀, hc₀⟩, ec⟩ := (IsLocalization.eq_iff_exists (hU.primeIdealOf ⟨y, hyU⟩).asIdeal.primeCompl (X.presheaf.stalk y)).mp key'
    have hc₀u : IsUnit ((X.presheaf.germ U y hyU).hom c₀) :=
      IsLocalization.map_units (M := (hU.primeIdealOf ⟨y, hyU⟩).asIdeal.primeCompl) (X.presheaf.stalk y) ⟨c₀, hc₀⟩
    refine ⟨⟨(X.presheaf.germ U x hxU).hom c₀ * (X.presheaf.germ U x hxU).hom ua * (X.presheaf.germ U x hxU).hom ub,
      (hunit _).mpr ?_⟩, ?_⟩
    · rw [map_mul, map_mul, hgerm, hgerm, hgerm]
      exact (hc₀u.mul (by rw [← hgerm]; exact hua.map _)).mul (by rw [← hgerm]; exact hub.map _)
    ·
      simp only
      have ec' := congrArg (X.presheaf.germ U x hxU).hom ec
      simp only [map_mul] at ec'
      calc (X.presheaf.germ U x hxU).hom c₀ * (X.presheaf.germ U x hxU).hom ua * (X.presheaf.germ U x hxU).hom ub * a
          = (X.presheaf.germ U x hxU).hom c₀ * ((a * (X.presheaf.germ U x hxU).hom ua) * (X.presheaf.germ U x hxU).hom ub) := by ring
        _ = (X.presheaf.germ U x hxU).hom c₀ * ((X.presheaf.germ U x hxU).hom a₀ * (X.presheaf.germ U x hxU).hom ub) := by rw [ea]
        _ = (X.presheaf.germ U x hxU).hom c₀ * ((X.presheaf.germ U x hxU).hom b₀ * (X.presheaf.germ U x hxU).hom ua) := by
              rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, ec]
        _ = (X.presheaf.germ U x hxU).hom c₀ * ((b * (X.presheaf.germ U x hxU).hom ub) * (X.presheaf.germ U x hxU).hom ua) := by rw [eb]
        _ = (X.presheaf.germ U x hxU).hom c₀ * (X.presheaf.germ U x hxU).hom ua * (X.presheaf.germ U x hxU).hom ub * b := by ring

-- created on 2026-10-20
