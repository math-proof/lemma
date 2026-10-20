import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

private lemma helper_main {R : Type u} [CommRing R] (I : Ideal R) (hI : I ≤ (⊥ : Ideal R).jacobson)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [UniversallyClosed f]
    (W : X.Opens) (hW : ∀ x : X, I ≤ (f.base x).asIdeal → x ∈ W) : W = ⊤ := by
  by_contra hne
  set Z : Set X := (W : Set X)ᶜ with hZ
  have hZc : IsClosed Z := W.2.isClosed_compl
  have hZne : Z.Nonempty := by
    by_contra h
    apply hne
    rw [Set.not_nonempty_iff_eq_empty, hZ, Set.compl_empty_iff] at h
    exact TopologicalSpace.Opens.ext (h.trans TopologicalSpace.Opens.coe_top.symm)
  have himg : IsClosed (f.base '' Z) := f.isClosedMap Z hZc
  obtain ⟨J, hJ⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).mp himg
  have hJtop : J ≠ ⊤ := by
    intro hJtop
    have hempty : PrimeSpectrum.zeroLocus (J : Set R) = ∅ := PrimeSpectrum.zeroLocus_empty_iff_eq_top.mpr hJtop
    obtain ⟨z, hz⟩ := hZne
    have : f.base z ∈ f.base '' Z := ⟨z, hz, rfl⟩
    rw [hJ, hempty] at this
    exact this
  obtain ⟨M, hMmax, hJM⟩ := Ideal.exists_le_maximal J hJtop
  have hMmem : (⟨M, hMmax.isPrime⟩ : PrimeSpectrum R) ∈ f.base '' Z := by
    rw [hJ]
    exact hJM
  obtain ⟨z, hz, hfz⟩ := hMmem
  have hIM : I ≤ (f.base z).asIdeal := by
    rw [hfz]
    intro r hr
    have hr' : r ∈ (⊥ : Ideal R).jacobson := hI hr
    rw [Ideal.jacobson, Submodule.mem_sInf] at hr'
    exact hr' M ⟨bot_le, hMmax⟩
  exact hz (hW z hIM)
/--
[AlgebraicGeometry_Scheme_Opens_eq_top_of_forall_mem_of_le_jacobson_of_universallyClosed](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_Opens_eq_top_of_forall_mem_of_le_jacobson_of_universallyClosed.lean)
-/
@[path]
private lemma main {R : Type u} [CommRing R] (I : Ideal R) (hI : I ≤ (⊥ : Ideal R).jacobson)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [UniversallyClosed f]
    (W : X.Opens) (hW : ∀ x : X, I ≤ (f.base x).asIdeal → x ∈ W) : W = ⊤ :=
  helper_main I hI f W hW

-- created on 2026-10-20
