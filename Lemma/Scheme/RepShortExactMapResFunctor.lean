import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[Rep_shortExact_map_resFunctor](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Rep_shortExact_map_resFunctor.lean)
-/
@[path]
private lemma main
  {k G H : Type u} [CommRing k] [Group G] [Group H]
  (f : H →* G)
  {X : ShortComplex (Rep k G)}
  -- given
  (hX : X.ShortExact) :
  -- imply
  (X.map (Rep.resFunctor f)).ShortExact where
  exact := (forget₂ (Rep k H) (ModuleCat k)).reflects_exact_of_faithful _
    ((ShortComplex.moduleCat_exact_iff _).2 fun x hx => by
      have h := (hX.exact.map (forget₂ (Rep k G) (ModuleCat k))).moduleCat_range_eq_ker
      have hx' : x ∈ LinearMap.ker (ModuleCat.Hom.hom (X.map (forget₂ (Rep k G) (ModuleCat k))).g) := hx
      rw [← h] at hx'
      obtain ⟨a, ha⟩ := hx'
      refine ⟨a, ha⟩)
  mono_f := (Rep.mono_iff_injective _).2 ((Rep.mono_iff_injective X.f).1 hX.mono_f)
  epi_g := (Rep.epi_iff_surjective _).2 ((Rep.epi_iff_surjective X.g).1 hX.epi_g)


-- created on 2026-10-20
