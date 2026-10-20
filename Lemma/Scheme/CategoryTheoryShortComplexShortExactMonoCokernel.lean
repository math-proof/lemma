import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[CategoryTheory_ShortComplex_shortExact_of_mono_cokernel](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_CategoryTheory_ShortComplex_shortExact_of_mono_cokernel.lean)
-/
@[path]
private lemma main
  {𝒜 : Type u} [Category 𝒜] [Abelian 𝒜] {X Y : 𝒜} (f : X ⟶ Y) [Mono f] :
  -- imply
  (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f)) (by change Mono f; infer_instance) (by change Epi (cokernel.π f); infer_instance)


-- created on 2026-10-20
