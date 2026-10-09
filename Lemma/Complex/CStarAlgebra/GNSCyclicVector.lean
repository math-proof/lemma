import Mathlib
import sympy.Basic
import sympy.Analysis.CStarAlgebra.GNSCyclicVector

open scoped InnerProductSpace ComplexOrder

/--
[cStarAlgebra_gns_cyclic_vector](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/GNSCyclicVector.lean)
-/
@[path]
private lemma cStarAlgebra_gns_cyclic_vector_eq
-- given
  {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  (f : PositiveLinearMap ℂ A ℂ) (hf : f (1 : A) = (1 : ℂ)) :
-- imply
  (∃ (ξ : f.GNS), ‖ξ‖ = 1 ∧
    (∀ a : A, f a = ⟪ξ, (f.gnsStarAlgHom a) ξ⟫_ℂ) ∧
      Dense (↑(Submodule.span ℂ (Set.range fun a : A => (f.gnsStarAlgHom a) ξ)) : Set f.GNS)) :=
-- proof
  Analysis.CStarAlgebra.LandmarkWanted.cStarAlgebra_gns_cyclic_vector f hf


-- created on 2026-10-09
