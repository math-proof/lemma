

import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal

/-
  Author: @toskua, Avocado
-/


open scoped InnerProductSpace ComplexOrder

universe u

namespace PositiveLinearMap

/-- For a state `f` on a unital C⋆-algebra (`f 1 = 1`), the GNS space has a unit cyclic vector
`ξ`: `f a = ⟪ξ, π(a) ξ⟫` for all `a`, and the vectors `π(a) ξ` span a dense subspace.
`cStarAlgebra_gns_cyclic_vector` is the source-shaped form. -/
theorem exists_gns_cyclic_vector
    {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (f : A →ₚ[ℂ] ℂ) (hf : f (1 : A) = (1 : ℂ)) :
    ∃ (ξ : f.GNS), ‖ξ‖ = 1 ∧
      (∀ a : A, f a = ⟪ξ, (f.gnsStarAlgHom a) ξ⟫_ℂ) ∧
      Dense (↑(Submodule.span ℂ (Set.range fun a : A => (f.gnsStarAlgHom a) ξ)) : Set f.GNS) := by
  have hpi : ∀ a : A, (f.gnsStarAlgHom a) ((f.toPreGNS 1 : f.PreGNS) : f.GNS)
      = ((f.toPreGNS a : f.PreGNS) : f.GNS) := by
    intro a
    change (f.gnsNonUnitalStarAlgHom a) ((f.toPreGNS 1 : f.PreGNS) : f.GNS) = _
    rw [f.gnsNonUnitalStarAlgHom_apply_coe, f.leftMulMapPreGNS_apply]
    congr 1
    simp
  refine ⟨((f.toPreGNS 1 : f.PreGNS) : f.GNS), ?_, ?_, ?_⟩
  · rw [UniformSpace.Completion.norm_coe, f.preGNS_norm_def]
    have h11 : star (f.ofPreGNS (f.toPreGNS (1 : A))) * f.ofPreGNS (f.toPreGNS (1 : A)) =
        (1 : A) := by
      simp
    rw [h11, hf]
    simp
  · intro a
    rw [hpi a, UniformSpace.Completion.inner_coe, f.preGNS_inner_def]
    have h1a : star (f.ofPreGNS (f.toPreGNS (1 : A))) * f.ofPreGNS (f.toPreGNS a) = a := by
      simp
    rw [h1a]
  · have hdense : Dense (Set.range fun x : f.PreGNS => (↑x : f.GNS)) :=
      UniformSpace.Completion.denseRange_coe
    have hrange : (Set.range fun x : f.PreGNS => (↑x : f.GNS))
        ⊆ ↑(Submodule.span ℂ (Set.range fun a : A => (f.gnsStarAlgHom a)
          ((f.toPreGNS 1 : f.PreGNS) : f.GNS))) := by
      intro y hy
      obtain ⟨x, rfl⟩ := hy
      change (↑x : f.GNS) ∈ ↑(Submodule.span ℂ (Set.range fun a : A => (f.gnsStarAlgHom a)
        ((f.toPreGNS 1 : f.PreGNS) : f.GNS)))
      have e1 : (↑x : f.GNS) = ((f.toPreGNS (f.ofPreGNS x) : f.PreGNS) : f.GNS) := by
        rw [f.toPreGNS_ofPreGNS x]
      have e2 : ((f.toPreGNS (f.ofPreGNS x) : f.PreGNS) : f.GNS)
          = (f.gnsStarAlgHom (f.ofPreGNS x)) ((f.toPreGNS 1 : f.PreGNS) : f.GNS) :=
        (hpi _).symm
      rw [e1, e2]
      exact Submodule.subset_span ⟨_, rfl⟩
    exact Dense.mono hrange hdense

end PositiveLinearMap

namespace Analysis.CStarAlgebra.LandmarkWanted

/--
For a unital positive functional `f` with `f 1 = 1` on a C*-algebra, the GNS space contains a unit
cyclic vector `ξ` with `f a = ⟪ξ, π(a) ξ⟫` and dense span of `π(A) ξ`. Source: GNS construction,
Gelfand–Naimark 1943 and I. E. Segal, Ann. of Math. 48 (1947); see Murphy, C*-Algebras; Lean is
unital state f 1 = 1 unit cyclic vector with inner-product formula and dense span.
It is `PositiveLinearMap.exists_gns_cyclic_vector`, kept under the source's name.
Proves `Wanted` entry `cStarAlgebra_gns_cyclic_vector`.
-/
theorem cStarAlgebra_gns_cyclic_vector
    {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (f : A →ₚ[ℂ] ℂ) (hf : f (1 : A) = (1 : ℂ)) :
    ∃ (ξ : f.GNS), ‖ξ‖ = 1 ∧
      (∀ a : A, f a = ⟪ξ, (f.gnsStarAlgHom a) ξ⟫_ℂ) ∧
      Dense (↑(Submodule.span ℂ (Set.range fun a : A => (f.gnsStarAlgHom a) ξ)) : Set f.GNS) :=
  PositiveLinearMap.exists_gns_cyclic_vector f hf

end Analysis.CStarAlgebra.LandmarkWanted
