/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Geometry/Polyhedra/PlatonicSolidsClassification.lean -/


import Def.Geometry.Polyhedra.PlatonicSolidsClassification.Part2
import Lemma.Set.Polyhedra.PlatonicSolidsClassification


namespace MetaMathlibExt

-- The existence half provides twelve uniformly positive-length cube edges.
example : ∃ (w : Fin 8 → EuclideanSpace ℝ (Fin 3)) (ee : Fin 12 → Fin 8 × Fin 8)
    (ll : ℝ),
    0 < ll ∧ ∀ e : Fin 12, dist (w (ee e).1) (w (ee e).2) = ll := by
  obtain ⟨w, ee, _, _, ll, _, hll, _, _, _, _, _, _, hedge, _⟩ :=
    platonic_solids_classification.2.2.1
  exact ⟨w, ee, ll, hll, hedge⟩

end MetaMathlibExt
