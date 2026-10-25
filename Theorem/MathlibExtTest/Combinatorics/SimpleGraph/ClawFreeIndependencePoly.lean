/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/ClawFreeIndependencePoly.lean -/


import Def.Combinatorics.SimpleGraph.ClawFreeIndependencePoly
import Lemma.SimpleGraph.ClawFreeIndependencePoly


-- The empty graph on `Fin 3` is claw-free: no vertex has any neighbours.
example : MetaMathlibExt.clawFree (⊥ : SimpleGraph (Fin 3)) := by
  unfold MetaMathlibExt.clawFree
  rintro ⟨c, l₁, l₂, l₃, _, _, _, _, _, _, h1, _, _, _, _, _⟩
  exact absurd h1 (by simp)

-- `SimpleGraph.IsClawFree` applies to graphs on infinite types, where the
-- Wanted `clawFree` (which needs `Fintype`) cannot even be stated.
example : (⊥ : SimpleGraph ℕ).IsClawFree := by
  unfold SimpleGraph.IsClawFree
  rintro ⟨c, l₁, l₂, l₃, _, _, _, _, _, _, h1, _, _, _, _, _⟩
  exact absurd h1 (by simp)

-- Specialising `independencePoly_bot` to `Fin 3`.
example : MetaMathlibExt.independencePoly (⊥ : SimpleGraph (Fin 3))
    = (1 + Polynomial.X) ^ 3 := by
  have h := MetaMathlibExt.independencePoly_bot (V := Fin 3)
  simpa using h

-- Specialising `independencePoly_top` to `Fin 3`.
example : MetaMathlibExt.independencePoly (⊤ : SimpleGraph (Fin 3))
    = 1 + Polynomial.C 3 * Polynomial.X := by
  have h := MetaMathlibExt.independencePoly_top (V := Fin 3)
  simpa using h

-- One coefficient via `independencePoly_coeff`: the complete graph on
-- `Fin 3` has exactly three independent singletons.
example : (MetaMathlibExt.independencePoly (⊤ : SimpleGraph (Fin 3))).coeff 1 = 3 := by
  rw [MetaMathlibExt.independencePoly_coeff]
  have h : (⊤ : SimpleGraph (Fin 3)).indepSetFinset 1
      = Finset.univ.powersetCard 1 := by
    ext s
    rw [SimpleGraph.mem_indepSetFinset_iff, SimpleGraph.isNIndepSet_iff,
      Finset.mem_powersetCard]
    constructor
    · rintro ⟨hI, hcard⟩
      exact ⟨Finset.subset_univ s, hcard⟩
    · rintro ⟨_, hcard⟩
      refine ⟨?_, hcard⟩
      rw [SimpleGraph.isIndepSet_iff]
      intro a ha b hb hne
      obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcard
      subst hx
      simp only [Finset.coe_singleton, Set.mem_singleton_iff] at ha hb
      exact absurd (ha.trans hb.symm) hne
  rw [h, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  decide

-- The main theorem applied to a concrete claw-free graph.
example : ((MetaMathlibExt.independencePoly (⊥ : SimpleGraph (Fin 3))).map
    (Int.castRingHom ℝ)).Splits := by
  apply MetaMathlibExt.independence_poly_of_claw_free_splits
  unfold MetaMathlibExt.clawFree
  rintro ⟨c, l₁, l₂, l₃, _, _, _, _, _, _, h1, _, _, _, _, _⟩
  exact absurd h1 (by simp)

