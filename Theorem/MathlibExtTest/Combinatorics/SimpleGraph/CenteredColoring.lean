/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/CenteredColoring.lean -/

-- MathlibExtTest/Combinatorics/SimpleGraph/CenteredColoring.lean

import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Def.Combinatorics.SimpleGraph.CenteredColoring
import Lemma.SimpleGraph.CenteredColoring
open SimpleGraph


/-- Singleton induced subgraph is connected: boundary probe. -/
example : ((⊥ : SimpleGraph (Fin 2)).induce ({0} : Set (Fin 2))).Connected := by
  have hne : Nonempty ↥({0} : Set (Fin 2)) := ⟨⟨0, Set.mem_singleton 0⟩⟩
  refine @SimpleGraph.Connected.mk _ _ ?_ hne
  intro v w
  have hv : v.val = 0 := Set.mem_singleton_iff.mp v.property
  have hw : w.val = 0 := Set.mem_singleton_iff.mp w.property
  have hvw : v = w := Subtype.ext (hv.trans hw.symm)
  subst hvw
  exact SimpleGraph.Reachable.refl _

/-- Tautological coloring is centered on a nontrivial complete graph. -/
example : IsCentered (SimpleGraph.selfColoring (⊤ : SimpleGraph (Fin 3))) :=
  selfColoring_isCentered _

/-- Singleton always carries a center for the tautological coloring. -/
example : IsPhiCenter (SimpleGraph.selfColoring (⊥ : SimpleGraph (Fin 2))) {0} 0 :=
  isPhiCenter_singleton _ _

/-- A vertex outside the set is never a center: boundary probe. -/
example : ¬ IsPhiCenter (SimpleGraph.selfColoring (⊤ : SimpleGraph (Fin 2))) {1} 0 := by
  rintro ⟨hmem, _⟩
  have : (0 : Fin 2) = 1 := Set.mem_singleton_iff.mp hmem
  exact absurd this (by decide)

