/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/CenteredColoring.lean -/

-- MathlibExtTest/Combinatorics/SimpleGraph/CenteredColoring.lean

import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Def.Combinatorics.SimpleGraph.CenteredColoring
import Lemma.SimpleGraph.CenteredColoring
import Def.MathlibExtTest.Combinatorics.SimpleGraph.CenteredColoring
open SimpleGraph


/-- On the full edgeless graph the constant color repeats, so no center. -/
example : ¬ IsPhiCenter constColor (Set.univ : Set (Fin 2)) 0 := by
  rintro ⟨_, huniq⟩
  have h10 : (1 : Fin 2) = 0 := huniq 1 (Set.mem_univ 1) rfl
  exact absurd h10 (by decide)

/-- Even with global repetition, each singleton retains its center. -/
example : IsPhiCenter constColor ({0} : Set (Fin 2)) 0 :=
  isPhiCenter_singleton constColor 0

/-- The alternating 2-coloring of the 4-vertex path is proper but not centered:
each color appears twice on the full vertex set, so no vertex is a center. -/
example : ¬ IsCentered (SimpleGraph.pathGraph.bicoloring 4) := by
  intro hC
  have hG : (SimpleGraph.pathGraph 4).Connected :=
    ⟨SimpleGraph.pathGraph_preconnected 4⟩
  have hConn : ((SimpleGraph.pathGraph 4).induce Set.univ).Connected :=
    (SimpleGraph.Iso.connected_iff (SimpleGraph.induceUnivIso _)).mpr hG
  obtain ⟨v, _, huniq⟩ := hC _ hConn
  fin_cases v
  · have heq :
        (SimpleGraph.pathGraph.bicoloring 4) (2 : Fin 4) =
          (SimpleGraph.pathGraph.bicoloring 4) (0 : Fin 4) := by decide
    have hcon := huniq (2 : Fin 4) (Set.mem_univ _) heq
    exact absurd hcon (by decide)
  · have heq :
        (SimpleGraph.pathGraph.bicoloring 4) (3 : Fin 4) =
          (SimpleGraph.pathGraph.bicoloring 4) (1 : Fin 4) := by decide
    have hcon := huniq (3 : Fin 4) (Set.mem_univ _) heq
    exact absurd hcon (by decide)
  · have heq :
        (SimpleGraph.pathGraph.bicoloring 4) (0 : Fin 4) =
          (SimpleGraph.pathGraph.bicoloring 4) (2 : Fin 4) := by decide
    have hcon := huniq (0 : Fin 4) (Set.mem_univ _) heq
    exact absurd hcon (by decide)
  · have heq :
        (SimpleGraph.pathGraph.bicoloring 4) (1 : Fin 4) =
          (SimpleGraph.pathGraph.bicoloring 4) (3 : Fin 4) := by decide
    have hcon := huniq (1 : Fin 4) (Set.mem_univ _) heq
    exact absurd hcon (by decide)

