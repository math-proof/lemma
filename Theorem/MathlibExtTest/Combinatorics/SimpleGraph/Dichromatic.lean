/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/Dichromatic.lean -/


import Def.Combinatorics.SimpleGraph.Dichromatic
import Lemma.SimpleGraph.Dichromatic
open SimpleGraph


-- Normal API use: the canonical orientation/dichromatic predicates accept a
-- graph and elaborate at the expected types.
noncomputable example (G : SimpleGraph (Fin 4)) (D : Fin 4 → Fin 4 → Prop) :
    Prop := G.IsOrientation D

noncomputable example (D : Fin 4 → Fin 4 → Prop)
    (n : ℕ) (f : Fin (n + 2) → Fin 4) : Prop :=
  IsDirectedCycle D n f

noncomputable example (G : SimpleGraph (Fin 4)) : ℕ∞ := G.dichromaticNumber

-- The public characterization exposes the natural-valued infimum whenever a
-- finite dichromatic coloring is available.
example (G : SimpleGraph (Fin 4)) (n : ℕ) (h : G.DichromaticColorable n) :
    G.dichromaticNumber = sInf {n' : ℕ | G.DichromaticColorable n'} :=
  h.dichromaticNumber_eq_sInf

-- Semantic check: edgeless graphs are dichromatically `1`-colourable.
example : (⊥ : SimpleGraph (Fin 4)).DichromaticColorable 1 :=
  DichromaticColorable.of_edgeless _ (fun u v h => by simp at h)

-- The empty digraph orients the edgeless graph.
example : (⊥ : SimpleGraph (Fin 4)).IsOrientation (fun _ _ => False) :=
  IsOrientation.of_edgeless _ (fun u v h => by simp at h)

