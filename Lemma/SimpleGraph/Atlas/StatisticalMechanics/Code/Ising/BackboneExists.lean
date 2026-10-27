import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.BackboneExists
open Finset Classical StatMech StatMech.Ising


/--
[bbe_backbone_path](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/BackboneExists.lean)
-/
@[path]
private lemma bbe_backbone_path_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {m : Current V}
  {o x : V}
-- given
  (hox : o ≠ x)
  (hconn : connP (oddEdges E m) o x) :
-- imply
  ∃ P₁ ⊆ oddEdges E m, srcP P₁ = ({o, x} : Finset V) := by
-- proof
  apply StatMech.Ising.bbe_backbone_path E m hox hconn

/--
[bbe_backbone_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/BackboneExists.lean)
-/
@[path]
private lemma bbe_backbone_exists_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {m : Current V}
  {o x y : V}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hconnx : connP (oddEdges E m) o x)
  (hconny : connP (oddEdges E m) o y) :
-- imply
  ∃ P ⊆ oddEdges E m, srcP P = ({x, y} : Finset V) ∧ (∀ e ∈ P, Odd (m e)) := by
-- proof
  apply StatMech.Ising.bbe_backbone_exists E m hox hoy hxy hconnx hconny

/--
[bbe_backbone_toggle_disconnects](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/BackboneExists.lean)
-/
@[path]
private lemma bbe_backbone_toggle_disconnects_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {m : Current V}
  {P : Finset (Sym2 V)}
  {x y : V}
  {n : Current V}
-- given
  (hPE : P ⊆ E)
  (hPodd : ∀ e ∈ P, Odd (m e))
  (hPsrc : srcP P = ({x, y} : Finset V))
  (hn : ∀ e, n e ≤ m e) :
-- imply
  sources E (reflect m P n) = sources E n ∆ ({x, y} : Finset V) := by
-- proof
  apply StatMech.Ising.bbe_backbone_toggle_disconnects E m P hPE hPodd hPsrc n hn

/--
[bbe_backbone_toggle_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/BackboneExists.lean)
-/
@[path]
private lemma bbe_backbone_toggle_weight_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : Current V}
  {P : Finset (Sym2 V)}
  {n : Current V}
-- given
  (hn : ∀ e, n e ≤ m e) :
-- imply
  Sharpness.weight G β J (reflect m P n) * Sharpness.weight G β J (fun e => m e - reflect m P n e) = Sharpness.weight G β J n * Sharpness.weight G β J (fun e => m e - n e) := by
-- proof
  apply StatMech.Ising.bbe_backbone_toggle_weight E G β J m P hn

/--
[bbe_backbone_exists_toggle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/BackboneExists.lean)
-/
@[path]
private lemma bbe_backbone_exists_toggle_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : Current V}
  {o x y : V}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hconnx : connP (oddEdges G.edgeFinset m) o x)
  (hconny : connP (oddEdges G.edgeFinset m) o y) :
-- imply
  ∃ P ⊆ oddEdges G.edgeFinset m, srcP P = ({x, y} : Finset V) ∧ (∀ e ∈ P, Odd (m e)) ∧ (∀ n : Current V, (∀ e, n e ≤ m e) → Sharpness.sources G (reflect m P n) = Sharpness.sources G n ∆ ({x, y} : Finset V)) ∧ (∀ n : Current V, (∀ e, n e ≤ m e) → Sharpness.weight G β J (reflect m P n) * Sharpness.weight G β J (fun e => m e - reflect m P n e) = Sharpness.weight G β J n * Sharpness.weight G β J (fun e => m e - n e)) := by
-- proof
  apply StatMech.Ising.bbe_backbone_exists_toggle E G β J m hox hoy hxy hconnx hconny


-- created on 2026-10-23
