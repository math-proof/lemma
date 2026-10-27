import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.FreeTailErgodicityPrereq.Part3
open MeasureTheory Set StatMech StatMech.FK


/--
[fkTailEdgeWindow_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeTailErgodicityPrereq.lean)
-/
@[path]
private lemma fkTailEdgeWindow_mono_eq
  {d : ℕ} :
-- imply
  Monotone (fkTailEdgeWindow d) := by
-- proof
  apply StatMech.FK.fkTailEdgeWindow_mono

/--
[fkTailEdgeWindow_escape](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeTailErgodicityPrereq.lean)
-/
@[path]
private lemma fkTailEdgeWindow_escape_eq
  {d : ℕ}
  {F : Finset (Sym2 (Site d))}
  {k : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  ∃ g : Multiplicative (Site d), (↑(F.image (fun e => g⁻¹ • e)) : Set (Sym2 (Site d))) ⊆ (fkTailEdgeWindow d k)ᶜ := by
-- proof
  apply StatMech.FK.fkTailEdgeWindow_escape hd F k

/--
[fk_invariant_event_ae_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FreeTailErgodicityPrereq.lean)
-/
@[path]
private lemma fk_invariant_event_ae_tail_eq
  {d : ℕ}
  {mu : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsFiniteMeasure mu]
-- given
  (hd : 1 ≤ d)
  (hmu : IsTranslationInvariant (G := Multiplicative (Site d)) mu) :
-- imply
  ∀ s : Set (ConfigSpace (Sym2 (Site d))), MeasurableSet s → (∀ g : Multiplicative (Site d), shift g ⁻¹' s = s) → ∃ s' : Set (ConfigSpace (Sym2 (Site d))), FKIsTailEvent d s' ∧ s =ᵐ[mu] s' := by
-- proof
  apply StatMech.FK.fk_invariant_event_ae_tail hd hmu


-- created on 2026-10-23
