import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.CuspForm.PeterssonOn
open MeasureTheory Matrix
open scoped MatrixGroups ModularForm
open CuspForm


/--
[peterssonOn_def](Lemma/Definitions/Def_CuspForm_PeterssonOn.lean)
-/
@[path]
private lemma main
  {Γ : Subgroup (SpecialLinearGroup (Fin 2) ℤ)}
  {k : ℤ}
  {f g : UpperHalfPlane → ℂ} :
-- imply
  peterssonOn Γ k f g =
    integral (volume.restrict ModularGroup.fd) (peterssonOnIntegrand Γ k f g) := by
-- proof
  apply peterssonOn_def


-- created on 2026-10-24
