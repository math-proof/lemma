import Mathlib
import Lemma.Fin.LinearIndependent_RothKronecker.of.All_RothKroneckerBounded.LinearIndependent.Gt_1
import Lemma.Polynomial.Det_PowDerivativeGetVal.ne.Zero.of.LinearIndependent
import Lemma.Submodule.Any_And_All_In.of.All_In_Span.NeDet_0
import Lemma.Submodule.RothPolyDerivativeRow_RothKronecker.in.Span_XRothKronHasseJetRows
open MathlibExt.NumberTheory.RothAuxiliary
open Fin
open Polynomial
open Submodule


/--
[roth_exists_generalized_wronskian_of_bounded](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m k D : ℕ}
-- given
  (f : Fin k → MvPolynomial (Fin m) ℚ)
  (hD : 1 < D)
  (hf : LinearIndependent ℚ f)
  (hb : ∀ j, rothKroneckerBounded D (f j)) :
-- imply
  ∃ i : Fin k → RothMvIndex m,
    (∀ s, rothMvOrder (i s) ≤ s) ∧
      (Matrix.det fun s j ↦ rothMvHasse (i s) (f j)) ≠ 0 := by
-- proof
  classical
  let g : Fin k → ℚ[X] := fun j ↦ rothKronecker D (f j)
  have hg : LinearIndependent ℚ g :=
    LinearIndependent_RothKronecker.of.All_RothKroneckerBounded.LinearIndependent.Gt_1
      f hD hf hb
  let A : Matrix (Fin k) (Fin k) ℚ[X] :=
    fun s j ↦ (derivative^[s.val]) (g j)
  have hA : A.det ≠ 0 :=
    Det_PowDerivativeGetVal.ne.Zero.of.LinearIndependent g hg
  have hArows : ∀ s : Fin k,
      A s ∈ Submodule.span ℚ[X] (rothKronHasseJetRows D f s) := by
    intro s
    exact RothPolyDerivativeRow_RothKronecker.in.Span_XRothKronHasseJetRows D f s
  obtain ⟨B, hB, hBrows⟩ :=
    Any_And_All_In.of.All_In_Span.NeDet_0 A
      (fun s ↦ rothKronHasseJetRows D f s) hA hArows
  choose i hi hrow using hBrows
  refine ⟨i, hi, ?_⟩
  let C : Matrix (Fin k) (Fin k) (MvPolynomial (Fin m) ℚ) :=
    fun s j ↦ rothMvHasse (i s) (f j)
  have hBC : B = (rothKronecker D).mapMatrix C := by
    ext s j
    rw [hrow s]
    rfl
  have hmapdet : rothKronecker D C.det = B.det := by
    rw [RingHom.map_det, ← hBC]
  intro hC
  apply hB
  rw [← hmapdet, hC, map_zero]


-- created on 2026-10-21
