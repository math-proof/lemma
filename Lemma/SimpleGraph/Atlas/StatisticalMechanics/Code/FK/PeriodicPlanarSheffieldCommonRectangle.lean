import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldCommonRectangle
open Filter MeasureTheory Set Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicPlaneEmbedding.exists_commonSquare_fourBoundaryPlacements](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCommonRectangle.lean)
-/
@[path]
private lemma exists_commonSquare_fourBoundaryPlacements_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {buffer : Nat → Nat}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hbuffer : ∀ N, N ≤ buffer N) :
-- imply
  ∃ (M : Nat → Nat) (baseL baseR baseB baseT : Nat → Site 2), (∀ N, P.shift (commonRectLeftShift M N) '' (P.shift (baseL N) '' (P.orbitBox (buffer N) : Set V)) ⊆ E.rectVertices (-(M N : Real)) (M N : Real) (-(M N : Real)) (M N : Real)) ∧ (∀ N, P.shift (commonRectRightShift M N) '' (P.shift (baseR N) '' (P.orbitBox (buffer N) : Set V)) ⊆ E.rectVertices (-(M N : Real)) (M N : Real) (-(M N : Real)) (M N : Real)) ∧ (∀ N, P.shift (commonRectBottomShift M N) '' (P.shift (baseB N) '' (P.orbitBox (buffer N) : Set V)) ⊆ E.rectVertices (-(M N : Real)) (M N : Real) (-(M N : Real)) (M N : Real)) ∧ (∀ N, P.shift (commonRectTopShift M N) '' (P.shift (baseT N) '' (P.orbitBox (buffer N) : Set V)) ⊆ E.rectVertices (-(M N : Real)) (M N : Real) (-(M N : Real)) (M N : Real)) ∧ Tendsto (fun N => mu.real (E.rectSideConnectionEvent (-(M N : Real)) (M N : Real) (-(M N : Real)) (M N : Real) (P.shift (commonRectLeftShift M N) '' (P.shift (baseL N) '' (P.orbitBox N : Set V))) (E.rectLeftBoundaryVertices (-(M N : Real)) (M N : Real) (-(M N : Real)) (M N : Real)))) atTop (nhds 1) ∧ Tendsto (fun N => mu.real (E.rectSideConnectionEvent (-(M N : Real)) (M N : Real) (-(M N : Real)) (M N : Real) (P.shift (commonRectRightShift M N) '' (P.shift (baseR N) '' (P.orbitBox N : Set V))) (E.rectRightBoundaryVertices (-(M N : Real)) (M N : Real) (-(M N : Real)) (M N : Real)))) atTop (nhds 1) ∧ Tendsto (fun N => mu.real (E.rectSideConnectionEvent (-(M N : Real)) (M N : Real) (-(M N : Real)) (M N : Real) (P.shift (commonRectBottomShift M N) '' (P.shift (baseB N) '' (P.orbitBox N : Set V))) (E.rectBottomBoundaryVertices (-(M N : Real)) (M N : Real) (-(M N : Real)) (M N : Real)))) atTop (nhds 1) ∧ Tendsto (fun N => mu.real (E.rectSideConnectionEvent (-(M N : Real)) (M N : Real) (-(M N : Real)) (M N : Real) (P.shift (commonRectTopShift M N) '' (P.shift (baseT N) '' (P.orbitBox N : Set V))) (E.rectTopBoundaryVertices (-(M N : Real)) (M N : Real) (-(M N : Real)) (M N : Real)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_commonSquare_fourBoundaryPlacements E mu hFKG hTI hunique buffer hbuffer


-- created on 2026-10-23
