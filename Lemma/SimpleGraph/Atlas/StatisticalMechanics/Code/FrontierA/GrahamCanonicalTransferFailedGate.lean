import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferFailedGate
open Finset StatMech StatMech.GrahamGHS StatMech.GrahamGHS.FourColor


/--
[edgeComponent_eq_of_conn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferFailedGate.lean)
-/
@[path]
private lemma edgeComponent_eq_of_conn_eq
  [Fintype I]
  [DecidableEq I]
  {K : Finset I}
  {u v : W}
-- given
  (ends : I -> Sym2 W)
  (huv : connK ends K u v) :
-- imply
  edgeComponent ends K u = edgeComponent ends K v := by
-- proof
  apply StatMech.GrahamGHS.FourColor.edgeComponent_eq_of_conn ends K u v huv

/--
[component_eq_of_not_rowsDisconnect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferFailedGate.lean)
-/
@[path]
private lemma component_eq_of_not_rowsDisconnect_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {k zero : W}
-- given
  (ends : I -> Sym2 W)
  (c : ↑m -> Fin 4)
  (hbad : ¬ RowsDisconnect ends m c k zero) :
-- imply
  edgeComponent ends (rowClass m c 0) zero = edgeComponent ends (rowClass m c 0) k ∨ edgeComponent ends (rowClass m c 1) zero = edgeComponent ends (rowClass m c 1) k := by
-- proof
  apply StatMech.GrahamGHS.FourColor.component_eq_of_not_rowsDisconnect ends m c k zero hbad

/--
[canonicalQuadrangleCompletion_failedGate_component](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferFailedGate.lean)
-/
@[path]
private lemma canonicalQuadrangleCompletion_failedGate_component_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {k zero : W}
-- given
  (ends : I -> Sym2 W)
  (a b c : ↑m -> Fin 4)
  (hbad : ¬ RowsDisconnect ends m (canonicalQuadrangleCompletion ends m k zero a b c) k zero) :
-- imply
  let d := canonicalQuadrangleCompletion ends m k zero a b c edgeComponent ends (rowClass m d 0) zero = edgeComponent ends (rowClass m d 0) k ∨ edgeComponent ends (rowClass m d 1) zero = edgeComponent ends (rowClass m d 1) k := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalQuadrangleCompletion_failedGate_component ends m k zero a b c hbad

/--
[canonicalQuadrangleCompletion_rowBoundaries](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferFailedGate.lean)
-/
@[path]
private lemma canonicalQuadrangleCompletion_rowBoundaries_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {a b c : leftMaskFiber ends m j k l zero p}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l) :
-- imply
  let d := canonicalQuadrangleCompletion ends m k zero a.1.1 b.1.1 c.1.1; sources ends (rowClass m d 0) = {j, k} ∧ sources ends (rowClass m d 1) = {k, l} := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalQuadrangleCompletion_rowBoundaries hloop hjk hkl a b c

/--
[failedRowZero_component_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferFailedGate.lean)
-/
@[path]
private lemma failedRowZero_component_boundary_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k zero : W}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (d : ↑m -> Fin 4)
  (hsrc : sources ends (rowClass m d 0) = {j, k})
  (hconn : connK ends (rowClass m d 0) k zero) :
-- imply
  sources ends (edgeComponent ends (rowClass m d 0) zero) = {j, k} ∧ sources ends (rowClass m d 0 \ edgeComponent ends (rowClass m d 0) zero) = ∅ := by
-- proof
  apply StatMech.GrahamGHS.FourColor.failedRowZero_component_boundary hloop hjk d hsrc hconn

/--
[failedRowOne_component_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferFailedGate.lean)
-/
@[path]
private lemma failedRowOne_component_boundary_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {k l zero : W}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hkl : k ≠ l)
  (d : ↑m -> Fin 4)
  (hsrc : sources ends (rowClass m d 1) = {k, l})
  (hconn : connK ends (rowClass m d 1) k zero) :
-- imply
  sources ends (edgeComponent ends (rowClass m d 1) zero) = {k, l} ∧ sources ends (rowClass m d 1 \ edgeComponent ends (rowClass m d 1) zero) = ∅ := by
-- proof
  apply StatMech.GrahamGHS.FourColor.failedRowOne_component_boundary hloop hkl d hsrc hconn

/--
[canonicalQuadrangleCompletion_failedGate_boundaryCertificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferFailedGate.lean)
-/
@[path]
private lemma canonicalQuadrangleCompletion_failedGate_boundaryCertificate_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {a b c : leftMaskFiber ends m j k l zero p}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hbad : ¬ RowsDisconnect ends m (canonicalQuadrangleCompletion ends m k zero a.1.1 b.1.1 c.1.1) k zero) :
-- imply
  let d := canonicalQuadrangleCompletion ends m k zero a.1.1 b.1.1 c.1.1 (connK ends (rowClass m d 0) k zero ∧ sources ends (edgeComponent ends (rowClass m d 0) zero) = {j, k} ∧ sources ends (rowClass m d 0 \ edgeComponent ends (rowClass m d 0) zero) = ∅) ∨ (connK ends (rowClass m d 1) k zero ∧ sources ends (edgeComponent ends (rowClass m d 1) zero) = {k, l} ∧ sources ends (rowClass m d 1 \ edgeComponent ends (rowClass m d 1) zero) = ∅) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalQuadrangleCompletion_failedGate_boundaryCertificate hloop hjk hkl a b c hbad


-- created on 2026-10-23
