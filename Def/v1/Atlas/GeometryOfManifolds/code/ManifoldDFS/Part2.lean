/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/ManifoldDFS.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Analysis.Normed.Module.Alternating.Uncurry.Fin
import Mathlib.Analysis.Calculus.VectorField
import Def.v1.Atlas.GeometryOfManifolds.code.DifferentialForms.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.DifferentialForms
import Def.v1.Atlas.GeometryOfManifolds.code.OmitIndex
import Instance.v1.Atlas.GeometryOfManifolds.code.ManifoldDFS
set_option autoImplicit false
set_option maxHeartbeats 400000

open scoped Manifold ContDiff


namespace ManifoldWedgeHelpers

section WedgeHelpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Convert a continuous alternating $1$-form $w \in \Lambda^1 E^*$ to a continuous linear
functional $E \to \mathbb{R}$, using the canonical identification of singleton-indexed
alternating maps with linear maps. -/
noncomputable def oneFormToCL
    (w : E [⋀^Fin 1]→L[ℝ] ℝ) : E →L[ℝ] ℝ :=
  (ContinuousAlternatingMap.ofSubsingleton ℝ E ℝ (0 : Fin 1)).symm w

/-- Pointwise wedge product of a $1$-form $w$ with a $p$-form $a$, producing a $(p+1)$-form
$w \wedge a$ via antisymmetrization of $(v_0, v_1, \dots, v_p) \mapsto w(v_0) \cdot a(v_1, \dots, v_p)$. -/
noncomputable def wedgePointwiseGeneral {p : ℕ}
    (w : E [⋀^Fin 1]→L[ℝ] ℝ) (a : E [⋀^Fin p]→L[ℝ] ℝ) :
    E [⋀^Fin (p + 1)]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.alternatizeUncurryFin ((oneFormToCL w).smulRight a)

/-- Multiplication of a $p$-form $\alpha$ by a scalar function $f \in \Omega^0$:
$(f \cdot \alpha)_x = f(x) \cdot \alpha_x$. -/
noncomputable def manifoldFMul {p : ℕ}
    (f : ManifoldΩ I M 0) (α : ManifoldΩ I M p) : ManifoldΩ I M p :=
  fun x => (f x Fin.elim0) • (α x)

/-- Interior product $\iota_X \alpha$: contracts a vector field $X$ into the first slot of
a $(p+1)$-form $\alpha$, producing a $p$-form. -/
noncomputable def manifoldIota (X : ManifoldVF I M) {p : ℕ}
    (α : ManifoldΩ I M (p + 1)) : ManifoldΩ I M p :=
  fun x => (α x).curryLeft (X x)

/-- The **exterior derivative** $d : \Omega^p(M) \to \Omega^{p+1}(M)$. On a function $f$,
$df$ is the differential. On a $(p+1)$-form $\alpha$, $d\alpha$ is given by the invariant
formula involving $\sum_i (-1)^i \, \partial_{v_i}(\alpha(\hat v_i))$. -/
noncomputable def manifoldWedge1 {p : ℕ}
    (w : ManifoldΩ I M 1) (α : ManifoldΩ I M p) : ManifoldΩ I M (p + 1) :=
  fun x => wedgePointwiseGeneral (w x) (α x)

/-- The Lie derivative is additive in the form: $\mathcal{L}_X(\alpha + \beta) = \mathcal{L}_X \alpha + \mathcal{L}_X \beta$. -/
noncomputable def fixOtherSlots {p : ℕ} (α : ManifoldΩ I M p)
    (i : Fin (p + 1)) (vs : Fin (p + 1) → E) : M → ℝ :=
  fun y => (α y) (Fin.removeNth i vs)

end Operations

/-- **The differential-form-space (DFS) structure on a smooth manifold $M$.** This bundles
the exterior derivative $d$, the interior product $\iota_X$, multiplication by functions,
wedge with $1$-forms, and the Lie derivative $\mathcal{L}_X$, together with all their
algebraic identities ($d^2 = 0$, Leibniz, Cartan, nondegeneracy of $\iota$). -/

@[reducible]

section TermB

open VectorField

/-- The "Lie-bracket term" appearing in the invariant Cartan formula for $d\alpha$:
$$\sum_{i < j} (-1)^{i+j} \, \alpha([V_i, V_j], V_0, \dots, \hat V_i, \dots, \hat V_j, \dots).$$
For constant vector fields this term vanishes by `lieBracket_constVF`. -/
noncomputable def termB {p : ℕ} (α : ManifoldΩ I M (p + 1))
    (x : M) (vs : Fin (p + 2) → E) : ℝ :=
  ∑ ij ∈ Finset.filter (fun ij : Fin (p + 2) × Fin (p + 2) => ij.1 < ij.2) Finset.univ,
    (-1 : ℝ) ^ ((ij.1 : ℕ) + (ij.2 : ℕ)) *
      (α x) (Fin.cons
        (lieBracket ℝ (fun _ : E => vs ij.1) (fun _ : E => vs ij.2) 0)
        (fun _ => (0 : E)))

end TermB
end ManifoldWedgeHelpers
