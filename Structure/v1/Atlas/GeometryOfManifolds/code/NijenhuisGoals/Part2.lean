/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/NijenhuisGoals.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
import Def.v1.Atlas.GeometryOfManifolds.code.NijenhuisGoals
set_option autoImplicit false
set_option maxHeartbeats 800000

open DifferentialFormSpace


/-- A $(0,1)$-form on a manifold with almost complex structure $J$: real and imaginary parts
$\alpha = \mathrm{re} + i\, \mathrm{im}$ satisfying the type condition
$\mathrm{im}(X) = \mathrm{re}(JX)$, so $\alpha \in \wedge^{0,1} T^*M$. -/
structure Form01OnMfd (Jstr : ACSOnMfd I M) where
  re : ∀ x : M, TangentSpace I x →L[ℝ] ℝ
  im : ∀ x : M, TangentSpace I x →L[ℝ] ℝ
  type_cond : ∀ (X : ∀ x : M, TangentSpace I x) (x : M),
    (im x) (X x) = (re x) (Jstr.J x (X x))

/-- Cartan-calculus data on a manifold: an evaluation map for $d\alpha(X, Y)$ via the Cartan
formula $d\alpha(X, Y) = X(\alpha(Y)) - Y(\alpha(X)) - \alpha([X, Y])$, the Lie derivative on
functions, and the $(2,0)$-component $(d\alpha)^{(2,0)}$ of $d$ applied to a $(0,1)$-form. -/
structure CartanDataOnMfd (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    (Jstr : ACSOnMfd I M) where
  d_eval : (∀ x : M, TangentSpace I x →L[ℝ] ℝ) →
    (∀ x : M, TangentSpace I x) → (∀ x : M, TangentSpace I x) → M → ℝ
  lieD : (∀ x : M, TangentSpace I x) → (M → ℝ) → M → ℝ
  cartan : ∀ (α : ∀ x : M, TangentSpace I x →L[ℝ] ℝ)
    (X Y : ∀ x : M, TangentSpace I x) (x : M),
    d_eval α X Y x =
      lieD X (fun y => (α y) (Y y)) x
      - lieD Y (fun y => (α y) (X y)) x
      - (α x) (VectorField.mlieBracket I X Y x)
  lieD_sub : ∀ (X : ∀ x : M, TangentSpace I x) (f g : M → ℝ) (x : M),
    lieD X (fun y => f y - g y) x = lieD X f x - lieD X g x
  lieD_neg : ∀ (X : ∀ x : M, TangentSpace I x) (f : M → ℝ) (x : M),
    lieD X (fun y => -(f y)) x = -(lieD X f x)
  d_antisymm : ∀ (α : ∀ x : M, TangentSpace I x →L[ℝ] ℝ)
    (X Y : ∀ x : M, TangentSpace I x) (x : M),
    d_eval α X Y x = -(d_eval α Y X x)
  dForm20 : Form01OnMfd Jstr → ∀ x : M, TangentSpace I x [⋀^Fin 2]→ₗ[ℝ] ℝ
  dForm20_eval : ∀ (f : Form01OnMfd Jstr) (U V : ∀ x : M, TangentSpace I x) (x : M),
    (dForm20 f x) ![U x, V x] =
      d_eval f.re U V x
      - d_eval f.re (fun y => Jstr.J y (U y)) (fun y => Jstr.J y (V y)) x
      + d_eval f.im U (fun y => Jstr.J y (V y)) x
      + d_eval f.im (fun y => Jstr.J y (U y)) V x

