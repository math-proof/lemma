module
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Def.v1.Atlas.ArithmeticGeometry.code.JInvariant.Part3
public import Theorem.Scheme.Atlas.v1.ArithmeticGeometry.code.JInvariant
public import Abbrev.v1.Atlas.ArithmeticGeometry.code.Twists
open AlgebraicGeometry CategoryTheory Limits


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Twists.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
universe u


namespace ArithmeticGeometry

variable (k : Type u) [Field k]

/-- The morphism of schemes $\mathrm{Spec}\, \overline{k} \to \mathrm{Spec}\, k$
induced by the algebraic closure inclusion $k \hookrightarrow \overline{k}$. -/
noncomputable def specAlgClosureToSpec :
    specOf (AlgebraicClosure k) ⟶ specOf k :=
  Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))

/-- Base change of a $k$-scheme $X$ along the algebraic closure, producing the
$\overline{k}$-scheme $X_{\overline{k}} := X \times_{\mathrm{Spec}\, k} \mathrm{Spec}\, \overline{k}$. -/
noncomputable def baseChangeToAlgClosure (X : Scheme.{u}) [X.Over (specOf k)] : Scheme.{u} :=
  pullback (X ↘ specOf k) (specAlgClosureToSpec k)

end ArithmeticGeometry
