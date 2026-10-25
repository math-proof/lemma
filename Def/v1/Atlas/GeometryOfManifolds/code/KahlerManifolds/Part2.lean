/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/KahlerManifolds.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.GeometryOfManifolds.code.AlmostComplexManifolds.Part4
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.AlmostComplexManifolds
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.ArnoldConjecture
import Class.v1.Atlas.GeometryOfManifolds.code.ArnoldConjecture.Part4
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Structure.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part3
set_option autoImplicit false


noncomputable section

open scoped Manifold


section DFSKahler

open DifferentialFormSpace


/-- The real part of the $(2,0)$-projection of $df$ for a $(0,1)$-form $f$, evaluated on a pair of vector fields $(u, v)$. -/
def dForm_20_proj
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (J : AlmostComplexStr (inst := inst))
    (f : Form01 J) (u v : VF) : Ω 0 :=
  inst.ι v (inst.ι u (inst.d f.re)) - inst.ι (J.J v) (inst.ι (J.J u) (inst.d f.re))
  + inst.ι (J.J v) (inst.ι u (inst.d f.im)) + inst.ι v (inst.ι (J.J u) (inst.d f.im))

/-- The imaginary part of the $(2,0)$-projection of $df$ for a $(0,1)$-form $f$, evaluated on a pair of vector fields $(u, v)$. -/
def dForm_20_proj_im
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (J : AlmostComplexStr (inst := inst))
    (f : Form01 J) (u v : VF) : Ω 0 :=
  inst.ι v (inst.ι u (inst.d f.im)) - inst.ι (J.J v) (inst.ι (J.J u) (inst.d f.im))
  - inst.ι v (inst.ι (J.J u) (inst.d f.re)) - inst.ι (J.J v) (inst.ι u (inst.d f.re))

/-- Evaluation of the Nijenhuis dual on the real part of $f$: $\iota_{N(u,v)} f_{\mathrm{re}}$. -/
def nijenhuis_dual_eval
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {J : AlmostComplexStr (inst := inst)}
    (nij : NijenhuisTensor J) (f : Form01 J) (u v : VF) : Ω 0 :=
  inst.ι (nij.N u v) f.re

/-- Evaluation of the Nijenhuis dual on the imaginary part of $f$: $\iota_{N(u,v)} f_{\mathrm{im}}$. -/
def nijenhuis_dual_eval_im
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {J : AlmostComplexStr (inst := inst)}
    (nij : NijenhuisTensor J) (f : Form01 J) (u v : VF) : Ω 0 :=
  inst.ι (nij.N u v) f.im

end DFSKahler
end
