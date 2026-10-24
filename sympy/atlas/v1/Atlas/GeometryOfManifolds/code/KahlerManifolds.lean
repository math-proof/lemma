/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/KahlerManifolds.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.GeometryOfManifolds.code.AlmostComplexManifolds
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.AlmostComplexManifolds
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.ArnoldConjecture
import sympy.atlas.v1.Atlas.GeometryOfManifolds.code.ArnoldConjecture
import Mathlib.Geometry.Manifold.VectorField.LieBracket
import Mathlib.Geometry.Manifold.IsManifold.Basic

set_option autoImplicit false

noncomputable section

open scoped Manifold


section MfdKahler

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]

/-- A symplectic form on a manifold: a smoothly varying nondegenerate antisymmetric bilinear form $\omega_x$ on each tangent space $T_x M$. -/
structure SymplecticFormOnMfd
    (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] where
  ω : ∀ (x : M), TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ
  antisymm : ∀ (x : M) (u v : TangentSpace I x), ω x u v = -(ω x v u)
  nondegenerate : ∀ (x : M) (u : TangentSpace I x),
    (∀ v : TangentSpace I x, ω x u v = 0) → u = 0
  closed : True

variable {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The Nijenhuis tensor field of an almost complex structure $J$: $N_J(U,V) = [JU, JV] - J[U, JV] - J[JU, V] - [U, V]$. -/
def nijenhuisTensorField [IsManifold I ⊤ M]
    (Jstr : AlmostComplexStructure I M)
    (U V : ∀ (x : M), TangentSpace I x) (x : M) : TangentSpace I x :=
  let JU : ∀ y : M, TangentSpace I y := fun y => Jstr.J y (U y)
  let JV : ∀ y : M, TangentSpace I y := fun y => Jstr.J y (V y)
  VectorField.mlieBracket I JU JV x
    - Jstr.J x (VectorField.mlieBracket I U JV x)
    - Jstr.J x (VectorField.mlieBracket I JU V x)
    - VectorField.mlieBracket I U V x

/-- An almost complex structure is integrable (i.e., a complex structure) when its Nijenhuis tensor vanishes identically. -/
structure IsIntegrableACS [IsManifold I ⊤ M]
    (Jstr : AlmostComplexStructure I M) : Prop where
  nijenhuis_vanishes : ∀ (U V : ∀ x : M, TangentSpace I x) (x : M),
    nijenhuisTensorField Jstr U V x = 0

/-- $J$ is compatible with $\omega$: $\omega(JU, JV) = \omega(U, V)$ and $\omega(u, Ju) > 0$ for $u \ne 0$ (taming). -/
structure IsCompatibleMfd [IsManifold I ⊤ M]
    (ω : SymplecticFormOnMfd I M) (Jstr : AlmostComplexStructure I M) : Prop where
  preserves : ∀ (x : M) (u v : TangentSpace I x),
    ω.ω x (Jstr.J x u) (Jstr.J x v) = ω.ω x u v
  taming : ∀ (x : M) (u : TangentSpace I x), u ≠ 0 → ω.ω x u (Jstr.J x u) > 0

/-- A Kähler structure on $M$: a symplectic form $\omega$ and an integrable almost complex structure $J$ that are compatible. -/
structure KahlerStructure
    (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ⊤ M] where
  ω : SymplecticFormOnMfd I M
  J : AlmostComplexStructure I M
  integrable : IsIntegrableACS J
  compatible : IsCompatibleMfd ω J

end MfdKahler


section DFSKahler
open DifferentialFormSpace


/-- The Nijenhuis tensor of an almost complex structure $J$, packaged as a bilinear vector-field-valued operation $N(U, V)$ that is antisymmetric on $1$-forms. -/
structure NijenhuisTensor
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (J : AlmostComplexStr (inst := inst)) where
  N : VF → VF → VF
  antisymm : ∀ (u v : VF) (α : Ω 1),
    inst.ι (N u v) α = -(inst.ι (N v u) α)


/-- `nij` represents the Nijenhuis tensor of $J$, i.e. it equals $[JX, JY] - J[JX, Y] - J[X, JY] - [X, Y]$ as evaluated on $1$-forms. -/
structure IsNijenhuisOf
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [hbr : HasLieBracket Ω VF]
    (J : AlmostComplexStr (inst := inst))
    (nij : NijenhuisTensor J) : Prop where
  nijenhuis_eq : ∀ (X Y : VF) {p : ℕ} (α : Ω (p + 1)),
    inst.ι (nij.N X Y) α =
      inst.ι (hbr.bracket (J.J X) (J.J Y)) α
      - inst.ι (J.J (hbr.bracket (J.J X) Y)) α
      - inst.ι (J.J (hbr.bracket X (J.J Y))) α
      - inst.ι (hbr.bracket X Y) α
  nijenhuis_eq_J : ∀ (X Y : VF) {p : ℕ} (α : Ω (p + 1)),
    inst.ι (J.J (nij.N X Y)) α =
      inst.ι (J.J (hbr.bracket (J.J X) (J.J Y))) α
      - inst.ι (J.J (J.J (hbr.bracket (J.J X) Y))) α
      - inst.ι (J.J (J.J (hbr.bracket X (J.J Y)))) α
      - inst.ι (J.J (hbr.bracket X Y)) α


/-- The almost complex structure $J$ is integrable when its Nijenhuis tensor vanishes when paired with any $1$-form. -/
structure IsIntegrable
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (J : AlmostComplexStr (inst := inst))
    (nij : NijenhuisTensor J) : Prop where
  vanishes : ∀ (u v : VF) (α : Ω 1), inst.ι (nij.N u v) α = 0


/-- A symplectic manifold $(M, \omega)$ together with $J$ is Kähler when $J$ is an integrable almost complex structure compatible with $\omega$. -/
structure IsKahler
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [HasLieBracket Ω VF]
    (S : SymplecticManifold Ω VF) (J : AlmostComplexStr (inst := inst)) : Prop where
  integrable : ∃ nij : NijenhuisTensor J, IsNijenhuisOf J nij ∧ IsIntegrable J nij
  compatible : IsCompatibleACS S J


/-- The Dolbeault operators $\partial$ and $\bar\partial$ on a complex manifold, satisfying $d = \partial + \bar\partial$, $\partial^2 = 0$, $\bar\partial^2 = 0$. -/
structure DolbeaultOps
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF] where
  del : ∀ {p : ℕ}, Ω p → Ω (p + 1)
  delbar : ∀ {p : ℕ}, Ω p → Ω (p + 1)
  decomp : ∀ {p : ℕ} (α : Ω p), inst.d α = del α + delbar α
  del_sq : ∀ {p : ℕ} (α : Ω p), del (del α) = 0
  delbar_sq : ∀ {p : ℕ} (α : Ω p), delbar (delbar α) = 0
  delbar_add : ∀ {p : ℕ} (α β : Ω p), delbar (α + β) = delbar α + delbar β
  delbar_smul : ∀ {p : ℕ} (r : ℝ) (α : Ω p), delbar (r • α) = r • delbar α


/-- A function $\varphi$ is strictly plurisubharmonic when the $(1,1)$-form $\partial\bar\partial\varphi$ is nondegenerate as a pairing on vector fields. -/
class IsStrictlyPlurisubharmonic
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (dol : DolbeaultOps (inst := inst)) (φ : Ω 0) : Prop where
  nondeg : Function.Injective (fun (X : VF) => inst.ι X (dol.del (dol.delbar φ)))


/-- A $(0,1)$-form represented by real and imaginary $1$-forms $(\mathrm{re}, \mathrm{im})$ satisfying the type condition $\iota_X \mathrm{im} = \iota_{JX} \mathrm{re}$. -/
structure Form01
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (J : AlmostComplexStr (inst := inst)) where
  re : Ω 1
  im : Ω 1
  type_cond : ∀ (X : VF), inst.ι X im = inst.ι (J.J X) re

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
