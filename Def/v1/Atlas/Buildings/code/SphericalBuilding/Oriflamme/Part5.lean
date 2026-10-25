/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/Oriflamme.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Determinant
import Def.v1.Atlas.Buildings.code.GeometricAlgebra.ExtendingIsometries
import Lemma.Submodule.OfEq.eq.M.of.Eq
import Lemma.Submodule.Any_EqAndAll_Eq_V.of.IsSubspaceIsometry.EqOrthogonalBilinFormTop_Bot.All_Eq
import Structure.v1.Atlas.Buildings.code.SphericalBuilding.Oriflamme.Part3


namespace Oriflamme

variable (k : Type*) [Field k] (V : Type*) [AddCommGroup V] [Module k V]
         (B : LinearMap.BilinForm k V) (n : ℕ)


/-- A Coxeter matrix is of **type $D_n$** ($n \ge 3$): linear $A_{n-2}$ chain
$1 - 2 - \cdots - (n-2)$ with two extra nodes branching off node $n-3$ at angle $3$ and
commuting with each other ($m = 2$). -/
def TypeDn (hn : n ≥ 3) : Prop :=
  ∃ (m : Fin n → Fin n → ℕ),

    (∀ i, m i i = 1) ∧

    (∀ i j, m i j = m j i) ∧

    (∀ i j : Fin n, i.val + 1 = j.val → j.val + 1 < n →
      m i j = 3) ∧

    (m ⟨n - 3, by omega⟩ ⟨n - 2, by omega⟩ = 3) ∧
    (m ⟨n - 3, by omega⟩ ⟨n - 1, by omega⟩ = 3) ∧

    (m ⟨n - 2, by omega⟩ ⟨n - 1, by omega⟩ = 2) ∧

    (∀ i j : Fin n, i ≠ j → m i j ≠ 1 →
      m i j = 2 ∨ m i j = 3)

/-- The maximal isotropic $n$-subspace $W$ belongs to **orbit class** $\mathrm{cls}$ relative
to the frame $F$ if $W$ is a sum of $n$ frame lines whose parity of `false`-indexed lines
matches $\mathrm{cls}$ (even for `true`, odd for `false`). -/
def IsInOrbitClass (F : OriflammeFrame k V B n) (W : Submodule k V)
    (cls : MaxIsotropicClass) : Prop :=
  IsTotallyIsotropic k V B W ∧
  Module.finrank k W = n ∧
  ∃ (S : Finset (Fin n × Bool)),
    S.card = n ∧
    W = ⨆ ib ∈ S, F.lines ib ∧

    (S.filter (fun ib => ib.2 = false)).card % 2 = if cls then 0 else 1


section DetIsometry

variable {k' : Type*} [Field k'] {V' : Type*} [AddCommGroup V'] [Module k' V']
         [FiniteDimensional k' V']

/-- The **special isometry group** $\mathrm{SO}(V, B) = \{g : g \text{ isometry}, \det g = 1\}$. -/
def SpecialIsometryGroup (B' : LinearMap.BilinForm k' V') : Set (V' ≃ₗ[k'] V') :=
  { g | (∀ v w, B' (g v) (g w) = B' v w) ∧ (g : V' →ₗ[k'] V').det = 1 }

end DetIsometry
end Oriflamme
