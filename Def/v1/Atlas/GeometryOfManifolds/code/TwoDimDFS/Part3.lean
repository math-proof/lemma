/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/TwoDimDFS.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.DifferentialForms.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.DifferentialForms
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticManifolds
import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds.Part3
import Instance.v1.Atlas.GeometryOfManifolds.code.TwoDimDFS.Part2
set_option autoImplicit false
set_option maxHeartbeats 800000


noncomputable section

/-- The standard symplectic structure on $\mathbb{R}^2$: the constant area form
$\omega = 1 \in \Omega^2$, which is closed and nondegenerate. -/
noncomputable def symp2Manifold : SymplecticManifold Symp2Ω Symp2VF where
  ω := (1 : Poly2)
  closed := by
    show symp2d (p := 2) (1 : Poly2) = (0 : Symp2Ω 3)
    rfl
  nondegenerate := by
    show Function.Injective (fun (X : Symp2VF) => symp2Iota X (p := 1) (1 : Poly2))
    intro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
    simp [symp2Iota] at h
    exact Prod.ext h.2 h.1


/-- Hodge star operator on polynomial forms on $\mathbb{R}^2$: $\star f = f$ on $0$- and $2$-forms,
and $\star(f\, dx + g\, dy) = -g\, dx + f\, dy$ on $1$-forms. -/
noncomputable def symp2HodgeStar : ∀ {p : ℕ}, Symp2Ω p → Symp2Ω p
  | 0, f => f
  | 1, (f, g) => (-g, f)
  | 2, h => h
  | _ + 3, x => x

end
