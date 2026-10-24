/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RepresentationTheory/Homological/TateCohomology/FiniteCyclic.lean -/


import sympy.atlas.RepresentationTheory.Homological.TateCohomology.FiniteCyclic
import Lemma.Int.Nonempty_TateCohomology

open CategoryTheory TateCohomology

universe u

variable {R G : Type u} [CommRing R] [Group G] [Fintype G] [IsCyclic G]

variable (A : Rep R G)

example (n : ℤ) : Nonempty (↑(tateCohomology A n) ≃+ ↑(tateCohomology A (n + 2))) := by
  obtain ⟨e⟩ := TateCohomology.nonempty_periodicityIso A n
  exact ⟨e.toLinearEquiv.toAddEquiv⟩

example : Nonempty (tateCohomology A 0 ≅ tateCohomology A 2) := by
  simpa using TateCohomology.nonempty_periodicityIso A 0

example : Nonempty (tateCohomology A (-1) ≅ tateCohomology A 1) := by
  simpa using TateCohomology.nonempty_periodicityIso A (-1)

example : Nonempty (tateCohomology A (-2) ≅ tateCohomology A 0) := by
  simpa using TateCohomology.nonempty_periodicityIso A (-2)

example : Nonempty (tateCohomology A (-3) ≅ tateCohomology A (-1)) := by
  simpa using TateCohomology.nonempty_periodicityIso A (-3)

example : Nonempty (tateCohomology A (-6) ≅ tateCohomology A (-4)) := by
  simpa using TateCohomology.nonempty_periodicityIso A (-6)
