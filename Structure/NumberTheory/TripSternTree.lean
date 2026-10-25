/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/TripSternTree.lean -/

import Mathlib.Data.Finset.Basic


namespace MetaMathlibExt

/-- The TRIP-Stern tree for a fixed pair of source transitions induced by `F_0`
and `F_1`: a distinguished root seed together with a fixed left transition and
a fixed right transition on node values. A left edge is represented by `false`
and a right edge by `true`.

Source: Ilya Amburg, Krishna Dasaratha, Laure Flapan, Thomas Garrity, Chansoo Lee, Cornelia Mihaila,
Nicholas Neumann-Chun, Sarah Peluse, and Matthew Stoffregen, *Stern Sequences for a Family of
Multidimensional Continued Fractions: TRIP-Stern Sequences*, Journal of Integer Sequences 20 (2017),
Article 17.1.7, <https://cs.uwaterloo.ca/journals/JIS/VOL20/Garrity/garrity6.tex>. The tree
abstracts Definition TRIPSternDef, lines 471-481 (seed (1,1,1), even/odd recursion by F_0/F_1,
levels as index intervals), with F_0/F_1 from line 387; binary paths follow the triangle(v)
definition, lines 485-488. -/
structure TripSternTree (α : Type _) where
  /-- Distinguished root seed of the tree. Source: Amburg et al., *TRIP-Stern Sequences*, JIS 20
  (2017), Article 17.1.7, Definition TRIPSternDef, lines 471-481. -/
  seed : α
  /-- Fixed left transition (induced by `F_0`), taken on a `false` edge.
  Source: Amburg et al., *TRIP-Stern Sequences*, JIS 20 (2017), Article 17.1.7, Definition
  TRIPSternDef, lines 471-481. -/
  leftTransition : α → α
  /-- Fixed right transition (induced by `F_1`), taken on a `true` edge.
  Source: Amburg et al., *TRIP-Stern Sequences*, JIS 20 (2017), Article 17.1.7, Definition
  TRIPSternDef, lines 471-481. -/
  rightTransition : α → α

end MetaMathlibExt
