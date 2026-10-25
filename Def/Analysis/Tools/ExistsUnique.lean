import Mathlib


/-!
# API for ExistsUnique

Here we review some of the API provided for {name}`ExistsUnique` in Mathlib, and provide some additional tools.  (Some of these might be suitable for upstreaming to Mathlib.)

-/
noncomputable def ExistsUnique.choose {α: Sort*} {p: α → Prop} (h : ∃! x, p x) : α := h.exists.choose

