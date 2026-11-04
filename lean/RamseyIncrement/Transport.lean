/-
Copyright (c) 2026 Milos Tatarevic and contributors. All rights reserved.
Released under the MIT license in the repository root.
Authors: Milos Tatarevic, OpenAI
-/
import RamseyIncrement.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fintype.EquivFin

/-!
# Transporting finite colorings

The constructions use descriptive tagged vertex types.  This module proves
that a verified coloring may be transported to the canonical `Fin n` type
used in numerical lower-bound statements.
-/

namespace RamseyIncrement

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V} {k s : ℕ}

/-- Ramsey-freeness is preserved when a finite graph is transported to its
canonical `Fin` vertex type. -/
theorem IsRamseyFree.overFin [Fintype V] (hG : IsRamseyFree G k s)
    {m : ℕ} (hcard : Fintype.card V = m) :
    IsRamseyFree (G.overFin hcard) k s := by
  let e := G.overFinIso hcard
  constructor
  · exact hG.1.comap e.isContained'
  · exact hG.2.comap
      (SimpleGraph.Embedding.complEquiv e.symm.toEmbedding).isContained

end RamseyIncrement
