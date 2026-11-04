/-
Copyright (c) 2026 Milos Tatarevic and contributors. All rights reserved.
Released under the MIT license in the repository root.
Authors: Milos Tatarevic, OpenAI
-/
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Fintype.Sum

/-!
# Basic Ramsey-coloring definitions

This file fixes the convention used throughout the formalization: a
`SimpleGraph` records the red edges and its complement records the blue
edges.
-/

namespace RamseyIncrement

open SimpleGraph

/-- A red graph is `(k,s)`-free when it has no red `K_k` and its complement
has no blue `K_s`. -/
def IsRamseyFree {V : Type*} (G : SimpleGraph V) (k s : ℕ) : Prop :=
  G.CliqueFree k ∧ Gᶜ.CliqueFree s

/-- The constructive lower-bound assertion on a fixed finite order. -/
def HasRamseyColoring (n k s : ℕ) : Prop :=
  ∃ G : SimpleGraph (Fin n), IsRamseyFree G k s

/-- Every coloring on `n` vertices contains one of the two forbidden
monochromatic cliques. -/
def ForcesRamsey (n k s : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), ¬IsRamseyFree G k s

theorem hasRamseyColoring_iff_not_forcesRamsey (n k s : ℕ) :
    HasRamseyColoring n k s ↔ ¬ForcesRamsey n k s := by
  simp only [HasRamseyColoring, ForcesRamsey]
  push Not
  rfl

theorem IsRamseyFree.symm {V : Type*} {G : SimpleGraph V} {k s : ℕ}
    (hG : IsRamseyFree G k s) : IsRamseyFree Gᶜ s k := by
  rcases hG with ⟨hred, hblue⟩
  refine ⟨hblue, ?_⟩
  simpa using hred

end RamseyIncrement
