/-
Copyright (c) 2026 Milos Tatarevic and contributors. All rights reserved.
Released under the MIT license in the repository root.
Authors: Milos Tatarevic, OpenAI
-/
import RamseyIncrement.SpecialLift
import Mathlib.Combinatorics.SimpleGraph.Sum

/-!
# A red universal-vertex extension

Adding one red-universal vertex turns a `(k,s)`-free graph into a
`(k+1,s)`-free graph (for `s ≥ 2`).  This elementary construction supplies
the strict monotonicity needed to find clique certificates in critical
Ramsey colorings.
-/

namespace RamseyIncrement

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V} {k s : ℕ}

/-- Join `G` to a single red-universal vertex. -/
def redCone (G : SimpleGraph V) : SimpleGraph (V ⊕ Unit) :=
  (Gᶜ ⊕g (⊥ : SimpleGraph Unit))ᶜ

@[simp]
theorem redCone_adj_inl_inl (u v : V) :
    (redCone G).Adj (.inl u) (.inl v) ↔ G.Adj u v := by
  simp only [redCone, SimpleGraph.compl_adj, SimpleGraph.sum_adj_inl]
  constructor
  · rintro ⟨hne, hnot⟩
    by_contra hG
    exact hnot ⟨fun huv ↦ hne (by simp [huv]), hG⟩
  · intro h
    refine ⟨by simpa using h.ne, ?_⟩
    rintro ⟨_, hnot⟩
    exact hnot h

@[simp]
theorem redCone_adj_inl_inr (u : V) (v : Unit) :
    (redCone G).Adj (.inl u) (.inr v) := by
  simp [redCone, SimpleGraph.compl_adj]

@[simp]
theorem redCone_adj_inr_inl (u : Unit) (v : V) :
    (redCone G).Adj (.inr u) (.inl v) := by
  simp [redCone, SimpleGraph.compl_adj]

abbrev ConeLeftIn (K : Finset (V ⊕ Unit)) :=
  {v : V // Sum.inl v ∈ K}

abbrev ConeRightIn (K : Finset (V ⊕ Unit)) :=
  {z : Unit // Sum.inr z ∈ K}

noncomputable instance coneLeftInFintype [Fintype V]
    (K : Finset (V ⊕ Unit)) : Fintype (ConeLeftIn K) :=
  Fintype.ofFinite _

noncomputable instance coneRightInFintype
    (K : Finset (V ⊕ Unit)) : Fintype (ConeRightIn K) :=
  Fintype.ofFinite _

def coneSetEquiv (K : Finset (V ⊕ Unit)) :
    {x // x ∈ K} ≃ ConeLeftIn K ⊕ ConeRightIn K where
  toFun x :=
    match x.1, x.2 with
    | .inl v, hv => .inl ⟨v, hv⟩
    | .inr z, hz => .inr ⟨z, hz⟩
  invFun
    | .inl v => ⟨.inl v.1, v.2⟩
    | .inr z => ⟨.inr z.1, z.2⟩
  left_inv x := by rcases x with ⟨x, hx⟩; cases x <;> rfl
  right_inv x := by rcases x with (v | z) <;> rfl

theorem cone_card_decompose [Fintype V] (K : Finset (V ⊕ Unit)) :
    K.card =
      Fintype.card (ConeLeftIn K) + Fintype.card (ConeRightIn K) := by
  classical
  rw [← Fintype.card_coe K, Fintype.card_congr (coneSetEquiv K)]
  simp

/-- The red-universal-vertex extension preserves the required
Ramsey-freeness. -/
theorem redCone_isRamseyFree [Fintype V]
    (hG : IsRamseyFree G k s) (hs : 2 ≤ s) :
    IsRamseyFree (redCone G) (k + 1) s := by
  classical
  constructor
  · intro K hK
    let leftEmbedding : ConeLeftIn K ↪ V :=
      ⟨Subtype.val, Subtype.val_injective⟩
    have hleft : Fintype.card (ConeLeftIn K) < k := by
      apply card_lt_of_cliqueFree_of_embedding hG.1 leftEmbedding
      intro p q hpq
      change G.Adj p.1 q.1
      exact (redCone_adj_inl_inl p.1 q.1).1
        (hK.isClique p.2 q.2 (by
          intro htag
          apply hpq
          apply Subtype.ext
          exact Sum.inl.inj htag))
    have hright : Fintype.card (ConeRightIn K) ≤ 1 := by
      let rightEmbedding : ConeRightIn K ↪ Unit :=
        ⟨Subtype.val, Subtype.val_injective⟩
      simpa using Fintype.card_le_of_injective
        rightEmbedding rightEmbedding.injective
    have hcard := cone_card_decompose K
    have hKcard := hK.card_eq
    omega
  · intro K hK
    let leftEmbedding : ConeLeftIn K ↪ V :=
      ⟨Subtype.val, Subtype.val_injective⟩
    have hleft : Fintype.card (ConeLeftIn K) < s := by
      apply card_lt_of_cliqueFree_of_embedding hG.2 leftEmbedding
      intro p q hpq
      change Gᶜ.Adj p.1 q.1
      have hadj := hK.isClique p.2 q.2 (by
        intro htag
        apply hpq
        apply Subtype.ext
        exact Sum.inl.inj htag)
      simpa [redCone] using hadj
    have hright : Fintype.card (ConeRightIn K) ≤ 1 := by
      let rightEmbedding : ConeRightIn K ↪ Unit :=
        ⟨Subtype.val, Subtype.val_injective⟩
      simpa using Fintype.card_le_of_injective
        rightEmbedding rightEmbedding.injective
    have hnotBoth :
        Fintype.card (ConeLeftIn K) = 0 ∨
          Fintype.card (ConeRightIn K) = 0 := by
      by_contra h
      push Not at h
      have hLpos : 0 < Fintype.card (ConeLeftIn K) := Nat.pos_of_ne_zero h.1
      have hRpos : 0 < Fintype.card (ConeRightIn K) := Nat.pos_of_ne_zero h.2
      letI : Nonempty (ConeLeftIn K) := Fintype.card_pos_iff.mp hLpos
      letI : Nonempty (ConeRightIn K) := Fintype.card_pos_iff.mp hRpos
      let p : ConeLeftIn K := Classical.choice inferInstance
      let z : ConeRightIn K := Classical.choice inferInstance
      have hadj := hK.isClique p.2 z.2 (by simp)
      simpa [redCone] using hadj
    have hcard := cone_card_decompose K
    have hKcard := hK.card_eq
    rcases hnotBoth with hzero | hzero <;> omega

@[simp]
theorem card_redCone [Fintype V] :
    Fintype.card (V ⊕ Unit) = Fintype.card V + 1 := by
  simp

end RamseyIncrement
