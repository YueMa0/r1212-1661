/-
Copyright (c) 2026 Milos Tatarevic and contributors. All rights reserved.
Released under the MIT license in the repository root.
Authors: Milos Tatarevic, OpenAI
-/
import RamseyIncrement.Cone
import RamseyIncrement.Transport
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

/-!
# A local finite Ramsey number

Mathlib does not currently expose the classical two-color graph Ramsey
number as a definition.  This file supplies the small amount of general
infrastructure needed by the numerical wrapper:

* an elementary recursive finite upper bound;
* existence of a least forcing order;
* the critical-coloring and monotonicity lemmas used by lower bounds.

The upper bound is deliberately crude.  Its only purpose is to make the
least-number definition axiom-free.
-/

namespace RamseyIncrement

open SimpleGraph

universe u

/-- A deliberately nonoptimal finite Ramsey bound.  The extra one in the
recurrence makes the neighborhood pigeonhole argument especially direct. -/
def crudeRamseyBound : ℕ → ℕ → ℕ
  | 0, _ => 0
  | _ + 1, 0 => 0
  | k + 1, s + 1 =>
      crudeRamseyBound k (s + 1) + crudeRamseyBound (k + 1) s + 1
termination_by k s => k + s
decreasing_by all_goals omega

/-- `ForcesRamseyCard n k s` means that every finite graph whose order is
at least `n` forces a red `K_k` or a blue `K_s`. -/
def ForcesRamseyCard (n k s : ℕ) : Prop :=
  ∀ (V : Type u) [Fintype V], n ≤ Fintype.card V →
    ∀ G : SimpleGraph V, ¬IsRamseyFree G k s

@[simp]
theorem compl_induce (G : SimpleGraph α) (S : Set α) :
    (G.induce S)ᶜ = Gᶜ.induce S := by
  ext u v
  simp [SimpleGraph.compl_adj, Subtype.ext_iff]

/-- The standard neighborhood recurrence for finite graph Ramsey theory. -/
theorem forcesRamseyCard_step {a b k s : ℕ}
    (ha : ForcesRamseyCard.{u} a k (s + 1))
    (hb : ForcesRamseyCard.{u} b (k + 1) s) :
    ForcesRamseyCard.{u} (a + b + 1) (k + 1) (s + 1) := by
  classical
  intro V _ hcard G hfree
  have hVpos : 0 < Fintype.card V := by omega
  letI : Nonempty V := Fintype.card_pos_iff.mp hVpos
  let v : V := Classical.choice inferInstance
  let NR : Set V := G.neighborSet v
  let NB : Set V := Gᶜ.neighborSet v
  have hsum :
      Fintype.card NR + Fintype.card NB = Fintype.card V - 1 := by
    rw [Set.fintypeCard_eq_ncard, Set.fintypeCard_eq_ncard,
      Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card']
    rw [← Finset.card_union_of_disjoint
      (Set.disjoint_toFinset.mpr (G.compl_neighborSet_disjoint v))]
    rw [← Set.toFinset_union]
    exact G.card_neighborSet_union_compl_neighborSet v
  have hlarge :
      a ≤ Fintype.card NR ∨ b ≤ Fintype.card NB := by
    omega
  rcases hlarge with hNR | hNB
  · have hredOn : G.CliqueFreeOn NR k := by
      have h := CliqueFreeOn.of_succ
        (G := G) (s := Set.univ) (n := k) (a := v)
        hfree.1.cliqueFreeOn (Set.mem_univ v)
      simpa [NR] using h
    have hNRfree : IsRamseyFree (G.induce NR) k (s + 1) := by
      constructor
      · exact (G.cliqueFree_induce_iff NR k).2 hredOn
      · rw [compl_induce]
        exact (Gᶜ.cliqueFree_induce_iff NR (s + 1)).2
          hfree.2.cliqueFreeOn
    exact ha NR hNR (G.induce NR) hNRfree
  · have hblueOn : Gᶜ.CliqueFreeOn NB s := by
      have h := CliqueFreeOn.of_succ
        (G := Gᶜ) (s := Set.univ) (n := s) (a := v)
        hfree.2.cliqueFreeOn (Set.mem_univ v)
      simpa [NB] using h
    have hNBfree : IsRamseyFree (G.induce NB) (k + 1) s := by
      constructor
      · exact (G.cliqueFree_induce_iff NB (k + 1)).2
          hfree.1.cliqueFreeOn
      · rw [compl_induce]
        exact (Gᶜ.cliqueFree_induce_iff NB s).2 hblueOn
    exact hb NB hNB (G.induce NB) hNBfree

/-- The crude recursive bound forces every pair of clique orders. -/
theorem crudeRamseyBound_forcesCard (k s : ℕ) :
    ForcesRamseyCard.{u} (crudeRamseyBound k s) k s := by
  induction k, s using crudeRamseyBound.induct with
  | case1 s =>
      intro V _ _ G hfree
      exact SimpleGraph.not_cliqueFree_zero hfree.1
  | case2 k =>
      intro V _ _ G hfree
      exact SimpleGraph.not_cliqueFree_zero hfree.2
  | case3 k s hk hs =>
      simpa [crudeRamseyBound] using forcesRamseyCard_step hk hs

/-- In particular, a concrete order on `Fin n` eventually forces the two
clique sizes. -/
theorem exists_forcesRamsey (k s : ℕ) : ∃ n, ForcesRamsey n k s := by
  refine ⟨crudeRamseyBound k s, ?_⟩
  intro G
  exact crudeRamseyBound_forcesCard k s (Fin _) (by simp) G

/-- The classical two-color graph Ramsey number, defined as the least
forcing order. -/
noncomputable def ramseyNumber (k s : ℕ) : ℕ :=
  by
    classical
    exact Nat.find (exists_forcesRamsey k s)

theorem ramseyNumber_forces (k s : ℕ) :
    ForcesRamsey (ramseyNumber k s) k s :=
  by
    classical
    exact Nat.find_spec (exists_forcesRamsey k s)

theorem not_forces_of_lt_ramseyNumber {n k s : ℕ}
    (hn : n < ramseyNumber k s) :
    ¬ForcesRamsey n k s := by
  classical
  exact Nat.find_min (exists_forcesRamsey k s) hn

theorem hasRamseyColoring_of_lt_ramseyNumber {n k s : ℕ}
    (hn : n < ramseyNumber k s) :
    HasRamseyColoring n k s :=
  (hasRamseyColoring_iff_not_forcesRamsey n k s).2
    (not_forces_of_lt_ramseyNumber hn)

/-- A critical coloring exists whenever the Ramsey number is positive. -/
theorem critical_coloring (k s : ℕ) (hpos : 0 < ramseyNumber k s) :
    HasRamseyColoring (ramseyNumber k s - 1) k s := by
  apply hasRamseyColoring_of_lt_ramseyNumber
  omega

/-- Any explicit coloring gives the corresponding numerical lower bound. -/
theorem ramseyNumber_lower_bound {n k s : ℕ}
    (h : HasRamseyColoring n k s) :
    n + 1 ≤ ramseyNumber k s := by
  by_contra hnot
  have hle : ramseyNumber k s ≤ n := by omega
  obtain ⟨G, hG⟩ := h
  let f : Fin (ramseyNumber k s) ↪ Fin n :=
    Fin.castLEEmb hle
  let H : SimpleGraph (Fin (ramseyNumber k s)) := G.comap f
  have hH : IsRamseyFree H k s := by
    constructor
    · exact hG.1.comap
        (SimpleGraph.Embedding.comap f G).isContained
    · have hcompl : Hᶜ = Gᶜ.comap f := by
        ext u v
        simp [H, SimpleGraph.compl_adj]
      rw [hcompl]
      exact hG.2.comap
        (SimpleGraph.Embedding.comap f Gᶜ).isContained
  exact ramseyNumber_forces k s H hH

/-- The empty coloring witnesses order zero for positive clique sizes. -/
theorem empty_hasRamseyColoring {k s : ℕ} (hk : 0 < k) (hs : 0 < s) :
    HasRamseyColoring 0 k s := by
  refine ⟨⊥, ?_⟩
  constructor
  · exact SimpleGraph.cliqueFree_of_card_lt (by simpa)
  · exact SimpleGraph.cliqueFree_of_card_lt (by simpa)

theorem ramseyNumber_pos {k s : ℕ} (hk : 0 < k) (hs : 0 < s) :
    0 < ramseyNumber k s := by
  have h := ramseyNumber_lower_bound
    (empty_hasRamseyColoring hk hs)
  omega

/-- Critical colorings exist for every pair of positive clique sizes. -/
theorem exists_critical_coloring {k s : ℕ} (hk : 0 < k) (hs : 0 < s) :
    HasRamseyColoring (ramseyNumber k s - 1) k s :=
  critical_coloring k s (ramseyNumber_pos hk hs)

/-- Complementation exchanges the two forcing parameters. -/
theorem forcesRamsey_symm (n k s : ℕ) :
    ForcesRamsey n k s ↔ ForcesRamsey n s k := by
  constructor
  · intro h G hG
    exact h Gᶜ hG.symm
  · intro h G hG
    exact h Gᶜ hG.symm

/-- Symmetry of the locally defined Ramsey number. -/
theorem ramseyNumber_symm (k s : ℕ) :
    ramseyNumber k s = ramseyNumber s k := by
  classical
  apply le_antisymm
  · apply Nat.find_min' (exists_forcesRamsey k s)
    exact (forcesRamsey_symm (ramseyNumber s k) k s).2
      (ramseyNumber_forces s k)
  · apply Nat.find_min' (exists_forcesRamsey s k)
    exact (forcesRamsey_symm (ramseyNumber k s) s k).2
      (ramseyNumber_forces k s)

/-- Reindex the red-universal-vertex extension as an explicit coloring. -/
theorem redCone_hasRamseyColoring {n k s : ℕ}
    (h : HasRamseyColoring n k s) (hs : 2 ≤ s) :
    HasRamseyColoring (n + 1) (k + 1) s := by
  obtain ⟨G, hG⟩ := h
  let C := redCone G
  have hC : IsRamseyFree C (k + 1) s :=
    redCone_isRamseyFree hG hs
  have hcard : Fintype.card (Fin n ⊕ Unit) = n + 1 := by
    simp
  exact ⟨C.overFin hcard, hC.overFin hcard⟩

/-- Ramsey numbers are strictly increasing in the first parameter once
the other forbidden clique has at least two vertices. -/
theorem ramseyNumber_strictMono_left {k s : ℕ}
    (hk : 0 < k) (hs : 2 ≤ s) :
    ramseyNumber k s + 1 ≤ ramseyNumber (k + 1) s := by
  have hcrit := exists_critical_coloring hk (by omega : 0 < s)
  have hcone := redCone_hasRamseyColoring hcrit hs
  have hlower := ramseyNumber_lower_bound hcone
  have hpos := ramseyNumber_pos hk (by omega : 0 < s)
  omega

/-- The corresponding strict monotonicity in the second parameter follows
by complementation. -/
theorem ramseyNumber_strictMono_right {k s : ℕ}
    (hk : 2 ≤ k) (hs : 0 < s) :
    ramseyNumber k s + 1 ≤ ramseyNumber k (s + 1) := by
  rw [ramseyNumber_symm k s, ramseyNumber_symm k (s + 1)]
  exact ramseyNumber_strictMono_left hs hk

/-- Every critical `(k,s)` coloring contains a red `K_(k-1)`. -/
theorem critical_has_red_certificate {k s : ℕ}
    (hk : 2 ≤ k) (hs : 2 ≤ s)
    (G : SimpleGraph (Fin (ramseyNumber k s - 1)))
    (hG : IsRamseyFree G k s) :
    ¬G.CliqueFree (k - 1) := by
  intro hsmall
  have hfreeSmall : IsRamseyFree G (k - 1) s :=
    ⟨hsmall, hG.2⟩
  have hlower := ramseyNumber_lower_bound
    (show HasRamseyColoring (ramseyNumber k s - 1) (k - 1) s
      from ⟨G, hfreeSmall⟩)
  have hstrict := ramseyNumber_strictMono_left
    (k := k - 1) (s := s) (by omega) hs
  have hkpred : k - 1 + 1 = k := by omega
  rw [hkpred] at hstrict
  have hpos := ramseyNumber_pos (by omega : 0 < k) (by omega : 0 < s)
  omega

/-- Every critical `(k,s)` coloring contains a blue `K_(s-1)`. -/
theorem critical_has_blue_certificate {k s : ℕ}
    (hk : 2 ≤ k) (hs : 2 ≤ s)
    (G : SimpleGraph (Fin (ramseyNumber k s - 1)))
    (hG : IsRamseyFree G k s) :
    ¬Gᶜ.CliqueFree (s - 1) := by
  intro hsmall
  have hfreeSmall : IsRamseyFree G k (s - 1) :=
    ⟨hG.1, hsmall⟩
  have hlower := ramseyNumber_lower_bound
    (show HasRamseyColoring (ramseyNumber k s - 1) k (s - 1)
      from ⟨G, hfreeSmall⟩)
  have hstrict := ramseyNumber_strictMono_right
    (k := k) (s := s - 1) hk (by omega)
  have hspred : s - 1 + 1 = s := by omega
  rw [hspred] at hstrict
  have hpos := ramseyNumber_pos (by omega : 0 < k) (by omega : 0 < s)
  omega

/-- The least forcing order also forces every larger finite vertex type,
not only its canonical `Fin` representative. -/
theorem ramseyNumber_forcesCard (k s : ℕ) :
    ForcesRamseyCard.{u} (ramseyNumber k s) k s := by
  classical
  intro V _ hcard G hG
  let f : Fin (ramseyNumber k s) ↪ V :=
    (Fin.castLEEmb hcard).trans
      (Fintype.equivFin V).symm.toEmbedding
  let H : SimpleGraph (Fin (ramseyNumber k s)) := G.comap f
  have hH : IsRamseyFree H k s := by
    constructor
    · exact hG.1.comap
        (SimpleGraph.Embedding.comap f G).isContained
    · have hcompl : Hᶜ = Gᶜ.comap f := by
        ext x y
        simp [H, SimpleGraph.compl_adj]
      rw [hcompl]
      exact hG.2.comap
        (SimpleGraph.Embedding.comap f Gᶜ).isContained
  exact ramseyNumber_forces k s H hH

end RamseyIncrement
