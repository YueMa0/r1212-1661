import RamseyIncrement.Basic
import Mathlib.Tactic

/-!
# The special Xu--Shao--Radziszowski lift

This file formalizes the first construction in Section 2 of `PROOF.md`.
The input graph records the red edges.  Given an indexed red clique
`c : Fin (k - 1) ↪ V`, the construction adds two indexed families `A`
and `B`, each of cardinality `k - 1`.

The adjacency relation is defined directly on a tagged vertex type.  It
does not model the construction as a sequence of edge updates.
-/

namespace RamseyIncrement

open SimpleGraph

/-- Vertices of the special lift: the old core, the `A` family, and the
`B` family. -/
inductive SpecialLiftVertex (V : Type*) (k : ℕ)
  | core : V → SpecialLiftVertex V k
  | a : Fin (k - 1) → SpecialLiftVertex V k
  | b : Fin (k - 1) → SpecialLiftVertex V k
  deriving DecidableEq, Fintype

namespace SpecialLiftVertex

/-- The tagged vertex type is equivalent to the corresponding nested
disjoint union.  This is used only for cardinal arithmetic. -/
def sumEquiv {V : Type*} {k : ℕ} :
    SpecialLiftVertex V k ≃ V ⊕ (Fin (k - 1) ⊕ Fin (k - 1)) where
  toFun
    | core v => Sum.inl v
    | a p => Sum.inr (Sum.inl p)
    | b p => Sum.inr (Sum.inr p)
  invFun
    | Sum.inl v => core v
    | Sum.inr (Sum.inl p) => a p
    | Sum.inr (Sum.inr p) => b p
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with (v | p | p) <;> rfl

theorem card [Fintype V] :
    Fintype.card (SpecialLiftVertex V k) =
      Fintype.card V + 2 * (k - 1) := by
  rw [Fintype.card_congr sumEquiv]
  simp
  omega

theorem card_eq_add_two_mul_sub_two [Fintype V] (hk : 1 ≤ k) :
    Fintype.card (SpecialLiftVertex V k) =
      Fintype.card V + 2 * k - 2 := by
  rw [card]
  omega

end SpecialLiftVertex

/-- The two red components in `B`: indices `0,1`, and indices at least
`2`. -/
def SameBPart {k : ℕ} (p q : Fin (k - 1)) : Prop :=
  (p.1 < 2 ∧ q.1 < 2) ∨ (2 ≤ p.1 ∧ 2 ≤ q.1)

theorem sameBPart_comm {k : ℕ} {p q : Fin (k - 1)} :
    SameBPart p q ↔ SameBPart q p := by
  simp only [SameBPart]
  aesop

/-- An oriented presentation of the red edges.  `SimpleGraph.fromRel`
below symmetrizes this relation and removes loops. -/
def specialLiftRel {V : Type*} {k : ℕ} (G : SimpleGraph V)
    (c : Fin (k - 1) ↪ V) :
    SpecialLiftVertex V k → SpecialLiftVertex V k → Prop
  | .core v, .core w => G.Adj v w
  | .a p, .a q => p ≠ q
  | .b p, .b q => p ≠ q ∧ SameBPart p q
  | .a p, .core v => c p = v
  | .b p, .core v => v ≠ c p ∧ G.Adj (c p) v
  | .a p, .b q => p ≠ q
  | _, _ => False

/-- The special lift of `G` along the indexed red clique `c`. -/
def specialLift {V : Type*} {k : ℕ} (G : SimpleGraph V)
    (c : Fin (k - 1) ↪ V) : SimpleGraph (SpecialLiftVertex V k) :=
  SimpleGraph.fromRel (specialLiftRel G c)

section Adjacency

variable {V : Type*} {k : ℕ} (G : SimpleGraph V)
  (c : Fin (k - 1) ↪ V)

@[simp]
theorem specialLift_adj_core_core (v w : V) :
    (specialLift G c).Adj (.core v) (.core w) ↔ G.Adj v w := by
  simp only [specialLift, SimpleGraph.fromRel_adj, specialLiftRel]
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · exact G.adj_symm h
  · intro h
    exact ⟨by simpa using h.ne, Or.inl h⟩

@[simp]
theorem specialLift_adj_a_a (p q : Fin (k - 1)) :
    (specialLift G c).Adj (.a p) (.a q) ↔ p ≠ q := by
  simp [specialLift, specialLiftRel, ne_comm]

@[simp]
theorem specialLift_adj_b_b (p q : Fin (k - 1)) :
    (specialLift G c).Adj (.b p) (.b q) ↔
      p ≠ q ∧ SameBPart p q := by
  simp only [specialLift, SimpleGraph.fromRel_adj, specialLiftRel]
  constructor
  · rintro ⟨hpq', h | h⟩
    · exact ⟨fun hpq => hpq' (by simp [hpq]), h.2⟩
    · exact ⟨fun hpq => hpq' (by simp [hpq]), sameBPart_comm.mp h.2⟩
  · rintro ⟨hpq, hpart⟩
    exact ⟨by simpa, Or.inl ⟨hpq, hpart⟩⟩

@[simp]
theorem specialLift_adj_a_core (p : Fin (k - 1)) (v : V) :
    (specialLift G c).Adj (.a p) (.core v) ↔ c p = v := by
  simp [specialLift, specialLiftRel]

@[simp]
theorem specialLift_adj_core_a (v : V) (p : Fin (k - 1)) :
    (specialLift G c).Adj (.core v) (.a p) ↔ c p = v := by
  rw [(specialLift G c).adj_comm]
  exact specialLift_adj_a_core G c p v

@[simp]
theorem specialLift_adj_b_core (p : Fin (k - 1)) (v : V) :
    (specialLift G c).Adj (.b p) (.core v) ↔
      v ≠ c p ∧ G.Adj (c p) v := by
  simp [specialLift, specialLiftRel, G.adj_comm]

@[simp]
theorem specialLift_adj_core_b (v : V) (p : Fin (k - 1)) :
    (specialLift G c).Adj (.core v) (.b p) ↔
      v ≠ c p ∧ G.Adj (c p) v := by
  rw [(specialLift G c).adj_comm]
  exact specialLift_adj_b_core G c p v

@[simp]
theorem specialLift_adj_a_b (p q : Fin (k - 1)) :
    (specialLift G c).Adj (.a p) (.b q) ↔ p ≠ q := by
  simp [specialLift, specialLiftRel]

@[simp]
theorem specialLift_adj_b_a (q p : Fin (k - 1)) :
    (specialLift G c).Adj (.b q) (.a p) ↔ p ≠ q := by
  rw [(specialLift G c).adj_comm]
  exact specialLift_adj_a_b G c p q

@[simp]
theorem specialLift_compl_adj_core_core (v w : V) :
    (specialLift G c)ᶜ.Adj (.core v) (.core w) ↔ Gᶜ.Adj v w := by
  simp

@[simp]
theorem specialLift_compl_adj_a_a (p q : Fin (k - 1)) :
    (specialLift G c)ᶜ.Adj (.a p) (.a q) ↔ False := by
  simp

@[simp]
theorem specialLift_compl_adj_b_b (p q : Fin (k - 1)) :
    (specialLift G c)ᶜ.Adj (.b p) (.b q) ↔
      p ≠ q ∧ ¬SameBPart p q := by
  by_cases hpq : p = q
  · subst q
    simp
  · simp [compl_adj, hpq]

@[simp]
theorem specialLift_compl_adj_a_core (p : Fin (k - 1)) (v : V) :
    (specialLift G c)ᶜ.Adj (.a p) (.core v) ↔ c p ≠ v := by
  simp

@[simp]
theorem specialLift_compl_adj_core_a (v : V) (p : Fin (k - 1)) :
    (specialLift G c)ᶜ.Adj (.core v) (.a p) ↔ c p ≠ v := by
  rw [(specialLift G c)ᶜ.adj_comm]
  exact specialLift_compl_adj_a_core G c p v

@[simp]
theorem specialLift_compl_adj_b_core (p : Fin (k - 1)) (v : V) :
    (specialLift G c)ᶜ.Adj (.b p) (.core v) ↔
      v = c p ∨ Gᶜ.Adj (c p) v := by
  by_cases h : v = c p
  · subst v
    simp
  · simp [compl_adj, h, ne_comm]

@[simp]
theorem specialLift_compl_adj_core_b (v : V) (p : Fin (k - 1)) :
    (specialLift G c)ᶜ.Adj (.core v) (.b p) ↔
      v = c p ∨ Gᶜ.Adj (c p) v := by
  rw [(specialLift G c)ᶜ.adj_comm]
  exact specialLift_compl_adj_b_core G c p v

@[simp]
theorem specialLift_compl_adj_a_b (p q : Fin (k - 1)) :
    (specialLift G c)ᶜ.Adj (.a p) (.b q) ↔ p = q := by
  simp

@[simp]
theorem specialLift_compl_adj_b_a (q p : Fin (k - 1)) :
    (specialLift G c)ᶜ.Adj (.b q) (.a p) ↔ p = q := by
  rw [(specialLift G c)ᶜ.adj_comm]
  exact specialLift_compl_adj_a_b G c p q

section Certificate

variable (hc : G.IsClique (Set.range c))

@[simp]
theorem specialLift_adj_a_certificate (p q : Fin (k - 1)) :
    (specialLift G c).Adj (.a p) (.core (c q)) ↔ p = q := by
  simp

@[simp]
theorem specialLift_compl_adj_a_certificate (p q : Fin (k - 1)) :
    (specialLift G c)ᶜ.Adj (.a p) (.core (c q)) ↔ p ≠ q := by
  simp

include hc

@[simp]
theorem specialLift_adj_b_certificate (p q : Fin (k - 1)) :
    (specialLift G c).Adj (.b p) (.core (c q)) ↔ p ≠ q := by
  constructor
  · intro h
    have hne := (specialLift_adj_b_core G c p (c q)).mp h |>.1
    intro hpq
    subst q
    exact hne rfl
  · intro hpq
    rw [specialLift_adj_b_core]
    refine ⟨fun h => hpq (c.injective h.symm), ?_⟩
    exact hc (Set.mem_range_self p) (Set.mem_range_self q) (c.injective.ne hpq)

@[simp]
theorem specialLift_compl_adj_b_certificate (p q : Fin (k - 1)) :
    (specialLift G c)ᶜ.Adj (.b p) (.core (c q)) ↔ p = q := by
  rw [compl_adj, specialLift_adj_b_certificate G c hc]
  simp

end Certificate

end Adjacency

section CliqueTools

variable {V : Type*} {k : ℕ}

/-- Core vertices of a finite set in the lift, with their tags removed. -/
abbrev CoreIn (K : Finset (SpecialLiftVertex V k)) :=
  {v : V // SpecialLiftVertex.core v ∈ K}

/-- `A` vertices of a finite set in the lift, with their tags removed. -/
abbrev AIn (K : Finset (SpecialLiftVertex V k)) :=
  {p : Fin (k - 1) // SpecialLiftVertex.a p ∈ K}

/-- `B` vertices of a finite set in the lift, with their tags removed. -/
abbrev BIn (K : Finset (SpecialLiftVertex V k)) :=
  {p : Fin (k - 1) // SpecialLiftVertex.b p ∈ K}

/-- Each tagged part of a finite lifted set is finite even when the
ambient core type is infinite. -/
instance coreInFinite (K : Finset (SpecialLiftVertex V k)) :
    Finite (CoreIn K) :=
  Finite.of_injective
    (fun d : CoreIn K =>
      (⟨.core d.1, d.2⟩ : {x // x ∈ K}))
    (by
      intro d e h
      apply Subtype.ext
      exact SpecialLiftVertex.core.inj (congrArg Subtype.val h))

instance aInFinite (K : Finset (SpecialLiftVertex V k)) :
    Finite (AIn K) :=
  Finite.of_injective
    (fun p : AIn K =>
      (⟨.a p.1, p.2⟩ : {x // x ∈ K}))
    (by
      intro p q h
      apply Subtype.ext
      exact SpecialLiftVertex.a.inj (congrArg Subtype.val h))

instance bInFinite (K : Finset (SpecialLiftVertex V k)) :
    Finite (BIn K) :=
  Finite.of_injective
    (fun p : BIn K =>
      (⟨.b p.1, p.2⟩ : {x // x ∈ K}))
    (by
      intro p q h
      apply Subtype.ext
      exact SpecialLiftVertex.b.inj (congrArg Subtype.val h))

noncomputable instance coreInFintype (K : Finset (SpecialLiftVertex V k)) :
    Fintype (CoreIn K) :=
  Fintype.ofFinite _

noncomputable instance aInFintype (K : Finset (SpecialLiftVertex V k)) :
    Fintype (AIn K) :=
  Fintype.ofFinite _

noncomputable instance bInFintype (K : Finset (SpecialLiftVertex V k)) :
    Fintype (BIn K) :=
  Fintype.ofFinite _

/-- Partition a finite set of lifted vertices into its three tagged
families. -/
def liftSetEquiv (K : Finset (SpecialLiftVertex V k)) :
    {x // x ∈ K} ≃ CoreIn K ⊕ (AIn K ⊕ BIn K) where
  toFun x :=
    match x.1, x.2 with
    | .core v, hv => Sum.inl ⟨v, hv⟩
    | .a p, hp => Sum.inr (Sum.inl ⟨p, hp⟩)
    | .b p, hp => Sum.inr (Sum.inr ⟨p, hp⟩)
  invFun
    | Sum.inl v => ⟨.core v.1, v.2⟩
    | Sum.inr (Sum.inl p) => ⟨.a p.1, p.2⟩
    | Sum.inr (Sum.inr p) => ⟨.b p.1, p.2⟩
  left_inv x := by rcases x with ⟨x, hx⟩; cases x <;> rfl
  right_inv x := by rcases x with (v | p | p) <;> rfl

theorem card_eq_card_core_add_card_a_add_card_b
    (K : Finset (SpecialLiftVertex V k)) :
    K.card =
      Fintype.card (CoreIn K) + Fintype.card (AIn K) +
        Fintype.card (BIn K) := by
  classical
  rw [← Fintype.card_coe K, Fintype.card_congr (liftSetEquiv K)]
  simp
  omega

/-- A finite clique in a clique-free graph has strictly fewer vertices
than the forbidden order.  The clique may be presented by any embedding
of a finite indexing type. -/
theorem card_lt_of_cliqueFree_of_embedding {W : Type*} [Fintype W]
    {G : SimpleGraph V} {n : ℕ} (hfree : G.CliqueFree n)
    (f : W ↪ V)
    (hclique : ∀ x y : W, x ≠ y → G.Adj (f x) (f y)) :
    Fintype.card W < n := by
  classical
  by_contra hnot
  have hn : n ≤ Fintype.card W := Nat.le_of_not_gt hnot
  obtain ⟨t, -, htcard⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset W)) hn
  let u : Finset V := t.map f
  apply hfree u
  refine ⟨?_, by simp [u, htcard]⟩
  intro _ hx _ hy hne
  simp only [u, Finset.coe_map, Set.mem_image] at hx hy
  obtain ⟨x, hx, rfl⟩ := hx
  obtain ⟨y, hy, rfl⟩ := hy
  exact hclique x y (fun hxy => hne (congrArg f hxy))

/-- A red clique among `B` vertices fits in one of the two red
components, whose larger size is `k - 3` when `k ≥ 5`. -/
theorem card_bIn_le_sub_three {K : Finset (SpecialLiftVertex V k)}
    (hk : 5 ≤ k)
    (hpair : ∀ p q : BIn K, p ≠ q → SameBPart p.1 q.1) :
    Fintype.card (BIn K) ≤ k - 3 := by
  classical
  by_cases hempty : IsEmpty (BIn K)
  · have : Fintype.card (BIn K) = 0 := Fintype.card_eq_zero
    omega
  · letI : Nonempty (BIn K) := not_isEmpty_iff.mp hempty
    let q₀ : BIn K := Classical.choice inferInstance
    by_cases hsmall : q₀.1.1 < 2
    · have hall : ∀ q : BIn K, q.1.1 < 2 := by
        intro q
        by_cases hq : q = q₀
        · simpa [hq] using hsmall
        · rcases hpair q q₀ hq with h | h
          · exact h.1
          · omega
      let f : BIn K ↪ Fin 2 :=
        { toFun := fun q => ⟨q.1.1, hall q⟩
          inj' := by
            intro p q hpq
            apply Subtype.ext
            apply Fin.ext
            exact congrArg (fun x : Fin 2 => x.1) hpq }
      have hcard : Fintype.card (BIn K) ≤ 2 := by
        simpa using Fintype.card_le_of_injective f f.injective
      omega
    · have hall : ∀ q : BIn K, 2 ≤ q.1.1 := by
        intro q
        by_cases hq : q = q₀
        · simpa [hq] using Nat.le_of_not_gt hsmall
        · rcases hpair q q₀ hq with h | h
          · omega
          · exact h.1
      let f : BIn K ↪ Fin (k - 3) :=
        { toFun := fun q =>
            ⟨q.1.1 - 2, by
              have hlt := q.1.2
              omega⟩
          inj' := by
            intro p q hpq
            apply Subtype.ext
            apply Fin.ext
            have hv :=
              congrArg (fun x : Fin (k - 3) => x.1) hpq
            dsimp at hv
            have hp := hall p
            have hq := hall q
            omega }
      simpa using Fintype.card_le_of_injective f f.injective

/-- A blue clique contains at most one `B` vertex from each of the two
red components. -/
theorem card_bIn_le_two_of_opposite_parts
    {K : Finset (SpecialLiftVertex V k)}
    (hpair : ∀ p q : BIn K, p ≠ q → ¬SameBPart p.1 q.1) :
    Fintype.card (BIn K) ≤ 2 := by
  classical
  let f : BIn K ↪ Fin 2 :=
    { toFun := fun p => if p.1.1 < 2 then 0 else 1
      inj' := by
        intro p q hpq
        by_contra hpq'
        have hnpart := hpair p q hpq'
        by_cases hp : p.1.1 < 2 <;> by_cases hq : q.1.1 < 2
        · exact hnpart (Or.inl ⟨hp, hq⟩)
        · simp [hp, hq] at hpq
        · simp [hp, hq] at hpq
        · exact hnpart (Or.inr ⟨Nat.le_of_not_gt hp, Nat.le_of_not_gt hq⟩) }
  simpa using Fintype.card_le_of_injective f f.injective

section RedCliques

variable (G : SimpleGraph V) (c : Fin (k - 1) ↪ V)

/-- The red half of the special-lift theorem. -/
theorem specialLift_cliqueFree (hc : G.IsClique (Set.range c))
    (hk : 5 ≤ k) (hred : G.CliqueFree k) :
    (specialLift G c).CliqueFree k := by
  classical
  intro K hK
  have hparts := card_eq_card_core_add_card_a_add_card_b K
  have hcard := hK.card_eq
  have hBpair :
      ∀ p q : BIn K, p ≠ q → SameBPart p.1 q.1 := by
    intro p q hpq
    have hpqv :
        (SpecialLiftVertex.b (V := V) p.1 : SpecialLiftVertex V k) ≠
          SpecialLiftVertex.b (V := V) q.1 := by
      intro heq
      apply hpq
      apply Subtype.ext
      exact SpecialLiftVertex.b.inj heq
    exact (specialLift_adj_b_b G c p.1 q.1).mp
      (hK.isClique p.2 q.2 hpqv) |>.2
  have hBle := card_bIn_le_sub_three hk hBpair
  by_cases hAtwo : 2 ≤ Fintype.card (AIn K)
  · have hApos : 0 < Fintype.card (AIn K) := by omega
    letI : Nonempty (AIn K) := Fintype.card_pos_iff.mp hApos
    let p : AIn K := Classical.choice inferInstance
    obtain ⟨q, hqp⟩ :=
      Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card (AIn K)) p
    have hcoreEmpty : IsEmpty (CoreIn K) := by
      constructor
      intro d
      have hpd :
          (specialLift G c).Adj (.a p.1) (.core d.1) :=
        hK.isClique p.2 d.2 (by simp)
      have hqd :
          (specialLift G c).Adj (.a q.1) (.core d.1) :=
        hK.isClique q.2 d.2 (by simp)
      have hpc : c p.1 = d.1 :=
        (specialLift_adj_a_core G c p.1 d.1).mp hpd
      have hqc : c q.1 = d.1 :=
        (specialLift_adj_a_core G c q.1 d.1).mp hqd
      apply hqp
      apply Subtype.ext
      apply c.injective
      exact hqc.trans hpc.symm
    letI : IsEmpty (CoreIn K) := hcoreEmpty
    have hcorecard : Fintype.card (CoreIn K) = 0 :=
      Fintype.card_eq_zero
    let f : AIn K ⊕ BIn K ↪ Fin (k - 1) :=
      { toFun := fun x =>
          match x with
          | Sum.inl p => p.1
          | Sum.inr q => q.1
        inj' := by
          intro x y hxy
          rcases x with p | q <;> rcases y with p' | q'
          · apply congrArg Sum.inl
            apply Subtype.ext
            exact hxy
          · have hadj :
                (specialLift G c).Adj (.a p.1) (.b q'.1) :=
              hK.isClique p.2 q'.2 (by simp)
            have hne := (specialLift_adj_a_b G c p.1 q'.1).mp hadj
            exact False.elim (hne hxy)
          · have hadj :
                (specialLift G c).Adj (.a p'.1) (.b q.1) :=
              hK.isClique p'.2 q.2 (by simp)
            have hne := (specialLift_adj_a_b G c p'.1 q.1).mp hadj
            exact False.elim (hne hxy.symm)
          · apply congrArg Sum.inr
            apply Subtype.ext
            exact hxy }
    have hAB :
        Fintype.card (AIn K) + Fintype.card (BIn K) ≤ k - 1 := by
      simpa using Fintype.card_le_of_injective f f.injective
    omega
  · have hAle : Fintype.card (AIn K) ≤ 1 := by omega
    by_cases hAzero : Fintype.card (AIn K) = 0
    · have hnoa (p : Fin (k - 1))
          (hp : SpecialLiftVertex.a p ∈ K) : False := by
        have hnonempty : Nonempty (AIn K) := ⟨⟨p, hp⟩⟩
        have hpos : 0 < Fintype.card (AIn K) :=
          Fintype.card_pos_iff.mpr hnonempty
        omega
      let f : {x // x ∈ K} ↪ V :=
        { toFun := fun x =>
            match x.1, x.2 with
            | .core v, _ => v
            | .a p, hp => False.elim (hnoa p hp)
            | .b q, _ => c q
          inj' := by
            rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
            apply Subtype.ext
            cases x with
            | core v =>
                cases y with
                | core w => exact congrArg SpecialLiftVertex.core hxy
                | a p => exact False.elim (hnoa p hy)
                | b q =>
                    have hadj :
                        (specialLift G c).Adj (.core v) (.b q) :=
                      hK.isClique hx hy (by simp)
                    have hne := (specialLift_adj_core_b G c v q).mp hadj |>.1
                    exact False.elim (hne hxy)
            | a p => exact False.elim (hnoa p hx)
            | b p =>
                cases y with
                | core w =>
                    have hadj :
                        (specialLift G c).Adj (.b p) (.core w) :=
                      hK.isClique hx hy (by simp)
                    have hne := (specialLift_adj_b_core G c p w).mp hadj |>.1
                    exact False.elim (hne hxy.symm)
                | a q => exact False.elim (hnoa q hy)
                | b q =>
                    exact congrArg SpecialLiftVertex.b (c.injective hxy) }
      have hfclique : ∀ x y : {x // x ∈ K}, x ≠ y →
          G.Adj (f x) (f y) := by
        rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
        cases x with
        | core v =>
            cases y with
            | core w =>
                exact (specialLift_adj_core_core G c v w).mp
                  (hK.isClique hx hy (by simpa using hxy))
            | a p => exact False.elim (hnoa p hy)
            | b q =>
                change G.Adj v (c q)
                exact G.adj_symm <|
                  (specialLift_adj_core_b G c v q).mp
                    (hK.isClique hx hy (by simp)) |>.2
        | a p => exact False.elim (hnoa p hx)
        | b p =>
            cases y with
            | core w =>
                change G.Adj (c p) w
                exact (specialLift_adj_b_core G c p w).mp
                  (hK.isClique hx hy (by simp)) |>.2
            | a q => exact False.elim (hnoa q hy)
            | b q =>
                change G.Adj (c p) (c q)
                have hpq : p ≠ q := by
                  intro hpq
                  subst q
                  exact hxy rfl
                exact hc (Set.mem_range_self p) (Set.mem_range_self q)
                  (c.injective.ne hpq)
      have hlt :=
        card_lt_of_cliqueFree_of_embedding hred f hfclique
      have : Fintype.card {x // x ∈ K} = K.card := Fintype.card_coe K
      omega
    · have hAone : Fintype.card (AIn K) = 1 := by omega
      have hApos : 0 < Fintype.card (AIn K) := by omega
      letI : Nonempty (AIn K) := Fintype.card_pos_iff.mp hApos
      let p : AIn K := Classical.choice inferInstance
      have hcorele : Fintype.card (CoreIn K) ≤ 1 := by
        rw [Fintype.card_le_one_iff]
        intro d e
        apply Subtype.ext
        have hpd :
            (specialLift G c).Adj (.a p.1) (.core d.1) :=
          hK.isClique p.2 d.2 (by simp)
        have hpe :
            (specialLift G c).Adj (.a p.1) (.core e.1) :=
          hK.isClique p.2 e.2 (by simp)
        exact ((specialLift_adj_a_core G c p.1 d.1).mp hpd).symm.trans
          ((specialLift_adj_a_core G c p.1 e.1).mp hpe)
      omega

end RedCliques

section BlueCliques

variable (G : SimpleGraph V) (c : Fin (k - 1) ↪ V)

/-- The blue half of the special-lift theorem. -/
theorem specialLift_compl_cliqueFree (hc : G.IsClique (Set.range c))
    (hblue : Gᶜ.CliqueFree s) :
    (specialLift G c)ᶜ.CliqueFree (s + 1) := by
  classical
  intro K hK
  have hparts := card_eq_card_core_add_card_a_add_card_b K
  have hcard := hK.card_eq
  have hAle : Fintype.card (AIn K) ≤ 1 := by
    rw [Fintype.card_le_one_iff]
    intro p q
    apply Subtype.ext
    by_contra hpq
    have hpqv :
        (SpecialLiftVertex.a (V := V) p.1 : SpecialLiftVertex V k) ≠
          SpecialLiftVertex.a (V := V) q.1 := by
      intro heq
      exact hpq (SpecialLiftVertex.a.inj heq)
    exact (specialLift_compl_adj_a_a G c p.1 q.1).mp
      (hK.isClique p.2 q.2 hpqv)
  have hBpair :
      ∀ p q : BIn K, p ≠ q → ¬SameBPart p.1 q.1 := by
    intro p q hpq
    have hpqv :
        (SpecialLiftVertex.b (V := V) p.1 : SpecialLiftVertex V k) ≠
          SpecialLiftVertex.b (V := V) q.1 := by
      intro heq
      apply hpq
      apply Subtype.ext
      exact SpecialLiftVertex.b.inj heq
    exact (specialLift_compl_adj_b_b G c p.1 q.1).mp
      (hK.isClique p.2 q.2 hpqv) |>.2
  have hBle : Fintype.card (BIn K) ≤ 2 :=
    card_bIn_le_two_of_opposite_parts hBpair
  have hcoreLt : Fintype.card (CoreIn K) < s := by
    let f : CoreIn K ↪ V :=
      { toFun := Subtype.val
        inj' := Subtype.val_injective }
    have hfclique : ∀ d e : CoreIn K, d ≠ e →
        Gᶜ.Adj (f d) (f e) := by
      intro d e hde
      change Gᶜ.Adj d.1 e.1
      rw [← specialLift_compl_adj_core_core G c]
      exact hK.isClique d.2 e.2 (by
        intro heq
        apply hde
        apply Subtype.ext
        exact SpecialLiftVertex.core.inj heq)
    exact card_lt_of_cliqueFree_of_embedding hblue f hfclique
  have hcoreAdjoinLt (p : Fin (k - 1))
      (hexclude : ∀ d : CoreIn K, d.1 ≠ c p)
      (hadj : ∀ d : CoreIn K, Gᶜ.Adj (c p) d.1) :
      Fintype.card (CoreIn K) + 1 < s := by
    let f : CoreIn K ⊕ Unit ↪ V :=
      { toFun := fun x =>
          match x with
          | Sum.inl d => d.1
          | Sum.inr _ => c p
        inj' := by
          intro x y hxy
          rcases x with d | u <;> rcases y with e | v
          · apply congrArg Sum.inl
            apply Subtype.ext
            exact hxy
          · exact False.elim (hexclude d hxy)
          · exact False.elim (hexclude e hxy.symm)
          · exact congrArg Sum.inr (Subsingleton.elim u v) }
    have hfclique : ∀ x y : CoreIn K ⊕ Unit, x ≠ y →
        Gᶜ.Adj (f x) (f y) := by
      intro x y hxy
      rcases x with d | u <;> rcases y with e | v
      · change Gᶜ.Adj d.1 e.1
        rw [← specialLift_compl_adj_core_core G c]
        exact hK.isClique d.2 e.2 (by
          intro heq
          apply hxy
          apply congrArg Sum.inl
          apply Subtype.ext
          exact SpecialLiftVertex.core.inj heq)
      · change Gᶜ.Adj d.1 (c p)
        exact Gᶜ.adj_symm (hadj d)
      · change Gᶜ.Adj (c p) e.1
        exact hadj e
      · exact False.elim (hxy (congrArg Sum.inr (Subsingleton.elim u v)))
    have hlt := card_lt_of_cliqueFree_of_embedding hblue f hfclique
    simpa using hlt
  by_cases hAzero : Fintype.card (AIn K) = 0
  · by_cases hBone : Fintype.card (BIn K) ≤ 1
    · omega
    · have hBtwo : Fintype.card (BIn K) = 2 := by omega
      have hBpos : 0 < Fintype.card (BIn K) := by omega
      letI : Nonempty (BIn K) := Fintype.card_pos_iff.mp hBpos
      let p : BIn K := Classical.choice inferInstance
      obtain ⟨q, hqp⟩ :=
        Fintype.exists_ne_of_one_lt_card (by omega : 1 < Fintype.card (BIn K)) p
      have hpq : p.1 ≠ q.1 := by
        intro heq
        apply hqp
        exact Subtype.ext heq.symm
      have hexclude : ∀ d : CoreIn K, d.1 ≠ c p.1 := by
        intro d hdc
        have hadjLift :
            (specialLift G c)ᶜ.Adj (.b q.1) (.core d.1) :=
          hK.isClique q.2 d.2 (by simp)
        have hadjCert :
            (specialLift G c)ᶜ.Adj (.b q.1) (.core (c p.1)) := by
          simpa [hdc] using hadjLift
        have heq :=
          (specialLift_compl_adj_b_certificate G c hc q.1 p.1).mp hadjCert
        exact hpq heq.symm
      have hadj : ∀ d : CoreIn K, Gᶜ.Adj (c p.1) d.1 := by
        intro d
        have hlift :
            (specialLift G c)ᶜ.Adj (.b p.1) (.core d.1) :=
          hK.isClique p.2 d.2 (by simp)
        rcases (specialLift_compl_adj_b_core G c p.1 d.1).mp hlift with heq | hadj
        · exact False.elim (hexclude d heq)
        · exact hadj
      have hplus := hcoreAdjoinLt p.1 hexclude hadj
      omega
  · have hAone : Fintype.card (AIn K) = 1 := by omega
    have hApos : 0 < Fintype.card (AIn K) := by omega
    letI : Nonempty (AIn K) := Fintype.card_pos_iff.mp hApos
    let p : AIn K := Classical.choice inferInstance
    have hBsub : ∀ q : BIn K, q.1 = p.1 := by
      intro q
      have hlift :
          (specialLift G c)ᶜ.Adj (.a p.1) (.b q.1) :=
        hK.isClique p.2 q.2 (by simp)
      exact (specialLift_compl_adj_a_b G c p.1 q.1).mp hlift |>.symm
    have hBone : Fintype.card (BIn K) ≤ 1 := by
      rw [Fintype.card_le_one_iff]
      intro q r
      apply Subtype.ext
      exact (hBsub q).trans (hBsub r).symm
    by_cases hBzero : Fintype.card (BIn K) = 0
    · omega
    · have hBpos : 0 < Fintype.card (BIn K) := by omega
      letI : Nonempty (BIn K) := Fintype.card_pos_iff.mp hBpos
      let q : BIn K := Classical.choice inferInstance
      have hqp : q.1 = p.1 := hBsub q
      have hexclude : ∀ d : CoreIn K, d.1 ≠ c p.1 := by
        intro d
        have hlift :
            (specialLift G c)ᶜ.Adj (.a p.1) (.core d.1) :=
          hK.isClique p.2 d.2 (by simp)
        exact (specialLift_compl_adj_a_core G c p.1 d.1).mp hlift |>.symm
      have hadj : ∀ d : CoreIn K, Gᶜ.Adj (c p.1) d.1 := by
        intro d
        have hlift :
            (specialLift G c)ᶜ.Adj (.b q.1) (.core d.1) :=
          hK.isClique q.2 d.2 (by simp)
        rw [hqp] at hlift
        rcases (specialLift_compl_adj_b_core G c p.1 d.1).mp hlift with heq | hadj
        · exact False.elim (hexclude d heq)
        · exact hadj
      have hplus := hcoreAdjoinLt p.1 hexclude hadj
      omega

end BlueCliques

/-- The complete special Xu--Shao--Radziszowski lift: a `(k,s)`-free
graph with an indexed red `K_(k-1)` produces a `(k,s+1)`-free graph. -/
theorem specialLift_isRamseyFree {s : ℕ} (G : SimpleGraph V)
    (c : Fin (k - 1) ↪ V) (hc : G.IsClique (Set.range c))
    (hk : 5 ≤ k) (hG : IsRamseyFree G k s) :
    IsRamseyFree (specialLift G c) k (s + 1) := by
  exact ⟨specialLift_cliqueFree G c hc hk hG.1,
    specialLift_compl_cliqueFree G c hc hG.2⟩

end CliqueTools

end RamseyIncrement
