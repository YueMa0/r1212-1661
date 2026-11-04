/-
R(12,12) ≥ 1642: a verified bitset clique search, evaluated by the kernel.
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Bitwise

/-!
# A verified clique search on bitsets

A graph on `ℕ` is given by `row : ℕ → ℕ`; `j` is adjacent to `i` when
`(row i).testBit j`.  A set of vertices is a natural number read as a bitset.

`noClique row t P = true` means: `P` contains no `t`-clique.  At each node the
search colours `P` greedily with `t` classes; a clique has at most one vertex
in each class, so it suffices to branch on the vertices `B` left uncoloured,
removing each branch vertex before the next (MCQ-style).  Fuel exhaustion only
ever makes the answer `false`, so no termination argument is needed.

`noClique_sound` is the only thing the kernel computation relies on.
-/

namespace RamseyIncrement
namespace R1212
namespace Search

variable (row : ℕ → ℕ)

/-- Grow `S` greedily from the top bits of `Q`, removing each chosen vertex and
its neighbours from `Q`. -/
def greedy : ℕ → ℕ → ℕ → ℕ
  | 0, _, S => S
  | f + 1, Q, S =>
      if Q == 0 then S else
        greedy f (Q ^^^ (Q &&& (row Q.log2 ||| 2 ^ Q.log2))) (S ||| 2 ^ Q.log2)

/-- The union of `c` greedy colour classes of `U`. -/
def colourUnion : ℕ → ℕ → ℕ → ℕ
  | 0, _, L => L
  | c + 1, U, L =>
      let S := greedy row 256 U 0
      colourUnion c (U ^^^ S) (L ||| S)

/-- Run `sub` on `R ∩ N(v)` for the bits `v` of `B`, top bit first, removing
each `v` from `R` and `B` afterwards. -/
def loopBits (sub : ℕ → Bool) : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => false
  | f + 1, R, B =>
      if B == 0 then true else
        sub (R &&& row B.log2) &&
          loopBits sub f (R ^^^ (R &&& 2 ^ B.log2)) (B ^^^ 2 ^ B.log2)

/-- `noClique row t P = true` means that `P` has no `t`-clique. -/
def noClique : ℕ → ℕ → Bool
  | 0, _ => false
  | t + 1, P =>
      if P == 0 then true else
        let L := colourUnion row t P 0
        let B := P ^^^ (P &&& L)
        if B == 0 then true else loopBits row (noClique t) 256 P B

/-! ## Soundness -/

/-- `K` is a clique of the row graph. -/
def IsClique (K : Finset ℕ) : Prop :=
  ∀ u ∈ K, ∀ v ∈ K, u ≠ v → (row u).testBit v = true

/-- No two distinct vertices of `S` are adjacent in both directions. -/
def Indep (S : ℕ) : Prop :=
  ∀ u w, S.testBit u = true → S.testBit w = true → u ≠ w →
    ¬((row u).testBit w = true ∧ (row w).testBit u = true)

theorem testBit_clear (Q M i : ℕ) :
    (Q ^^^ (Q &&& M)).testBit i = (Q.testBit i && !M.testBit i) := by
  simp only [Nat.testBit_xor, Nat.testBit_and]
  cases Q.testBit i <;> cases M.testBit i <;> rfl

theorem testBit_two_pow_self (v : ℕ) : (2 ^ v).testBit v = true := by
  simp [Nat.testBit_two_pow]

theorem testBit_two_pow_ne {v i : ℕ} (h : v ≠ i) : (2 ^ v).testBit i = false := by
  simp [Nat.testBit_two_pow, h]

theorem eq_zero_of_beq {Q : ℕ} (h : (Q == 0) = true) : Q = 0 := by simpa using h

theorem ne_zero_of_beq {Q : ℕ} (h : ¬(Q == 0) = true) : Q ≠ 0 := by simpa using h

theorem testBit_of_zero {Q i : ℕ} (h : Q = 0) : Q.testBit i = false := by
  subst h
  simp

/-- `greedy` keeps an independent set independent and only adds bits of `Q`. -/
theorem greedy_spec : ∀ (f Q S : ℕ), Indep row S →
    (∀ u w, S.testBit u = true → Q.testBit w = true →
      u ≠ w ∧ (row u).testBit w = false) →
    Indep row (greedy row f Q S) ∧
      ∀ i, (greedy row f Q S).testBit i = true → S.testBit i = true ∨ Q.testBit i = true
  | 0, Q, S, hS, _ => ⟨hS, fun i h ↦ Or.inl h⟩
  | f + 1, Q, S, hS, hSQ => by
    unfold greedy
    split
    · exact ⟨hS, fun i h ↦ Or.inl h⟩
    · rename_i hQ
      have hQ0 := ne_zero_of_beq hQ
      set v := Q.log2 with hv
      have hvQ : Q.testBit v = true := Nat.testBit_log2 hQ0
      have hS' : Indep row (S ||| 2 ^ v) := by
        intro u w hu hw huw
        simp only [Nat.testBit_or, Bool.or_eq_true] at hu hw
        rcases hu with hu | hu <;> rcases hw with hw | hw
        · exact hS u w hu hw huw
        · have hwv : w = v := by
            by_contra h
            rw [testBit_two_pow_ne (Ne.symm h)] at hw
            exact absurd hw (by simp)
          subst hwv
          rintro ⟨h, -⟩
          rw [(hSQ u _ hu hvQ).2] at h
          exact absurd h (by simp)
        · have huv : u = v := by
            by_contra h
            rw [testBit_two_pow_ne (Ne.symm h)] at hu
            exact absurd hu (by simp)
          subst huv
          rintro ⟨-, h⟩
          rw [(hSQ w _ hw hvQ).2] at h
          exact absurd h (by simp)
        · have huv : u = v := by
            by_contra h
            rw [testBit_two_pow_ne (Ne.symm h)] at hu
            exact absurd hu (by simp)
          have hwv : w = v := by
            by_contra h
            rw [testBit_two_pow_ne (Ne.symm h)] at hw
            exact absurd hw (by simp)
          exact absurd (huv.trans hwv.symm) huw
      have hSQ' : ∀ u w, (S ||| 2 ^ v).testBit u = true →
          (Q ^^^ (Q &&& (row v ||| 2 ^ v))).testBit w = true →
          u ≠ w ∧ (row u).testBit w = false := by
        intro u w hu hw
        rw [testBit_clear] at hw
        simp only [Nat.testBit_or, Bool.and_eq_true, Bool.not_eq_true',
          Bool.or_eq_false_iff] at hw
        obtain ⟨hwQ, hwr, hwv⟩ := hw
        simp only [Nat.testBit_or, Bool.or_eq_true] at hu
        rcases hu with hu | hu
        · exact hSQ u w hu hwQ
        · have huv : u = v := by
            by_contra h
            rw [testBit_two_pow_ne (Ne.symm h)] at hu
            exact absurd hu (by simp)
          subst huv
          refine ⟨fun h ↦ ?_, hwr⟩
          subst h
          rw [testBit_two_pow_self] at hwv
          exact absurd hwv (by simp)
      obtain ⟨hI, hsub⟩ := greedy_spec f _ _ hS' hSQ'
      refine ⟨hI, fun i hi ↦ ?_⟩
      rcases hsub i hi with h | h
      · simp only [Nat.testBit_or, Bool.or_eq_true] at h
        rcases h with h | h
        · exact Or.inl h
        · have hiv : i = v := by
            by_contra hne
            rw [testBit_two_pow_ne (Ne.symm hne)] at h
            exact absurd h (by simp)
          subst hiv
          exact Or.inr hvQ
      · rw [testBit_clear] at h
        simp only [Bool.and_eq_true] at h
        exact Or.inr h.1

/-- A clique has at most one vertex in an independent set. -/
theorem card_filter_le_one {S : ℕ} (hS : Indep row S) {K : Finset ℕ} (hK : IsClique row K) :
    (K.filter fun v ↦ S.testBit v = true).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro u hu w hw
  rw [Finset.mem_filter] at hu hw
  by_contra huw
  exact hS u w hu.2 hw.2 huw ⟨hK u hu.1 w hw.1 huw, hK w hw.1 u hu.1 (Ne.symm huw)⟩

/-- A clique has at most `c` vertices in `c` greedy classes. -/
theorem colourUnion_spec : ∀ (c U L : ℕ) (K : Finset ℕ), IsClique row K →
    (K.filter fun v ↦ (colourUnion row c U L).testBit v = true).card ≤
      c + (K.filter fun v ↦ L.testBit v = true).card
  | 0, U, L, K, _ => by simp [colourUnion]
  | c + 1, U, L, K, hK => by
    rw [colourUnion]
    try dsimp only
    set S := greedy row 256 U 0
    have hS : Indep row S := (greedy_spec row 256 U 0 (by intro u w hu; simp at hu)
      (by intro u w hu; simp at hu)).1
    have ih := colourUnion_spec c (U ^^^ S) (L ||| S) K hK
    have hsplit : (K.filter fun v ↦ (L ||| S).testBit v = true).card ≤
        (K.filter fun v ↦ L.testBit v = true).card +
          (K.filter fun v ↦ S.testBit v = true).card := by
      rw [← Finset.card_union_add_card_inter]
      apply le_trans _ (Nat.le_add_right _ _)
      apply Finset.card_le_card
      intro v hv
      rw [Finset.mem_filter, Nat.testBit_or, Bool.or_eq_true] at hv
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      rcases hv.2 with h | h
      · exact Or.inl ⟨hv.1, h⟩
      · exact Or.inr ⟨hv.1, h⟩
    have h1 := card_filter_le_one row hS hK
    omega

/-- `loopBits` succeeds only if every clique of `R` meeting `B` has a vertex `v`
with `sub (R' ∩ N(v))` true for some `R' ⊇ K`. -/
theorem loopBits_sound (sub : ℕ → Bool) : ∀ (f R B : ℕ), loopBits row sub f R B = true →
    ∀ K : Finset ℕ, (∀ v ∈ K, R.testBit v = true) → (∃ v ∈ K, B.testBit v = true) →
      ∃ v ∈ K, ∃ R', (∀ w ∈ K, R'.testBit w = true) ∧ sub (R' &&& row v) = true
  | 0, R, B, h, _, _, _ => by simp [loopBits] at h
  | f + 1, R, B, h, K, hKR, hKB => by
    unfold loopBits at h
    split at h
    · rename_i hB
      obtain ⟨v, -, hv⟩ := hKB
      rw [testBit_of_zero (eq_zero_of_beq hB)] at hv
      exact absurd hv (by simp)
    · rw [Bool.and_eq_true] at h
      obtain ⟨hsub, hrest⟩ := h
      by_cases htop : B.log2 ∈ K
      · exact ⟨_, htop, R, hKR, hsub⟩
      · apply loopBits_sound sub f _ _ hrest K
        · intro w hw
          have hne : B.log2 ≠ w := fun e ↦ htop (e ▸ hw)
          rw [testBit_clear, testBit_two_pow_ne hne, hKR w hw]
          rfl
        · obtain ⟨v, hvK, hvB⟩ := hKB
          refine ⟨v, hvK, ?_⟩
          have hne : B.log2 ≠ v := fun e ↦ htop (e ▸ hvK)
          rw [Nat.testBit_xor, hvB, testBit_two_pow_ne hne]
          rfl

/-- **Soundness**: if `noClique row t P = true`, every clique inside `P` has
fewer than `t` vertices. -/
theorem noClique_sound : ∀ (t P : ℕ), noClique row t P = true →
    ∀ K : Finset ℕ, IsClique row K → (∀ v ∈ K, P.testBit v = true) → K.card < t
  | 0, P, h, _, _, _ => by simp [noClique] at h
  | t + 1, P, h, K, hK, hKP => by
    unfold noClique at h
    split at h
    · rename_i hP
      have : K = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro v hv
        have := hKP v hv
        rw [testBit_of_zero (eq_zero_of_beq hP)] at this
        exact absurd this (by simp)
      subst this
      simp
    · simp only at h
      set L := colourUnion row t P 0 with hL
      have hcol := colourUnion_spec row t P 0 K hK
      simp only [Nat.zero_testBit, Bool.false_eq_true, Finset.filter_false,
        Finset.card_empty, add_zero] at hcol
      -- vertices of `K` outside `B` are coloured
      have hKL : ∀ v ∈ K, (P ^^^ (P &&& L)).testBit v = false → L.testBit v = true := by
        intro v hv hB
        rw [testBit_clear, hKP v hv] at hB
        simpa using hB
      split at h
      · rename_i hB
        have hall : K.filter (fun v ↦ L.testBit v = true) = K := by
          apply Finset.filter_true_of_mem
          intro v hv
          exact hKL v hv (testBit_of_zero (eq_zero_of_beq hB))
        rw [hall] at hcol
        omega
      · by_cases hmeet : ∃ v ∈ K, (P ^^^ (P &&& L)).testBit v = true
        · obtain ⟨v, hvK, R', hR', hsub⟩ :=
            loopBits_sound row (noClique row t) 256 P _ h K hKP hmeet
          have hrest : (K.erase v).card < t := by
            apply noClique_sound t _ hsub (K.erase v)
            · intro a ha b hb hab
              exact hK a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb) hab
            · intro w hw
              rw [Nat.testBit_and, hR' w (Finset.mem_of_mem_erase hw),
                hK v hvK w (Finset.mem_of_mem_erase hw) (Finset.ne_of_mem_erase hw).symm]
              rfl
          have := Finset.card_erase_add_one hvK
          omega
        · push Not at hmeet
          have hall : K.filter (fun v ↦ L.testBit v = true) = K := by
            apply Finset.filter_true_of_mem
            intro v hv
            exact hKL v hv (by simpa using hmeet v hv)
          rw [hall] at hcol
          omega

/-! ## Splitting the top level into separately checked branches -/

/-- The arguments `R ∩ N(v)` that `loopBits` passes to `sub`. -/
def branchArgs : ℕ → ℕ → ℕ → List ℕ
  | 0, _, _ => []
  | f + 1, R, B =>
      if B == 0 then [] else
        (R &&& row B.log2) :: branchArgs f (R ^^^ (R &&& 2 ^ B.log2)) (B ^^^ 2 ^ B.log2)

theorem loopBits_of_forall (sub : ℕ → Bool) : ∀ (f R B : ℕ),
    loopBits row (fun _ ↦ true) f R B = true →
    (∀ x ∈ branchArgs row f R B, sub x = true) → loopBits row sub f R B = true
  | 0, R, B, h, _ => by simp [loopBits] at h
  | f + 1, R, B, h, hall => by
    unfold loopBits at h ⊢
    unfold branchArgs at hall
    split
    · rfl
    · rename_i hB
      rw [if_neg hB] at h hall
      simp only [Bool.true_and] at h
      rw [Bool.and_eq_true]
      exact ⟨hall _ (List.mem_cons_self ..),
        loopBits_of_forall sub f _ _ h (fun x hx ↦ hall x (List.mem_cons_of_mem _ hx))⟩

/-- `noClique row (t + 1) P` from the separately checked branches of its top
level. -/
theorem noClique_succ_of (t P : ℕ)
    (hloop : loopBits row (fun _ ↦ true) 256 P (P ^^^ (P &&& colourUnion row t P 0)) = true)
    (hall : ∀ x ∈ branchArgs row 256 P (P ^^^ (P &&& colourUnion row t P 0)),
      noClique row t x = true) :
    noClique row (t + 1) P = true := by
  unfold noClique
  split
  · rfl
  · simp only
    split
    · rfl
    · exact loopBits_of_forall row (noClique row t) 256 P _ hloop hall

end Search
end R1212
end RamseyIncrement
