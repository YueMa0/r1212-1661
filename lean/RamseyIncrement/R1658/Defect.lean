/-
R(12,12) ≥ 1658: a clique of the core has at most one defect.
-/
import Mathlib.Data.Finset.Card

/-!
# At most one defect

A finite clique `K` of `adj` may contain "constant" vertices (`cst`) and "conflicts"
(pairs `bad u v`).  Suppose that

1. no two constant vertices are adjacent;
2. no conflict lies in the neighbourhood of a constant vertex;
3. there is no conflict triangle;
4. no conflict lies in the common neighbourhood of another conflict.

Then deleting at most one vertex of `K` leaves no constant vertex and no conflict.
(Constant vertices and the vertex covers of the conflict graph are the defects.  The
conflict graph of `K` has no two disjoint edges and no triangle, so it is a star.)
-/

namespace RamseyIncrement
namespace R1658

theorem defect_le_one {adj : ℕ → ℕ → Prop} {cst : ℕ → Prop} {bad : ℕ → ℕ → Prop} {n : ℕ}
    (bad_symm : ∀ u < n, ∀ v < n, bad u v → bad v u)
    (h1 : ∀ f < n, ∀ g, cst f → adj f g → cst g → False)
    (h2 : ∀ f < n, ∀ u < n, ∀ v, cst f → adj f u → adj f v → bad u v → False)
    (h3 : ∀ u < n, ∀ v < n, ∀ w, bad u v → bad v w → bad u w → False)
    (h4 : ∀ u < n, ∀ v < n, ∀ w < n, ∀ x, bad u v → adj u w → adj v w → adj u x → adj v x →
      bad w x → False)
    (K : Finset ℕ) (hKn : ∀ u ∈ K, u < n) (hK : ∀ u ∈ K, ∀ v ∈ K, u ≠ v → adj u v) :
    ∃ S ⊆ K, K.card ≤ S.card + 1 ∧ (∀ j ∈ S, ¬cst j) ∧
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j → ¬bad i j) := by
  classical
  by_cases hc : ∃ f ∈ K, cst f
  · -- delete the constant vertex
    obtain ⟨f, hfK, hf⟩ := hc
    refine ⟨K.erase f, Finset.erase_subset _ _, ?_, ?_, ?_⟩
    · rw [Finset.card_erase_of_mem hfK]
      omega
    · intro j hj hcj
      exact h1 f (hKn f hfK) j hf
        (hK f hfK j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj).symm) hcj
    · intro i hi j hj _ hb
      exact h2 f (hKn f hfK) i (hKn i (Finset.mem_of_mem_erase hi)) j hf
        (hK f hfK i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi).symm)
        (hK f hfK j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj).symm) hb
  push Not at hc
  by_cases hb : ∃ u ∈ K, ∃ v ∈ K, u ≠ v ∧ bad u v
  swap
  · push Not at hb
    exact ⟨K, subset_refl _, by omega, hc, hb⟩
  obtain ⟨u, huK, v, hvK, huv, hbuv⟩ := hb
  have hu := hKn u huK
  have hv := hKn v hvK
  by_cases hgood : ∀ i ∈ K.erase u, ∀ j ∈ K.erase u, i ≠ j → ¬bad i j
  · -- deleting `u` removes every conflict
    refine ⟨K.erase u, Finset.erase_subset _ _, ?_,
      fun j hj ↦ hc j (Finset.mem_of_mem_erase hj), hgood⟩
    rw [Finset.card_erase_of_mem huK]
    omega
  -- otherwise deleting `v` does
  push Not at hgood
  obtain ⟨i, hi, j, hj, hij, hbij⟩ := hgood
  refine ⟨K.erase v, Finset.erase_subset _ _, ?_,
    fun j hj ↦ hc j (Finset.mem_of_mem_erase hj), ?_⟩
  · rw [Finset.card_erase_of_mem hvK]
    omega
  intro i' hi' j' hj' hij' hbij'
  have hiK := Finset.mem_of_mem_erase hi
  have hjK := Finset.mem_of_mem_erase hj
  have hiu := Finset.ne_of_mem_erase hi
  have hju := Finset.ne_of_mem_erase hj
  have hi'K := Finset.mem_of_mem_erase hi'
  have hj'K := Finset.mem_of_mem_erase hj'
  have hi'v := Finset.ne_of_mem_erase hi'
  have hj'v := Finset.ne_of_mem_erase hj'
  -- the conflict `ij` avoids `u`, so it passes through `v`: a conflict `vw`
  obtain ⟨w, hwK, hwu, hwv, hbvw⟩ : ∃ w ∈ K, w ≠ u ∧ w ≠ v ∧ bad v w := by
    by_cases hiv : i = v
    · refine ⟨j, hjK, hju, fun h ↦ hij (hiv.trans h.symm), ?_⟩
      rw [← hiv]
      exact hbij
    by_cases hjv : j = v
    · refine ⟨i, hiK, hiu, hiv, ?_⟩
      rw [← hjv]
      exact bad_symm i (hKn i hiK) j (hKn j hjK) hbij
    exact (h4 u hu v hv i (hKn i hiK) j hbuv (hK u huK i hiK (Ne.symm hiu))
      (hK v hvK i hiK (Ne.symm hiv)) (hK u huK j hjK (Ne.symm hju))
      (hK v hvK j hjK (Ne.symm hjv)) hbij).elim
  -- the conflict `i'j'` avoids `v`, so it passes through `u`: a conflict `uw'`
  obtain ⟨w', hw'K, hw'u, hw'v, hbuw'⟩ : ∃ w' ∈ K, w' ≠ u ∧ w' ≠ v ∧ bad u w' := by
    by_cases hi'u : i' = u
    · refine ⟨j', hj'K, fun h ↦ hij' (hi'u.trans h.symm), hj'v, ?_⟩
      rw [← hi'u]
      exact hbij'
    by_cases hj'u : j' = u
    · refine ⟨i', hi'K, hi'u, hi'v, ?_⟩
      rw [← hj'u]
      exact bad_symm i' (hKn i' hi'K) j' (hKn j' hj'K) hbij'
    exact (h4 u hu v hv i' (hKn i' hi'K) j' hbuv (hK u huK i' hi'K (Ne.symm hi'u))
      (hK v hvK i' hi'K (Ne.symm hi'v)) (hK u huK j' hj'K (Ne.symm hj'u))
      (hK v hvK j' hj'K (Ne.symm hj'v)) hbij').elim
  by_cases hww : w = w'
  · -- a conflict triangle `u v w`
    rw [← hww] at hbuw'
    exact h3 u hu v hv w hbuv hbvw hbuw'
  · -- two disjoint conflicts `vw`, `uw'`, completely joined
    exact h4 v hv w (hKn w hwK) u hu w' hbvw (hK v hvK u huK (Ne.symm huv)) (hK w hwK u huK hwu)
      (hK v hvK w' hw'K (Ne.symm hw'v)) (hK w hwK w' hw'K hww) hbuw'

end R1658
end RamseyIncrement
