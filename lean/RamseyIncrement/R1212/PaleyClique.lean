/-
R(12,12) ≥ 1642: `ω(P₇₉₇) ≤ 9`.
-/
import RamseyIncrement.R1212.Paley
import RamseyIncrement.R1212.H01NoK8

/-!
# `P₇₉₇` has no `K₁₀`

`x ↦ (x - u) / (v - u)` preserves adjacency when `v - u` is a nonzero square,
and sends `u, v` to `0, 1`.  So a `K₁₀` through `u, v` would give a `K₈` in the
common neighborhood of `0` and `1`, which `h01_noK8` excludes.
-/

namespace RamseyIncrement
namespace R1212

theorem val_lt (x : F) : x.val < 797 := ZMod.val_lt x

theorem qrB_iff {d : ℕ} (hd : d < 797) : qrB d = true ↔ QR (d : F) := by
  rw [QR_iff_pow, ZMod.val_natCast_of_lt hd]
  simp [qrB]

theorem natCast_sub_eq {a b : ℕ} (hb : b < 797) :
    ((a : F) - (b : F)) = (((a + 797 - b) % 797 : ℕ) : F) := by
  rw [ZMod.natCast_mod, Nat.cast_sub (by omega), Nat.cast_add, ZMod.natCast_self, add_zero]

theorem adj_vtx {i j : ℕ} (hi : i < 198) (hj : j < 198) (hij : i ≠ j) :
    paley.Adj (vtx i : F) (vtx j : F) ↔ (rowH i).testBit j = true := by
  rw [rowH_spec i hi j hj, paley_adj, natCast_sub_eq (vtx_lt j hj)]
  rw [← qrB_iff (Nat.mod_lt _ (by norm_num))]
  simp [hij]

theorem mem_H01 {w : F} (h0 : paley.Adj w 0) (h1 : paley.Adj w 1) :
    idx w.val < 198 ∧ ((vtx (idx w.val) : ℕ) : F) = w := by
  have hw0 : qrB w.val = true := by
    rw [qrB_iff (val_lt w), ZMod.natCast_zmod_val]
    simpa [paley_adj] using h0
  have hw1 : qrB ((w.val + 796) % 797) = true := by
    rw [qrB_iff (Nat.mod_lt _ (by norm_num))]
    have := natCast_sub_eq (a := w.val) (b := 1) (by norm_num)
    rw [Nat.cast_one, ZMod.natCast_zmod_val] at this
    rw [show w.val + 796 = w.val + 797 - 1 by omega, ← this]
    simpa [paley_adj] using h1
  obtain ⟨hlt, heq⟩ := idx_spec w.val (val_lt w) hw0 hw1
  exact ⟨hlt, by rw [heq, ZMod.natCast_zmod_val]⟩

theorem fullH_testBit (i : ℕ) : fullH.testBit i = decide (i < 198) :=
  Nat.testBit_two_pow_sub_one 198 i

/-- **`ω(P₇₉₇) ≤ 9`.** -/
theorem paley_cliqueFree : paley.CliqueFree 10 := by
  classical
  intro K hK
  obtain ⟨u, hu, v, hv, huv⟩ : ∃ u ∈ K, ∃ v ∈ K, u ≠ v := by
    have : 1 < K.card := by rw [hK.card_eq]; norm_num
    exact Finset.one_lt_card.1 this
  have hd : QR (v - u) := hK.isClique hv hu huv.symm
  set d := v - u with hd_def
  have hd0 : d ≠ 0 := hd.1
  let f : F → F := fun x ↦ (x - u) * d⁻¹
  have hfadj : ∀ x ∈ K, ∀ y ∈ K, x ≠ y → paley.Adj (f x) (f y) := by
    intro x hx y hy hxy
    have hxy' : QR (x - y) := hK.isClique hx hy hxy
    have : f x - f y = (x - y) * d⁻¹ := by simp only [f]; ring
    rw [paley_adj, this]
    exact hxy'.mul hd.inv
  have hfu : f u = 0 := by simp [f]
  have hfv : f v = 1 := by simp only [f]; rw [← hd_def]; exact mul_inv_cancel₀ hd0
  set K' := (K.erase u).erase v with hK'
  have hK'mem : ∀ x ∈ K', x ∈ K ∧ x ≠ u ∧ x ≠ v := by
    intro x hx
    rw [hK', Finset.mem_erase, Finset.mem_erase] at hx
    exact ⟨hx.2.2, hx.2.1, hx.1⟩
  have hK'card : K'.card = 8 := by
    rw [hK', Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨huv.symm, hv⟩),
      Finset.card_erase_of_mem hu, hK.card_eq]
  have hH : ∀ x ∈ K', idx (f x).val < 198 ∧ ((vtx (idx (f x).val) : ℕ) : F) = f x := by
    intro x hx
    obtain ⟨hxK, hxu, hxv⟩ := hK'mem x hx
    apply mem_H01
    · rw [← hfu]; exact hfadj x hxK u hu hxu
    · rw [← hfv]; exact hfadj x hxK v hv hxv
  let g : F → ℕ := fun x ↦ idx (f x).val
  have hginj : Set.InjOn g K' := by
    intro x hx y hy hxy
    have h1 := (hH x hx).2
    have h2 := (hH y hy).2
    simp only [g] at hxy
    rw [hxy] at h1
    have hfxy : f x = f y := h1.symm.trans h2
    simp only [f] at hfxy
    have := mul_right_cancel₀ (inv_ne_zero hd0) hfxy
    exact sub_left_injective this
  set T := K'.image g
  have hTcard : T.card = 8 := by rw [Finset.card_image_of_injOn hginj, hK'card]
  have hTclique : Search.IsClique rowH T := by
    intro i hi j hj hij
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hi
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hj
    have hxy : x ≠ y := fun h ↦ hij (by rw [h])
    rw [← adj_vtx (hH x hx).1 (hH y hy).1 hij, (hH x hx).2, (hH y hy).2]
    exact hfadj x (hK'mem x hx).1 y (hK'mem y hy).1 hxy
  have hTsub : ∀ i ∈ T, fullH.testBit i = true := by
    intro i hi
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hi
    rw [fullH_testBit]
    simpa using (hH x hx).1
  have := Search.noClique_sound rowH 8 fullH h01_noK8 T hTclique hTsub
  omega

end R1212
end RamseyIncrement
