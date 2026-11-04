/-
R(12,12) ≥ 1661: the 1660-vertex colouring.
-/
import RamseyIncrement.R1212.Mathon
import RamseyIncrement.R1661.Checks

/-!
# The colouring on `V° ⊕ Fin 85`

`Σ_V` is a set of 21 vertices of the Mathon graph `M(797)`: the 20 certificate vertices of
r1212-1642 and `A₆₇₅`.  `V°` is `M(797)` without `Σ_V` (file vertices `0–1574`, in the order of
r1212-1642 with `Σ_V` left out).  The 85 core vertices are `inr f`, `f < 85` (file vertex
`1575 + f`).  Red edges:

* `inl u`, `inl v`: as in `M(797)`;
* `inl u`, `inr f`: as given by the type `vt f` of `f`: a copy of sigma vertex `t`
  (`vt f = t < 21`) is red to `u` iff `sig t` is, a constant vertex is red (`vt f = 21`) or
  blue (`vt f = 22`) to all of `V°`;
* `inr f`, `inr g`: as in the core table `rowR`.

`tools/compare_export_1661.py` checks that this is the colouring of `b1660_PM2.graph`.
-/

namespace RamseyIncrement
namespace R1661

open R1212 R1212.MV

/-- The sigma vertices: the certificates of r1212-1642, `c₀,…,c₉` (a red `K₁₀`) and
`i₀,…,i₉` (a blue `K₁₀`), then `A₆₇₅`, the antipode of `i₆ = B₆₇₅`.  In the file numbering of
`M(797)`: `930, 926, 1573, 1338, 1479, 1483, 1492, 1582, 1586, 1595`,
`1061, 1588, 1576, 1549, 1554, 1594, 1472, 1557, 1079, 1267` and `675`. -/
def sig : Fin 21 → MV :=
  ![B 133, B 129, B 776, B 541, B 682, B 686, B 695, B 785, B 789, b,
    B 264, B 791, B 779, B 752, B 757, a, B 675, B 760, B 282, B 470, A 675]

theorem sig_injective : Function.Injective sig := by decide +kernel

/-- `sig n` for `n < 21` (`b` otherwise; never used). -/
def sigN (n : ℕ) : MV := if h : n < 21 then sig ⟨n, h⟩ else b

theorem sigN_lt {n : ℕ} (h : n < 21) : sigN n = sig ⟨n, h⟩ := dif_pos h

theorem sigN_inj {p q : ℕ} (hp : p < 21) (hq : q < 21) (h : sigN p = sigN q) : p = q := by
  rw [sigN_lt hp, sigN_lt hq] at h
  exact Fin.mk.inj_iff.1 (sig_injective h)

/-- `Σ_V`. -/
def sigSet : Finset MV := Finset.univ.image sig

theorem sigN_mem {p : ℕ} (hp : p < 21) : sigN p ∈ sigSet := by
  rw [sigN_lt hp]
  exact Finset.mem_image_of_mem sig (Finset.mem_univ _)

/-- `V°`: the vertices of `M(797)` outside `Σ_V`. -/
abbrev V0 := {u : MV // u ∉ sigSet}

theorem sigN_ne {p : ℕ} (hp : p < 21) (u : V0) : sigN p ≠ u.1 := fun h ↦ u.2 (h ▸ sigN_mem hp)

theorem card_sigSet : sigSet.card = 21 := by
  rw [sigSet, Finset.card_image_of_injective _ sig_injective, Finset.card_univ, Fintype.card_fin]

theorem card_V0 : Fintype.card V0 = 1575 := by
  show Fintype.card {u : MV // u ∉ sigSet} = 1575
  rw [Fintype.card_subtype_compl, Fintype.card_coe, card_sigSet, card_MV]

/-! ## Antipodes -/

/-- The antipode in `M(797)`: `A_x ↔ B_x`, `a ↔ b`. -/
def antip : MV → MV
  | .inl x => .inr (.inl x)
  | .inr (.inl x) => .inl x
  | .inr (.inr t) => .inr (.inr !t)

theorem QR_iff_isSquare_sub_comm {x y : F} (hxy : x ≠ y) : QR (x - y) ↔ IsSquare (y - x) := by
  refine ⟨fun h ↦ (QR_sub_comm h).2, fun h ↦ ?_⟩
  by_contra hq
  exact nsq_sub_comm (fun hs ↦ hq ⟨sub_ne_zero.2 hxy, hs⟩) h

theorem QR_iff_isSquare {x y : F} (hxy : x ≠ y) : QR (x - y) ↔ IsSquare (x - y) :=
  ⟨fun h ↦ h.2, fun h ↦ ⟨sub_ne_zero.2 hxy, h⟩⟩

/-- **A vertex and its antipode have opposite colours towards every other vertex.** -/
theorem mathon_antip (v u : MV) (h1 : u ≠ v) (h2 : u ≠ antip v) :
    mathon.Adj (antip v) u ↔ ¬mathon.Adj v u := by
  rcases v with x | x | t
  · rcases u with y | y | s
    · have hxy : x ≠ y := fun h ↦ h1 (by subst h; rfl)
      show (y ≠ x ∧ ¬IsSquare (y - x)) ↔ ¬QR (x - y)
      rw [QR_iff_isSquare_sub_comm hxy]
      exact ⟨fun h hs ↦ h.2 hs, fun h ↦ ⟨Ne.symm hxy, h⟩⟩
    · have hxy : x ≠ y := fun h ↦ h2 (by subst h; rfl)
      show QR (x - y) ↔ ¬(x ≠ y ∧ ¬IsSquare (x - y))
      rw [QR_iff_isSquare hxy]
      exact ⟨fun h hn ↦ hn.2 h, fun h ↦ not_not.1 fun hs ↦ h ⟨hxy, hs⟩⟩
    · cases s
      · exact iff_of_false id (not_not.2 trivial)
      · exact iff_of_true trivial id
  · rcases u with y | y | s
    · have hxy : x ≠ y := fun h ↦ h2 (by subst h; rfl)
      show QR (x - y) ↔ ¬(y ≠ x ∧ ¬IsSquare (y - x))
      rw [QR_iff_isSquare_sub_comm hxy]
      exact ⟨fun h hn ↦ hn.2 h, fun h ↦ not_not.1 fun hs ↦ h ⟨Ne.symm hxy, hs⟩⟩
    · have hxy : x ≠ y := fun h ↦ h1 (by subst h; rfl)
      show (x ≠ y ∧ ¬IsSquare (x - y)) ↔ ¬QR (x - y)
      rw [QR_iff_isSquare hxy]
      exact ⟨fun h hs ↦ h.2 hs, fun h ↦ ⟨hxy, h⟩⟩
    · cases s
      · exact iff_of_true trivial id
      · exact iff_of_false id (not_not.2 trivial)
  · cases t <;> rcases u with y | y | s
    · exact iff_of_false id (not_not.2 trivial)
    · exact iff_of_true trivial id
    · cases s
      · exact (h1 rfl).elim
      · exact (h2 rfl).elim
    · exact iff_of_true trivial id
    · exact iff_of_false id (not_not.2 trivial)
    · cases s
      · exact (h2 rfl).elim
      · exact (h1 rfl).elim

/-! ## The colouring -/

/-- Red edges between a core vertex of type `t` and a vertex `u` of `V°`. -/
def typeAdj (t : ℕ) (u : MV) : Prop := if t < 21 then mathon.Adj (sigN t) u else t = 21

instance (t : ℕ) (u : MV) : Decidable (typeAdj t u) :=
  if h : t < 21 then decidable_of_iff (mathon.Adj (sigN t) u) (by simp [typeAdj, h])
  else decidable_of_iff (t = 21) (by simp [typeAdj, h])

/-- The vertices: `V°`, then the 85 core vertices. -/
abbrev W := V0 ⊕ Fin 85

/-- The red relation. -/
def adjW : W → W → Prop
  | .inl u, .inl v => mathon.Adj u.1 v.1
  | .inl u, .inr f => typeAdj (vt f.val) u.1
  | .inr f, .inl u => typeAdj (vt f.val) u.1
  | .inr f, .inr g => f ≠ g ∧ (rowR f.val).testBit g.val = true

/-- The 1660-vertex colouring; red edges are graph edges. -/
def G1660 : SimpleGraph W where
  Adj := adjW
  symm := ⟨fun x y h ↦ by
    rcases x with u | f <;> rcases y with v | g
    · exact SimpleGraph.Adj.symm (G := mathon) h
    · exact h
    · exact h
    · obtain ⟨hfg, hb⟩ := h
      show g ≠ f ∧ (rowR g.val).testBit f.val = true
      exact ⟨Ne.symm hfg, (rowR_symm _ g.isLt _ f.isLt).trans hb⟩⟩
  loopless := ⟨fun x h ↦ by
    rcases x with u | f
    · exact mathon.loopless.irrefl u.1 h
    · obtain ⟨hff, -⟩ := h
      exact hff rfl⟩

instance : DecidableRel G1660.Adj := fun x y ↦
  match x, y with
  | .inl u, .inl v => mathonDecAdj u.1 v.1
  | .inl u, .inr f => (inferInstance : Decidable (typeAdj (vt f.val) u.1))
  | .inr f, .inl u => (inferInstance : Decidable (typeAdj (vt f.val) u.1))
  | .inr f, .inr g =>
      (inferInstance : Decidable (f ≠ g ∧ (rowR f.val).testBit g.val = true))

theorem card_W : Fintype.card W = 1660 := by
  rw [Fintype.card_sum, card_V0, Fintype.card_fin]

/-! ## The definition, read back -/

/-- `M(797)` on `V°` is an induced subgraph. -/
theorem adj_inl_inl (u v : V0) : G1660.Adj (.inl u) (.inl v) ↔ mathon.Adj u.1 v.1 := Iff.rfl

/-- A core vertex that copies sigma vertex `t` has its colour towards `V°`. -/
theorem adj_inr_copy {f : Fin 85} (h21 : vt f.val < 21) (u : V0) :
    G1660.Adj (.inr f) (.inl u) ↔ mathon.Adj (sigN (vt f.val)) u.1 := by
  show typeAdj _ _ ↔ _
  rw [typeAdj, if_pos h21]

/-- Constant vertices towards `V°`. -/
theorem adj_inr_const {f : Fin 85} (c : Bool) (ht : vt f.val = constCode c) (u : V0) :
    G1660.Adj (.inr f) (.inl u) ↔ c = true := by
  show typeAdj _ _ ↔ _
  cases c <;> simp [typeAdj, ht, constCode]

/-- The sigma table is `M(797)` on the sigma vertices. -/
theorem sigR_spec : ∀ p < 21, ∀ q < 21,
    (sigR p).testBit q = decide (mathon.Adj (sigN p) (sigN q)) := by
  decide +kernel

/-- The antipodal table: `j` copies the antipode of the sigma vertex that `i` copies. -/
theorem antiRow_spec : ∀ i < 85, ∀ j < 85,
    (antiRow i).testBit j = (isNC i && isNC j && decide (sigN (vt j) = antip (sigN (vt i)))) := by
  decide +kernel

/-! ## Core positions -/

/-- Core position `j < 85` as a vertex. -/
def coreV (j : ℕ) : W := .inr ⟨j % 85, Nat.mod_lt _ (by norm_num)⟩

/-- The core position of a vertex; `85` for the vertices of `V°`. -/
def idx : W → ℕ
  | .inl _ => 85
  | .inr f => f.val

theorem coreV_val (f : Fin 85) : coreV f.val = .inr f := by
  unfold coreV
  apply congrArg Sum.inr
  apply Fin.ext
  exact Nat.mod_eq_of_lt f.isLt

theorem coreV_lt {j : ℕ} (hj : j < 85) : coreV j = .inr ⟨j, hj⟩ := coreV_val ⟨j, hj⟩

theorem coreV_ne_inl (j : ℕ) (u : V0) : coreV j ≠ .inl u := by simp [coreV]

theorem coreV_idx {x : W} (hx : idx x < 85) : coreV (idx x) = x := by
  rcases x with u | f
  · exact absurd hx (lt_irrefl 85)
  · exact coreV_val f

theorem eq_inl_of_idx {x : W} (hx : ¬idx x < 85) : ∃ u, x = .inl u := by
  rcases x with u | f
  · exact ⟨u, rfl⟩
  · exact absurd f.isLt hx

/-- Between core positions, the colouring is the core table. -/
theorem adj_core {i j : ℕ} (hi : i < 85) (hj : j < 85) (hij : i ≠ j) :
    G1660.Adj (coreV i) (coreV j) ↔ (rowR i).testBit j = true := by
  rw [coreV_lt hi, coreV_lt hj]
  show (⟨i, hi⟩ : Fin 85) ≠ ⟨j, hj⟩ ∧ _ ↔ _
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨fun e ↦ hij (Fin.mk.inj_iff.1 e), h⟩⟩

/-- Towards `V°`, a non-constant core position has the colour of the sigma vertex it copies. -/
theorem adj_out_nc {j : ℕ} (hj : j < 85) (hnc : isNC j = true) (u : V0) :
    G1660.Adj (coreV j) (.inl u) ↔ mathon.Adj (sigN (vt j)) u.1 := by
  rw [coreV_lt hj]
  exact adj_inr_copy (f := ⟨j, hj⟩) (by simpa [isNC] using hnc) u

/-- Towards `V°`, a constant-`c'` core position has colour `c'`. -/
theorem adj_out_const {j : ℕ} (hj : j < 85) (c' : Bool) (hc : vt j = constCode c') (u : V0) :
    G1660.Adj (coreV j) (.inl u) ↔ c' = true := by
  rw [coreV_lt hj]
  exact adj_inr_const (f := ⟨j, hj⟩) c' hc u

end R1661
end RamseyIncrement
