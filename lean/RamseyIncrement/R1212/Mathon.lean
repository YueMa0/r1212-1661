/-
R(12,12) ≥ 1642: the Mathon graph `M(797)` is an `(11,11)`-coloring.
-/
import RamseyIncrement.R1212.Paley
import RamseyIncrement.Basic

/-!
# The Mathon graph `M(797)`

Vertices `A_x`, `B_x` (`x ∈ ZMod 797`), `a`, `b`.  Red: `A_x A_y` and `B_x B_y`
when `x - y` is a nonzero square; `A_x B_y` when `x ≠ y` and `x - y` is not a
square; `a` to all of `A`, `b` to all of `B`.

Every monochromatic clique through a vertex `v` maps into `P₇₉₇` by an explicit
map (the neighbourhood lemma of Shearer and Mathon):

* red, `v = A_c` or `B_c`: `A_x ↦ 1/(x - c)`, `B_y ↦ 1/(y - c)`, `a, b ↦ 0`;
* red, `v = a` or `b`: `A_x ↦ x`, `B_y ↦ y`;
* blue: twice these maps (`2` is not a square), after discarding the one vertex
  `B_c` (resp. `A_c`, `b`, `a`) that is blue to `v` and red to the rest of the
  blue neighborhood.

So `ω(M(797)) ≤ 1 + ω(P₇₉₇)` and `α(M(797)) ≤ 1 + ω(P₇₉₇)`.
-/

namespace RamseyIncrement
namespace R1212

/-- Vertices of `M(797)`. -/
abbrev MV := F ⊕ F ⊕ Bool

namespace MV
abbrev A (x : F) : MV := Sum.inl x
abbrev B (x : F) : MV := Sum.inr (Sum.inl x)
abbrev a : MV := Sum.inr (Sum.inr false)
abbrev b : MV := Sum.inr (Sum.inr true)
end MV

open MV

theorem isSquare_iff (x : F) : IsSquare x ↔ x = 0 ∨ QR x := by
  constructor
  · intro h
    by_cases hx : x = 0
    · exact Or.inl hx
    · exact Or.inr ⟨hx, h⟩
  · rintro (rfl | h)
    · exact ⟨0, by ring⟩
    · exact h.2

instance : DecidablePred (IsSquare : F → Prop) := fun x ↦
  decidable_of_iff _ (isSquare_iff x).symm

/-- The red relation of `M(797)`. -/
def mathonAdj : MV → MV → Prop
  | .inl x, .inl y => QR (x - y)
  | .inr (.inl x), .inr (.inl y) => QR (x - y)
  | .inl x, .inr (.inl y) => x ≠ y ∧ ¬IsSquare (x - y)
  | .inr (.inl y), .inl x => x ≠ y ∧ ¬IsSquare (x - y)
  | .inl _, .inr (.inr false) => True
  | .inr (.inr false), .inl _ => True
  | .inr (.inl _), .inr (.inr true) => True
  | .inr (.inr true), .inr (.inl _) => True
  | _, _ => False

/-- The Mathon graph `M(797)`; red edges are graph edges. -/
def mathon : SimpleGraph MV where
  Adj := mathonAdj
  symm := ⟨fun u v h ↦ by
    rcases u with x | x | c <;> rcases v with y | y | d <;>
      (try cases c) <;> (try cases d) <;> simp only [mathonAdj] at h ⊢ <;>
      first
      | trivial
      | exact h
      | (have : y - x = -(x - y) := by ring
         rw [this]; exact QR.neg h)⟩
  loopless := ⟨fun v h ↦ by
    rcases v with x | x | c
    · exact (h : QR (x - x)).1 (sub_self x)
    · exact (h : QR (x - x)).1 (sub_self x)
    · cases c <;> exact h⟩

/-- Kernel-reducible decision procedure for the red relation (no casts). -/
instance mathonDecAdj : DecidableRel mathon.Adj := fun u v ↦
  match u, v with
  | .inl x, .inl y => (inferInstance : Decidable (QR (x - y)))
  | .inr (.inl x), .inr (.inl y) => (inferInstance : Decidable (QR (x - y)))
  | .inl x, .inr (.inl y) => (inferInstance : Decidable (x ≠ y ∧ ¬IsSquare (x - y)))
  | .inr (.inl y), .inl x => (inferInstance : Decidable (x ≠ y ∧ ¬IsSquare (x - y)))
  | .inl _, .inr (.inr false) => isTrue trivial
  | .inr (.inr false), .inl _ => isTrue trivial
  | .inr (.inl _), .inr (.inr true) => isTrue trivial
  | .inr (.inr true), .inr (.inl _) => isTrue trivial
  | .inl _, .inr (.inr true) => isFalse id
  | .inr (.inr true), .inl _ => isFalse id
  | .inr (.inl _), .inr (.inr false) => isFalse id
  | .inr (.inr false), .inr (.inl _) => isFalse id
  | .inr (.inr false), .inr (.inr false) => isFalse id
  | .inr (.inr false), .inr (.inr true) => isFalse id
  | .inr (.inr true), .inr (.inr false) => isFalse id
  | .inr (.inr true), .inr (.inr true) => isFalse id

@[simp] theorem adj_AA (x y : F) : mathon.Adj (A x) (A y) ↔ QR (x - y) := Iff.rfl
@[simp] theorem adj_BB (x y : F) : mathon.Adj (B x) (B y) ↔ QR (x - y) := Iff.rfl
@[simp] theorem adj_AB (x y : F) : mathon.Adj (A x) (B y) ↔ x ≠ y ∧ ¬IsSquare (x - y) :=
  Iff.rfl
@[simp] theorem adj_BA (y x : F) : mathon.Adj (B y) (A x) ↔ x ≠ y ∧ ¬IsSquare (x - y) :=
  Iff.rfl
@[simp] theorem adj_Aa (x : F) : mathon.Adj (A x) a := trivial
@[simp] theorem adj_aA (x : F) : mathon.Adj a (A x) := trivial
@[simp] theorem adj_Bb (x : F) : mathon.Adj (B x) b := trivial
@[simp] theorem adj_bB (x : F) : mathon.Adj b (B x) := trivial
@[simp] theorem not_adj_Ab (x : F) : ¬mathon.Adj (A x) b := id
@[simp] theorem not_adj_bA (x : F) : ¬mathon.Adj b (A x) := id
@[simp] theorem not_adj_Ba (x : F) : ¬mathon.Adj (B x) a := id
@[simp] theorem not_adj_aB (x : F) : ¬mathon.Adj a (B x) := id
@[simp] theorem not_adj_ab : ¬mathon.Adj a b := id
@[simp] theorem not_adj_ba : ¬mathon.Adj b a := id

theorem card_MV : Fintype.card MV = 1596 := by simp

/-! ## Maps into `P₇₉₇` -/

/-- `A_x ↦ 1/(x - c)`, `B_y ↦ 1/(y - c)`, `a, b ↦ 0`. -/
def phi (c : F) : MV → F
  | .inl x => (x - c)⁻¹
  | .inr (.inl y) => (y - c)⁻¹
  | _ => 0

/-- `A_x ↦ x`, `B_y ↦ y`, `a, b ↦ 0`. -/
def lab : MV → F
  | .inl x => x
  | .inr (.inl y) => y
  | _ => 0

@[simp] theorem phi_A (c x : F) : phi c (A x) = (x - c)⁻¹ := rfl
@[simp] theorem phi_B (c y : F) : phi c (B y) = (y - c)⁻¹ := rfl
@[simp] theorem phi_a (c : F) : phi c a = 0 := rfl
@[simp] theorem phi_b (c : F) : phi c b = 0 := rfl
@[simp] theorem lab_A (x : F) : lab (A x) = x := rfl
@[simp] theorem lab_B (y : F) : lab (B y) = y := rfl

theorem inv_sub_inv' {u v : F} (hu : u ≠ 0) (hv : v ≠ 0) :
    u⁻¹ - v⁻¹ = (v - u) * (u * v)⁻¹ := by
  field_simp

theorem two_mul_inv_sub {u v : F} (hu : u ≠ 0) (hv : v ≠ 0) :
    2 * u⁻¹ - 2 * v⁻¹ = 2 * ((v - u) * (u * v)⁻¹) := by
  rw [← inv_sub_inv' hu hv]
  ring

theorem nsq_of_not_QR {x : F} (h0 : x ≠ 0) (h : ¬QR x) : ¬IsSquare x := fun hs ↦ h ⟨h0, hs⟩

theorem QR_of_isSquare {x : F} (h0 : x ≠ 0) (h : IsSquare x) : QR x := ⟨h0, h⟩

theorem sub_ne_zero' {x y : F} (h : x ≠ y) : x - y ≠ 0 := sub_ne_zero.2 h

theorem nsq_sub_comm {x y : F} (h : ¬IsSquare (x - y)) : ¬IsSquare (y - x) := by
  have : y - x = -(x - y) := by ring
  rw [this]
  exact nsq_neg h

theorem QR_sub_comm {x y : F} (h : QR (x - y)) : QR (y - x) := by
  have : y - x = -(x - y) := by ring
  rw [this]
  exact h.neg

/-! ## Red cliques

Each case reads its facts off the hypotheses by definitional unfolding, and a
single `first` list closes whichever case it is. -/

theorem red_pair_A {c : F} {w w' : MV} (hw : mathon.Adj w (A c)) (hw' : mathon.Adj w' (A c))
    (h : mathon.Adj w w') : paley.Adj (phi c w) (phi c w') := by
  rw [paley_adj]
  rcases w with x | y | e <;> rcases w' with x' | y' | e' <;> (try cases e) <;> (try cases e') <;>
  first
  | exact absurd h (not_adj_Ab _)
  | exact absurd h (not_adj_Ba _)
  | exact absurd h (not_adj_aB _)
  | exact absurd h not_adj_ab
  | exact absurd h not_adj_ba
  | exact absurd hw (not_adj_bA c)
  | exact absurd hw' (not_adj_bA c)
  | exact absurd h (mathon.loopless.irrefl _)
  | -- A x, A x'
    (have hx : QR (x - c) := hw
     have hx' : QR (x' - c) := hw'
     have hxx : QR (x - x') := h
     show QR ((x - c)⁻¹ - (x' - c)⁻¹)
     rw [inv_sub_inv' hx.1 hx'.1, show x' - c - (x - c) = x' - x by ring]
     exact (QR_sub_comm hxx).mul (hx.mul hx').inv)
  | -- A x, B y'
    (have hx : QR (x - c) := hw
     have hy : c ≠ y' ∧ ¬IsSquare (c - y') := hw'
     have hxy : x ≠ y' ∧ ¬IsSquare (x - y') := h
     show QR ((x - c)⁻¹ - (y' - c)⁻¹)
     rw [inv_sub_inv' hx.1 (sub_ne_zero' (Ne.symm hy.1)), show y' - c - (x - c) = y' - x by ring]
     exact nsq_mul_nsq (nsq_sub_comm hxy.2) (nsq_inv (hx.mul_nsq (nsq_sub_comm hy.2))))
  | -- B y, A x'
    (have hy : c ≠ y ∧ ¬IsSquare (c - y) := hw
     have hx : QR (x' - c) := hw'
     have hxy : x' ≠ y ∧ ¬IsSquare (x' - y) := h
     show QR ((y - c)⁻¹ - (x' - c)⁻¹)
     rw [inv_sub_inv' (sub_ne_zero' (Ne.symm hy.1)) hx.1, show x' - c - (y - c) = x' - y by ring]
     exact nsq_mul_nsq hxy.2 (nsq_inv (nsq_mul_QR (nsq_sub_comm hy.2) hx)))
  | -- B y, B y'
    (have hy : c ≠ y ∧ ¬IsSquare (c - y) := hw
     have hy' : c ≠ y' ∧ ¬IsSquare (c - y') := hw'
     have hyy : QR (y - y') := h
     show QR ((y - c)⁻¹ - (y' - c)⁻¹)
     rw [inv_sub_inv' (sub_ne_zero' (Ne.symm hy.1)) (sub_ne_zero' (Ne.symm hy'.1)),
       show y' - c - (y - c) = y' - y by ring]
     exact (QR_sub_comm hyy).mul (nsq_mul_nsq (nsq_sub_comm hy.2) (nsq_sub_comm hy'.2)).inv)
  | -- A x, a
    (have hx : QR (x - c) := hw
     show QR ((x - c)⁻¹ - 0)
     rw [sub_zero]
     exact hx.inv)
  | -- a, A x'
    (have hx : QR (x' - c) := hw'
     show QR (0 - (x' - c)⁻¹)
     rw [zero_sub]
     exact hx.inv.neg)

theorem red_pair_B {c : F} {w w' : MV} (hw : mathon.Adj w (B c)) (hw' : mathon.Adj w' (B c))
    (h : mathon.Adj w w') : paley.Adj (phi c w) (phi c w') := by
  rw [paley_adj]
  rcases w with x | y | e <;> rcases w' with x' | y' | e' <;> (try cases e) <;> (try cases e') <;>
  first
  | exact absurd h (not_adj_Ab _)
  | exact absurd h (not_adj_Ba _)
  | exact absurd h (not_adj_bA _)
  | exact absurd h not_adj_ab
  | exact absurd h not_adj_ba
  | exact absurd hw (not_adj_aB c)
  | exact absurd hw' (not_adj_aB c)
  | exact absurd h (mathon.loopless.irrefl _)
  | -- A x, A x'
    (have hx : x ≠ c ∧ ¬IsSquare (x - c) := hw
     have hx' : x' ≠ c ∧ ¬IsSquare (x' - c) := hw'
     have hxx : QR (x - x') := h
     show QR ((x - c)⁻¹ - (x' - c)⁻¹)
     rw [inv_sub_inv' (sub_ne_zero' hx.1) (sub_ne_zero' hx'.1), show x' - c - (x - c) = x' - x by ring]
     exact (QR_sub_comm hxx).mul (nsq_mul_nsq hx.2 hx'.2).inv)
  | -- A x, B y'
    (have hx : x ≠ c ∧ ¬IsSquare (x - c) := hw
     have hy : QR (y' - c) := hw'
     have hxy : x ≠ y' ∧ ¬IsSquare (x - y') := h
     show QR ((x - c)⁻¹ - (y' - c)⁻¹)
     rw [inv_sub_inv' (sub_ne_zero' hx.1) hy.1, show y' - c - (x - c) = y' - x by ring]
     exact nsq_mul_nsq (nsq_sub_comm hxy.2) (nsq_inv (nsq_mul_QR hx.2 hy)))
  | -- B y, A x'
    (have hy : QR (y - c) := hw
     have hx : x' ≠ c ∧ ¬IsSquare (x' - c) := hw'
     have hxy : x' ≠ y ∧ ¬IsSquare (x' - y) := h
     show QR ((y - c)⁻¹ - (x' - c)⁻¹)
     rw [inv_sub_inv' hy.1 (sub_ne_zero' hx.1), show x' - c - (y - c) = x' - y by ring]
     exact nsq_mul_nsq hxy.2 (nsq_inv (hy.mul_nsq hx.2)))
  | -- B y, B y'
    (have hy : QR (y - c) := hw
     have hy' : QR (y' - c) := hw'
     have hyy : QR (y - y') := h
     show QR ((y - c)⁻¹ - (y' - c)⁻¹)
     rw [inv_sub_inv' hy.1 hy'.1, show y' - c - (y - c) = y' - y by ring]
     exact (QR_sub_comm hyy).mul (hy.mul hy').inv)
  | -- B y, b
    (have hy : QR (y - c) := hw
     show QR ((y - c)⁻¹ - 0)
     rw [sub_zero]
     exact hy.inv)
  | -- b, B y'
    (have hy : QR (y' - c) := hw'
     show QR (0 - (y' - c)⁻¹)
     rw [zero_sub]
     exact hy.inv.neg)

theorem red_pair_a {w w' : MV} (hw : mathon.Adj w a) (hw' : mathon.Adj w' a)
    (h : mathon.Adj w w') : paley.Adj (lab w) (lab w') := by
  rcases w with x | y | e <;> rcases w' with x' | y' | e' <;> (try cases e) <;> (try cases e') <;>
  first
  | exact absurd hw (not_adj_Ba _)
  | exact absurd hw' (not_adj_Ba _)
  | exact absurd hw not_adj_ba
  | exact absurd hw' not_adj_ba
  | exact absurd hw (mathon.loopless.irrefl _)
  | exact absurd hw' (mathon.loopless.irrefl _)
  | (have hxx : QR (x - x') := h
     exact hxx)

theorem red_pair_b {w w' : MV} (hw : mathon.Adj w b) (hw' : mathon.Adj w' b)
    (h : mathon.Adj w w') : paley.Adj (lab w) (lab w') := by
  rcases w with x | y | e <;> rcases w' with x' | y' | e' <;> (try cases e) <;> (try cases e') <;>
  first
  | exact absurd hw (not_adj_Ab _)
  | exact absurd hw' (not_adj_Ab _)
  | exact absurd hw not_adj_ab
  | exact absurd hw' not_adj_ab
  | exact absurd hw (mathon.loopless.irrefl _)
  | exact absurd hw' (mathon.loopless.irrefl _)
  | (have hyy : QR (y - y') := h
     exact hyy)

/-! ## Blue cliques -/

theorem compl_adj' {u v : MV} : mathonᶜ.Adj u v ↔ u ≠ v ∧ ¬mathon.Adj u v :=
  SimpleGraph.compl_adj mathon u v

theorem A_ne {x y : F} (h : A x ≠ A y) : x ≠ y := fun e ↦ h (by rw [e])
theorem B_ne {x y : F} (h : B x ≠ B y) : x ≠ y := fun e ↦ h (by rw [e])

/-- From "not red and distinct" to "nonzero non-square". -/
theorem nsq_of_blue {x : F} (h0 : x ≠ 0) (h : ¬QR x) : ¬IsSquare x := nsq_of_not_QR h0 h

/-- From "not (`u ≠ v` and non-square)" and `u ≠ v`, a nonzero square. -/
theorem QR_of_not_red {x y : F} (hxy : x ≠ y) (h : ¬(x ≠ y ∧ ¬IsSquare (x - y))) :
    QR (x - y) :=
  ⟨sub_ne_zero' hxy, by by_contra hs; exact h ⟨hxy, hs⟩⟩

theorem blue_pair_A {c : F} {w w' : MV} (hw : mathonᶜ.Adj w (A c)) (hw' : mathonᶜ.Adj w' (A c))
    (hwB : w ≠ B c) (hwB' : w' ≠ B c) (h : mathonᶜ.Adj w w') :
    paley.Adj (2 * phi c w) (2 * phi c w') := by
  rw [paley_adj]
  have hw₁ := compl_adj'.1 hw
  have hw₂ := compl_adj'.1 hw'
  have h₁ := compl_adj'.1 h
  rcases w with x | y | e <;> rcases w' with x' | y' | e' <;> (try cases e) <;> (try cases e') <;>
  first
  | exact absurd (adj_aA c) hw₁.2
  | exact absurd (adj_aA c) hw₂.2
  | exact absurd (adj_Bb _) h₁.2
  | exact absurd (adj_bB _) h₁.2
  | exact absurd rfl h₁.1
  | -- A x, A x'
    (have hx := nsq_of_blue (sub_ne_zero' (A_ne hw₁.1)) (hw₁.2 : ¬QR (x - c))
     have hx' := nsq_of_blue (sub_ne_zero' (A_ne hw₂.1)) (hw₂.2 : ¬QR (x' - c))
     have hxx := nsq_of_blue (sub_ne_zero' (A_ne h₁.1)) (h₁.2 : ¬QR (x - x'))
     show QR (2 * (x - c)⁻¹ - 2 * (x' - c)⁻¹)
     rw [two_mul_inv_sub (sub_ne_zero' (A_ne hw₁.1)) (sub_ne_zero' (A_ne hw₂.1)),
       show x' - c - (x - c) = x' - x by ring]
     exact nsq_mul_nsq nsq_two (nsq_mul_QR (nsq_sub_comm hxx) (nsq_mul_nsq hx hx').inv))
  | -- A x, B y'
    (have hx := nsq_of_blue (sub_ne_zero' (A_ne hw₁.1)) (hw₁.2 : ¬QR (x - c))
     have hy : QR (y' - c) := QR_sub_comm (QR_of_not_red (Ne.symm (B_ne hwB'))
       (hw₂.2 : ¬(c ≠ y' ∧ ¬IsSquare (c - y'))))
     have hxy : x ≠ y' := fun e ↦ hx (by rw [e]; exact hy.2)
     have hq := QR_of_not_red hxy (h₁.2 : ¬(x ≠ y' ∧ ¬IsSquare (x - y')))
     show QR (2 * (x - c)⁻¹ - 2 * (y' - c)⁻¹)
     rw [two_mul_inv_sub (sub_ne_zero' (A_ne hw₁.1)) hy.1, show y' - c - (x - c) = y' - x by ring]
     exact nsq_mul_nsq nsq_two ((QR_sub_comm hq).mul_nsq (nsq_inv (nsq_mul_QR hx hy))))
  | -- B y, A x'
    (have hx := nsq_of_blue (sub_ne_zero' (A_ne hw₂.1)) (hw₂.2 : ¬QR (x' - c))
     have hy : QR (y - c) := QR_sub_comm (QR_of_not_red (Ne.symm (B_ne hwB))
       (hw₁.2 : ¬(c ≠ y ∧ ¬IsSquare (c - y))))
     have hxy : x' ≠ y := fun e ↦ hx (by rw [e]; exact hy.2)
     have hq := QR_of_not_red hxy (h₁.2 : ¬(x' ≠ y ∧ ¬IsSquare (x' - y)))
     show QR (2 * (y - c)⁻¹ - 2 * (x' - c)⁻¹)
     rw [two_mul_inv_sub hy.1 (sub_ne_zero' (A_ne hw₂.1)), show x' - c - (y - c) = x' - y by ring]
     exact nsq_mul_nsq nsq_two (hq.mul_nsq (nsq_inv (hy.mul_nsq hx))))
  | -- B y, B y'
    (have hy : QR (y - c) := QR_sub_comm (QR_of_not_red (Ne.symm (B_ne hwB))
       (hw₁.2 : ¬(c ≠ y ∧ ¬IsSquare (c - y))))
     have hy' : QR (y' - c) := QR_sub_comm (QR_of_not_red (Ne.symm (B_ne hwB'))
       (hw₂.2 : ¬(c ≠ y' ∧ ¬IsSquare (c - y'))))
     have hyy := nsq_of_blue (sub_ne_zero' (B_ne h₁.1)) (h₁.2 : ¬QR (y - y'))
     show QR (2 * (y - c)⁻¹ - 2 * (y' - c)⁻¹)
     rw [two_mul_inv_sub hy.1 hy'.1, show y' - c - (y - c) = y' - y by ring]
     exact nsq_mul_nsq nsq_two (nsq_mul_QR (nsq_sub_comm hyy) (hy.mul hy').inv))
  | -- A x, b
    (have hx := nsq_of_blue (sub_ne_zero' (A_ne hw₁.1)) (hw₁.2 : ¬QR (x - c))
     show QR (2 * (x - c)⁻¹ - 2 * 0)
     rw [mul_zero, sub_zero]
     exact nsq_mul_nsq nsq_two (nsq_inv hx))
  | -- b, A x'
    (have hx := nsq_of_blue (sub_ne_zero' (A_ne hw₂.1)) (hw₂.2 : ¬QR (x' - c))
     show QR (2 * 0 - 2 * (x' - c)⁻¹)
     rw [mul_zero, zero_sub]
     exact (nsq_mul_nsq nsq_two (nsq_inv hx)).neg)

theorem blue_pair_B {c : F} {w w' : MV} (hw : mathonᶜ.Adj w (B c)) (hw' : mathonᶜ.Adj w' (B c))
    (hwA : w ≠ A c) (hwA' : w' ≠ A c) (h : mathonᶜ.Adj w w') :
    paley.Adj (2 * phi c w) (2 * phi c w') := by
  rw [paley_adj]
  have hw₁ := compl_adj'.1 hw
  have hw₂ := compl_adj'.1 hw'
  have h₁ := compl_adj'.1 h
  rcases w with x | y | e <;> rcases w' with x' | y' | e' <;> (try cases e) <;> (try cases e') <;>
  first
  | exact absurd (adj_bB c) hw₁.2
  | exact absurd (adj_bB c) hw₂.2
  | exact absurd (adj_Aa _) h₁.2
  | exact absurd (adj_aA _) h₁.2
  | exact absurd rfl h₁.1
  | -- A x, A x'
    (have hx : QR (x - c) := QR_of_not_red (A_ne hwA) (hw₁.2 : ¬(x ≠ c ∧ ¬IsSquare (x - c)))
     have hx' : QR (x' - c) := QR_of_not_red (A_ne hwA') (hw₂.2 : ¬(x' ≠ c ∧ ¬IsSquare (x' - c)))
     have hxx := nsq_of_blue (sub_ne_zero' (A_ne h₁.1)) (h₁.2 : ¬QR (x - x'))
     show QR (2 * (x - c)⁻¹ - 2 * (x' - c)⁻¹)
     rw [two_mul_inv_sub hx.1 hx'.1, show x' - c - (x - c) = x' - x by ring]
     exact nsq_mul_nsq nsq_two (nsq_mul_QR (nsq_sub_comm hxx) (hx.mul hx').inv))
  | -- A x, B y'
    (have hx : QR (x - c) := QR_of_not_red (A_ne hwA) (hw₁.2 : ¬(x ≠ c ∧ ¬IsSquare (x - c)))
     have hy := nsq_of_blue (sub_ne_zero' (B_ne hw₂.1)) (hw₂.2 : ¬QR (y' - c))
     have hxy : x ≠ y' := fun e ↦ hy (by rw [← e]; exact hx.2)
     have hq := QR_of_not_red hxy (h₁.2 : ¬(x ≠ y' ∧ ¬IsSquare (x - y')))
     show QR (2 * (x - c)⁻¹ - 2 * (y' - c)⁻¹)
     rw [two_mul_inv_sub hx.1 (sub_ne_zero' (B_ne hw₂.1)), show y' - c - (x - c) = y' - x by ring]
     exact nsq_mul_nsq nsq_two ((QR_sub_comm hq).mul_nsq (nsq_inv (hx.mul_nsq hy))))
  | -- B y, A x'
    (have hx : QR (x' - c) := QR_of_not_red (A_ne hwA') (hw₂.2 : ¬(x' ≠ c ∧ ¬IsSquare (x' - c)))
     have hy := nsq_of_blue (sub_ne_zero' (B_ne hw₁.1)) (hw₁.2 : ¬QR (y - c))
     have hxy : x' ≠ y := fun e ↦ hy (by rw [← e]; exact hx.2)
     have hq := QR_of_not_red hxy (h₁.2 : ¬(x' ≠ y ∧ ¬IsSquare (x' - y)))
     show QR (2 * (y - c)⁻¹ - 2 * (x' - c)⁻¹)
     rw [two_mul_inv_sub (sub_ne_zero' (B_ne hw₁.1)) hx.1, show x' - c - (y - c) = x' - y by ring]
     exact nsq_mul_nsq nsq_two (hq.mul_nsq (nsq_inv (nsq_mul_QR hy hx))))
  | -- B y, B y'
    (have hy := nsq_of_blue (sub_ne_zero' (B_ne hw₁.1)) (hw₁.2 : ¬QR (y - c))
     have hy' := nsq_of_blue (sub_ne_zero' (B_ne hw₂.1)) (hw₂.2 : ¬QR (y' - c))
     have hyy := nsq_of_blue (sub_ne_zero' (B_ne h₁.1)) (h₁.2 : ¬QR (y - y'))
     show QR (2 * (y - c)⁻¹ - 2 * (y' - c)⁻¹)
     rw [two_mul_inv_sub (sub_ne_zero' (B_ne hw₁.1)) (sub_ne_zero' (B_ne hw₂.1)),
       show y' - c - (y - c) = y' - y by ring]
     exact nsq_mul_nsq nsq_two (nsq_mul_QR (nsq_sub_comm hyy) (nsq_mul_nsq hy hy').inv))
  | -- B y, a
    (have hy := nsq_of_blue (sub_ne_zero' (B_ne hw₁.1)) (hw₁.2 : ¬QR (y - c))
     show QR (2 * (y - c)⁻¹ - 2 * 0)
     rw [mul_zero, sub_zero]
     exact nsq_mul_nsq nsq_two (nsq_inv hy))
  | -- a, B y'
    (have hy := nsq_of_blue (sub_ne_zero' (B_ne hw₂.1)) (hw₂.2 : ¬QR (y' - c))
     show QR (2 * 0 - 2 * (y' - c)⁻¹)
     rw [mul_zero, zero_sub]
     exact (nsq_mul_nsq nsq_two (nsq_inv hy)).neg)

theorem blue_pair_a {w w' : MV} (hw : mathonᶜ.Adj w a) (hw' : mathonᶜ.Adj w' a)
    (hb : w ≠ b) (hb' : w' ≠ b) (h : mathonᶜ.Adj w w') :
    paley.Adj (2 * lab w) (2 * lab w') := by
  rw [paley_adj]
  have hw₁ := compl_adj'.1 hw
  have hw₂ := compl_adj'.1 hw'
  have h₁ := compl_adj'.1 h
  rcases w with x | y | e <;> rcases w' with x' | y' | e' <;> (try cases e) <;> (try cases e') <;>
  first
  | exact absurd (adj_Aa _) hw₁.2
  | exact absurd (adj_Aa _) hw₂.2
  | exact absurd rfl hw₁.1
  | exact absurd rfl hw₂.1
  | exact absurd rfl hb
  | exact absurd rfl hb'
  | (have hyy := nsq_of_blue (sub_ne_zero' (B_ne h₁.1)) (h₁.2 : ¬QR (y - y'))
     show QR (2 * y - 2 * y')
     rw [show 2 * y - 2 * y' = 2 * (y - y') by ring]
     exact nsq_mul_nsq nsq_two hyy)

theorem blue_pair_b {w w' : MV} (hw : mathonᶜ.Adj w b) (hw' : mathonᶜ.Adj w' b)
    (ha : w ≠ a) (ha' : w' ≠ a) (h : mathonᶜ.Adj w w') :
    paley.Adj (2 * lab w) (2 * lab w') := by
  rw [paley_adj]
  have hw₁ := compl_adj'.1 hw
  have hw₂ := compl_adj'.1 hw'
  have h₁ := compl_adj'.1 h
  rcases w with x | y | e <;> rcases w' with x' | y' | e' <;> (try cases e) <;> (try cases e') <;>
  first
  | exact absurd (adj_Bb _) hw₁.2
  | exact absurd (adj_Bb _) hw₂.2
  | exact absurd rfl hw₁.1
  | exact absurd rfl hw₂.1
  | exact absurd rfl ha
  | exact absurd rfl ha'
  | (have hxx := nsq_of_blue (sub_ne_zero' (A_ne h₁.1)) (h₁.2 : ¬QR (x - x'))
     show QR (2 * x - 2 * x')
     rw [show 2 * x - 2 * x' = 2 * (x - x') by ring]
     exact nsq_mul_nsq nsq_two hxx)

/-! ## The bounds -/

theorem false_of_map {W V : Type*} {H : SimpleGraph W} {G' : SimpleGraph V} {n : ℕ}
    (hfree : G'.CliqueFree n) {t : Finset W} (ht : H.IsNClique n t) (f : W → V)
    (hf : ∀ u ∈ t, ∀ v ∈ t, u ≠ v → G'.Adj (f u) (f v)) : False := by
  classical
  have hinj : Set.InjOn f t := by
    intro u hu v hv huv
    by_contra hne
    exact (hf u hu v hv hne).ne huv
  apply hfree (t.image f)
  refine ⟨?_, ?_⟩
  · intro x hx y hy hxy
    rw [Finset.coe_image] at hx hy
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨v, hv, rfl⟩ := hy
    exact hf u hu v hv (fun h ↦ hxy (h ▸ rfl))
  · rw [Finset.card_image_of_injOn hinj, ht.card_eq]

theorem erase_isNClique {H : SimpleGraph MV} {n : ℕ} {K : Finset MV} (hK : H.IsNClique (n + 1) K)
    {v : MV} (hv : v ∈ K) : H.IsNClique n (K.erase v) :=
  ⟨hK.isClique.subset (Finset.erase_subset v K), by rw [Finset.card_erase_of_mem hv, hK.card_eq]; rfl⟩

/-- **`ω(M(797)) ≤ 10`.** -/
theorem mathon_cliqueFree (hP : paley.CliqueFree 10) : mathon.CliqueFree 11 := by
  classical
  intro K hK
  obtain ⟨v, hv⟩ : K.Nonempty := Finset.card_pos.1 (by rw [hK.card_eq]; norm_num)
  have hK' := erase_isNClique hK hv
  have hadj : ∀ w ∈ K.erase v, mathon.Adj w v := fun w hw ↦
    hK.isClique (Finset.mem_of_mem_erase hw) hv (Finset.ne_of_mem_erase hw)
  rcases v with c | c | e
  · exact false_of_map hP hK' (phi c) fun w hw w' hw' hne ↦
      red_pair_A (hadj w hw) (hadj w' hw') (hK'.isClique hw hw' hne)
  · exact false_of_map hP hK' (phi c) fun w hw w' hw' hne ↦
      red_pair_B (hadj w hw) (hadj w' hw') (hK'.isClique hw hw' hne)
  · cases e
    · exact false_of_map hP hK' lab fun w hw w' hw' hne ↦
        red_pair_a (hadj w hw) (hadj w' hw') (hK'.isClique hw hw' hne)
    · exact false_of_map hP hK' lab fun w hw w' hw' hne ↦
        red_pair_b (hadj w hw) (hadj w' hw') (hK'.isClique hw hw' hne)

/-- If a blue clique contains `v` and its "twin" `t` (blue to `v`, red to the rest of the
blue neighborhood of `v`), it has at most two vertices. -/
theorem card_le_two_of_twin {K : Finset MV} {v t : MV} (hK : mathonᶜ.IsClique (K : Set MV))
    (hv : v ∈ K) (ht : t ∈ K)
    (htwin : ∀ w, mathonᶜ.Adj w v → mathonᶜ.Adj w t → False) : K.card ≤ 2 := by
  classical
  have hsub : K ⊆ {v, t} := by
    intro w hw
    by_contra hnot
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
    exact htwin w (hK hw hv hnot.1) (hK hw ht hnot.2)
  exact (Finset.card_le_card hsub).trans Finset.card_le_two

theorem twin_A (c : F) (w : MV) (h1 : mathonᶜ.Adj w (A c)) (h2 : mathonᶜ.Adj w (B c)) : False := by
  have h₁ := compl_adj'.1 h1
  have h₂ := compl_adj'.1 h2
  rcases w with x | y | e
  · have hxc := A_ne h₁.1
    exact (h₂.2 : ¬(x ≠ c ∧ ¬IsSquare (x - c)))
      ⟨hxc, nsq_of_blue (sub_ne_zero' hxc) (h₁.2 : ¬QR (x - c))⟩
  · have hyc := B_ne h₂.1
    exact (h₂.2 : ¬QR (y - c))
      (QR_sub_comm (QR_of_not_red (Ne.symm hyc) (h₁.2 : ¬(c ≠ y ∧ ¬IsSquare (c - y)))))
  · cases e
    · exact h₁.2 (adj_aA c)
    · exact h₂.2 (adj_bB c)

theorem twin_B (c : F) (w : MV) (h1 : mathonᶜ.Adj w (B c)) (h2 : mathonᶜ.Adj w (A c)) : False := by
  have h₁ := compl_adj'.1 h1
  have h₂ := compl_adj'.1 h2
  rcases w with x | y | e
  · have hxc := A_ne h₂.1
    exact (h₂.2 : ¬QR (x - c)) (QR_of_not_red hxc (h₁.2 : ¬(x ≠ c ∧ ¬IsSquare (x - c))))
  · have hyc := B_ne h₁.1
    exact (h₂.2 : ¬(c ≠ y ∧ ¬IsSquare (c - y)))
      ⟨Ne.symm hyc, nsq_sub_comm (nsq_of_blue (sub_ne_zero' hyc) (h₁.2 : ¬QR (y - c)))⟩
  · cases e
    · exact h₂.2 (adj_aA c)
    · exact h₁.2 (adj_bB c)

theorem twin_a (w : MV) (h1 : mathonᶜ.Adj w a) (h2 : mathonᶜ.Adj w b) : False := by
  have h₁ := compl_adj'.1 h1
  have h₂ := compl_adj'.1 h2
  rcases w with x | y | e
  · exact h₁.2 (adj_Aa x)
  · exact h₂.2 (adj_Bb y)
  · cases e
    · exact h₁.1 rfl
    · exact h₂.1 rfl

/-- **`α(M(797)) ≤ 10`.** -/
theorem mathon_compl_cliqueFree (hP : paley.CliqueFree 10) : mathonᶜ.CliqueFree 11 := by
  classical
  intro K hK
  obtain ⟨v, hv⟩ : K.Nonempty := Finset.card_pos.1 (by rw [hK.card_eq]; norm_num)
  have hK' := erase_isNClique hK hv
  have hadj : ∀ w ∈ K.erase v, mathonᶜ.Adj w v := fun w hw ↦
    hK.isClique (Finset.mem_of_mem_erase hw) hv (Finset.ne_of_mem_erase hw)
  have hsmall : ∀ t ∈ K, (∀ w, mathonᶜ.Adj w v → mathonᶜ.Adj w t → False) → False :=
    fun t ht htw ↦ by
      have := card_le_two_of_twin hK.isClique hv ht htw
      rw [hK.card_eq] at this
      omega
  have hne : ∀ {t}, t ∉ K → ∀ w ∈ K.erase v, w ≠ t := fun ht w hw h ↦
    ht (h ▸ Finset.mem_of_mem_erase hw)
  rcases v with c | c | e
  · by_cases hB : B c ∈ K
    · exact hsmall _ hB (twin_A c)
    · exact false_of_map hP hK' (fun w ↦ 2 * phi c w) fun w hw w' hw' hww ↦
        blue_pair_A (hadj w hw) (hadj w' hw') (hne hB w hw) (hne hB w' hw') (hK'.isClique hw hw' hww)
  · by_cases hA : A c ∈ K
    · exact hsmall _ hA (twin_B c)
    · exact false_of_map hP hK' (fun w ↦ 2 * phi c w) fun w hw w' hw' hww ↦
        blue_pair_B (hadj w hw) (hadj w' hw') (hne hA w hw) (hne hA w' hw') (hK'.isClique hw hw' hww)
  · cases e
    · by_cases hb : b ∈ K
      · exact hsmall _ hb twin_a
      · exact false_of_map hP hK' (fun w ↦ 2 * lab w) fun w hw w' hw' hww ↦
          blue_pair_a (hadj w hw) (hadj w' hw') (hne hb w hw) (hne hb w' hw') (hK'.isClique hw hw' hww)
    · by_cases ha : a ∈ K
      · exact hsmall _ ha (fun w h1 h2 ↦ twin_a w h2 h1)
      · exact false_of_map hP hK' (fun w ↦ 2 * lab w) fun w hw w' hw' hww ↦
          blue_pair_b (hadj w hw) (hadj w' hw') (hne ha w hw) (hne ha w' hw') (hK'.isClique hw hw' hww)

/-- **`M(797)` is an `(11,11)`-coloring**, given `ω(P₇₉₇) ≤ 9`. -/
theorem mathon_isRamseyFree (hP : paley.CliqueFree 10) : IsRamseyFree mathon 11 11 :=
  ⟨mathon_cliqueFree hP, mathon_compl_cliqueFree hP⟩

end R1212
end RamseyIncrement
