/-
R(12,12) ≥ 1642: quadratic residues mod 797 and the Paley graph `P₇₉₇`.
-/
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Tactic.NormNum.Prime

/-!
# The Paley graph `P₇₉₇`

`797` is a prime with `797 ≡ 1 (mod 4)` and `797 ≡ 5 (mod 8)`, so `-1` is a
square and `2` is not.  `x ~ y` in `P₇₉₇` iff `x - y` is a nonzero square.
-/

namespace RamseyIncrement
namespace R1212

instance fact_prime_797 : Fact (Nat.Prime 797) := ⟨by norm_num⟩

/-- The field with `797` elements. -/
abbrev F := ZMod 797

/-- Nonzero squares. -/
def QR (x : F) : Prop := x ≠ 0 ∧ IsSquare x

theorem chi_mul (a b : F) :
    quadraticChar F (a * b) = quadraticChar F a * quadraticChar F b :=
  map_mul (quadraticChar F) a b

theorem chi_eq_one_iff {x : F} : quadraticChar F x = 1 ↔ QR x := by
  constructor
  · intro h
    have hx : x ≠ 0 := by
      rintro rfl
      simp at h
    exact ⟨hx, (quadraticChar_one_iff_isSquare hx).1 h⟩
  · rintro ⟨hx, hs⟩
    exact (quadraticChar_one_iff_isSquare hx).2 hs

theorem chi_eq_neg_one_iff {x : F} : quadraticChar F x = -1 ↔ ¬IsSquare x :=
  quadraticChar_neg_one_iff_not_isSquare

theorem ne_zero_of_not_isSquare {x : F} (h : ¬IsSquare x) : x ≠ 0 := by
  rintro rfl
  exact h ⟨0, by ring⟩

theorem QR.mul {a b : F} (ha : QR a) (hb : QR b) : QR (a * b) :=
  ⟨mul_ne_zero ha.1 hb.1, ha.2.mul hb.2⟩

theorem QR.mul_nsq {a b : F} (ha : QR a) (hb : ¬IsSquare b) : ¬IsSquare (a * b) := by
  rw [← chi_eq_neg_one_iff, chi_mul, chi_eq_one_iff.2 ha, chi_eq_neg_one_iff.2 hb, one_mul]

theorem nsq_mul_QR {a b : F} (ha : ¬IsSquare a) (hb : QR b) : ¬IsSquare (a * b) := by
  rw [mul_comm]
  exact hb.mul_nsq ha

theorem nsq_mul_nsq {a b : F} (ha : ¬IsSquare a) (hb : ¬IsSquare b) : QR (a * b) := by
  rw [← chi_eq_one_iff, chi_mul, chi_eq_neg_one_iff.2 ha, chi_eq_neg_one_iff.2 hb]
  norm_num

theorem QR.inv {a : F} (ha : QR a) : QR a⁻¹ :=
  ⟨inv_ne_zero ha.1, ha.2.inv⟩

theorem nsq_inv {a : F} (ha : ¬IsSquare a) : ¬IsSquare a⁻¹ := fun h ↦ ha (by
  simpa using h.inv)

theorem QR_neg_one : QR (-1) :=
  ⟨neg_ne_zero.2 one_ne_zero, ZMod.exists_sq_eq_neg_one_iff.2 (by norm_num)⟩

theorem QR.neg {a : F} (ha : QR a) : QR (-a) := by
  simpa using QR_neg_one.mul ha

theorem nsq_neg {a : F} (ha : ¬IsSquare a) : ¬IsSquare (-a) := by
  simpa using QR_neg_one.mul_nsq ha

theorem nsq_two : ¬IsSquare (2 : F) := fun h ↦ by
  have := (ZMod.exists_sq_eq_two_iff (p := 797) (by norm_num)).1 h
  norm_num at this

theorem trichotomy (a : F) : a = 0 ∨ QR a ∨ ¬IsSquare a := by
  by_cases h0 : a = 0
  · exact Or.inl h0
  · by_cases hs : IsSquare a
    · exact Or.inr (Or.inl ⟨h0, hs⟩)
    · exact Or.inr (Or.inr hs)

/-- Euler's criterion as a cheap test on natural numbers. -/
theorem QR_iff_pow (x : F) : QR x ↔ x.val ≠ 0 ∧ x.val ^ 398 % 797 = 1 := by
  have hval : x ≠ 0 ↔ x.val ≠ 0 := by rw [ne_eq, ne_eq, ZMod.val_eq_zero]
  have hpow : x ^ 398 = 1 ↔ x.val ^ 398 % 797 = 1 := by
    have : x ^ 398 = ((x.val ^ 398 % 797 : ℕ) : F) := by
      rw [ZMod.natCast_mod, Nat.cast_pow, ZMod.natCast_zmod_val]
    rw [this]
    constructor
    · intro h
      have := congrArg ZMod.val h
      rwa [ZMod.val_natCast, Nat.mod_mod, ZMod.val_one] at this
    · intro h
      rw [h, Nat.cast_one]
  constructor
  · rintro ⟨h0, hs⟩
    exact ⟨hval.1 h0, hpow.1 ((ZMod.euler_criterion 797 h0).1 hs)⟩
  · rintro ⟨h0, hp⟩
    have h0' := hval.2 h0
    exact ⟨h0', (ZMod.euler_criterion 797 h0').2 (hpow.2 hp)⟩

instance : DecidablePred QR := fun x ↦ decidable_of_iff _ (QR_iff_pow x).symm

/-- The Paley graph on `ZMod 797`. -/
def paley : SimpleGraph F where
  Adj x y := QR (x - y)
  symm := ⟨fun x y h ↦ by
    have : y - x = -(x - y) := by ring
    rw [this]
    exact QR.neg h⟩
  loopless := ⟨fun x h ↦ h.1 (sub_self x)⟩

instance : DecidableRel paley.Adj := fun x y ↦ (inferInstance : Decidable (QR (x - y)))

theorem paley_adj {x y : F} : paley.Adj x y ↔ QR (x - y) := Iff.rfl

end R1212
end RamseyIncrement
