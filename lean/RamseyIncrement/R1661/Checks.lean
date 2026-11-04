/-
R(12,12) ≥ 1661: the finite checks on the 85-vertex core, evaluated by the kernel.
-/
import RamseyIncrement.R1661.Data

/-!
# Finite checks on the core

Colour `c = true` is red, `c = false` is blue.  For a core position `j < 85`:

* `rowC c j`: the `c`-neighbours of `j` in the core;
* `cstMask c`: the core vertices that are constant `c` towards `V°`;
* `vt j < 21`: the sigma vertex that `j` copies on `V°`;
* `sigC c p`: the `c`-neighbours of sigma vertex `p` among the sigma vertices, in `M(797)`;
* `antiRow i`: the non-constant `j` that copy the antipode of the sigma vertex that `i` copies
  (`Graph.lean` proves this);
* `rowA c i`: `rowC c i` without `antiRow i`;
* `badRow c i`: the conflicts of `i`, i.e. the `c`-neighbours `j`, not antipodal to `i`, such
  that `vt i`, `vt j` are equal or not `c`-adjacent in `M(797)`, with `i` and `j` both not
  constant.

`noK12` says that the core has no monochromatic `K₁₂`.  The four checks `check1`–`check4`
say that a `c`-clique of `rowA c` never contains two "defects"; `R1658/Defect.lean` turns
this into "deleting one vertex leaves no defect".  A `c`-clique of the core with no antipodal
pair is a clique of `rowA c`.
-/

namespace RamseyIncrement
namespace R1661

/-- Blue rows of the core: the complement of the red rows. -/
def rowB (i : ℕ) : ℕ := mask85 ^^^ rowR i ^^^ 2 ^ i

/-- The `c`-rows: red for `true`, blue for `false`. -/
def rowC : Bool → ℕ → ℕ
  | true => rowR
  | false => rowB

/-- Blue rows of `M(797)` on the sigma vertices. -/
def sigB (p : ℕ) : ℕ := mask21 ^^^ sigR p ^^^ 2 ^ p

/-- The `c`-rows of `M(797)` on the sigma vertices. -/
def sigC : Bool → ℕ → ℕ
  | true => sigR
  | false => sigB

/-- The type code of a constant-`c` vertex. -/
def constCode : Bool → ℕ
  | true => 21
  | false => 22

/-- The constant-`c` core positions. -/
def cstMask : Bool → ℕ
  | true => cstRLit
  | false => cstBLit

/-- The antipodal rows. -/
def antiRow (i : ℕ) : ℕ := (antiLit >>> (85 * i)) &&& mask85

/-- The `c`-rows without the antipodal pairs. -/
def rowA (c : Bool) (i : ℕ) : ℕ := rowC c i &&& (mask85 ^^^ antiRow i)

/-- The conflict rows. -/
def badRow : Bool → ℕ → ℕ
  | true, i => (badRLit >>> (85 * i)) &&& mask85
  | false, i => (badBLit >>> (85 * i)) &&& mask85

/-- `j` is not constant: a copy of a sigma vertex. -/
def isNC (j : ℕ) : Bool := decide (vt j < 21)

/-- The definition of a conflict. -/
def badB (c : Bool) (i j : ℕ) : Bool :=
  i != j && isNC i && isNC j && (rowC c i).testBit j && !(sigC c (vt i)).testBit (vt j) &&
    !(antiRow i).testBit j

/-- `p i` for all `i < n`. -/
def allLt (n : ℕ) (p : ℕ → Bool) : Bool := (List.range n).all p

/-- No two constant-`c` vertices are `c`-adjacent. -/
def check1 (c : Bool) : Bool :=
  allLt 85 fun f => !(cstMask c).testBit f || (rowA c f &&& cstMask c == 0)

/-- No conflict among the `c`-neighbours of a constant-`c` vertex. -/
def check2 (c : Bool) : Bool :=
  allLt 85 fun f => !(cstMask c).testBit f ||
    allLt 85 fun u => !(rowA c f).testBit u || (badRow c u &&& rowA c f == 0)

/-- No conflict triangle. -/
def check3 (c : Bool) : Bool :=
  allLt 85 fun u => allLt 85 fun v => !(badRow c u).testBit v || (badRow c u &&& badRow c v == 0)

/-- No conflict inside the common `rowA c`-neighbourhood of a conflict. -/
def check4 (c : Bool) : Bool :=
  allLt 85 fun u => allLt 85 fun v => !(badRow c u).testBit v ||
    allLt 85 fun w => !(rowA c u &&& rowA c v).testBit w ||
      (badRow c w &&& (rowA c u &&& rowA c v) == 0)

/-! ## Kernel computations -/

theorem rowR_symm : ∀ i < 85, ∀ j < 85, (rowR i).testBit j = (rowR j).testBit i := by
  decide +kernel

theorem rowR_irrefl : ∀ i < 85, (rowR i).testBit i = false := by decide +kernel

theorem mask85_testBit : ∀ j < 85, mask85.testBit j = true := by decide +kernel

theorem mask21_testBit : ∀ p < 21, mask21.testBit p = true := by decide +kernel

theorem vt_lt : ∀ f < 85, vt f < 23 := by decide +kernel

theorem sigR_irrefl : ∀ p < 21, (sigR p).testBit p = false := by decide +kernel

theorem cstMask_spec : ∀ c : Bool, ∀ j < 85, (cstMask c).testBit j = (vt j == constCode c) := by
  decide +kernel

theorem badRow_spec : ∀ c : Bool, ∀ i < 85, ∀ j < 85, (badRow c i).testBit j = badB c i j := by
  decide +kernel

theorem badRow_symm : ∀ c : Bool, ∀ i < 85, ∀ j < 85,
    (badRow c i).testBit j = (badRow c j).testBit i := by
  decide +kernel

/-- **The core has no monochromatic `K₁₂`.** -/
theorem noK12 : ∀ c : Bool, R1212.Search.noClique (rowC c) 12 mask85 = true := by
  decide +kernel

theorem checks_ok : ∀ c : Bool, (check1 c && check2 c && check3 c && check4 c) = true := by
  decide +kernel

/-! ## Reading the checks -/

theorem allLt_spec {n : ℕ} {p : ℕ → Bool} (h : allLt n p = true) {i : ℕ} (hi : i < n) :
    p i = true :=
  List.all_eq_true.1 h i (List.mem_range.2 hi)

theorem testBit_eq_false_of_and {a b i : ℕ} (h : (a &&& b == 0) = true)
    (hb : b.testBit i = true) : a.testBit i = false := by
  have h0 : a &&& b = 0 := by simpa using h
  have := congrArg (fun x ↦ x.testBit i) h0
  simpa [Nat.testBit_and, hb] using this

variable {c : Bool}

theorem check1_ok (c : Bool) : check1 c = true := by
  have := checks_ok c
  simp only [Bool.and_eq_true] at this
  exact this.1.1.1

theorem check2_ok (c : Bool) : check2 c = true := by
  have := checks_ok c
  simp only [Bool.and_eq_true] at this
  exact this.1.1.2

theorem check3_ok (c : Bool) : check3 c = true := by
  have := checks_ok c
  simp only [Bool.and_eq_true] at this
  exact this.1.2

theorem check4_ok (c : Bool) : check4 c = true := by
  have := checks_ok c
  simp only [Bool.and_eq_true] at this
  exact this.2

theorem h1_of {f g : ℕ} (hf : f < 85) (hcf : (cstMask c).testBit f = true)
    (hfg : (rowA c f).testBit g = true) : (cstMask c).testBit g = false := by
  have h := allLt_spec (check1_ok c) hf
  simp only [hcf, Bool.not_true, Bool.false_or] at h
  have h0 : rowA c f &&& cstMask c = 0 := by simpa using h
  have := congrArg (fun x ↦ x.testBit g) h0
  simpa [Nat.testBit_and, hfg] using this

theorem h2_of {f u v : ℕ} (hf : f < 85) (hu : u < 85) (hcf : (cstMask c).testBit f = true)
    (hfu : (rowA c f).testBit u = true) (hfv : (rowA c f).testBit v = true) :
    (badRow c u).testBit v = false := by
  have h := allLt_spec (check2_ok c) hf
  simp only [hcf, Bool.not_true, Bool.false_or] at h
  have h' := allLt_spec h hu
  simp only [hfu, Bool.not_true, Bool.false_or] at h'
  exact testBit_eq_false_of_and h' hfv

theorem h3_of {u v w : ℕ} (hu : u < 85) (hv : v < 85) (huv : (badRow c u).testBit v = true)
    (hvw : (badRow c v).testBit w = true) : (badRow c u).testBit w = false := by
  have h := allLt_spec (allLt_spec (check3_ok c) hu) hv
  simp only [huv, Bool.not_true, Bool.false_or] at h
  exact testBit_eq_false_of_and h hvw

theorem h4_of {u v w x : ℕ} (hu : u < 85) (hv : v < 85) (hw : w < 85)
    (huv : (badRow c u).testBit v = true)
    (huw : (rowA c u).testBit w = true) (hvw : (rowA c v).testBit w = true)
    (hux : (rowA c u).testBit x = true) (hvx : (rowA c v).testBit x = true) :
    (badRow c w).testBit x = false := by
  have h := allLt_spec (allLt_spec (check4_ok c) hu) hv
  simp only [huv, Bool.not_true, Bool.false_or] at h
  have h' := allLt_spec h hw
  simp only [Nat.testBit_and, huw, hvw, Bool.and_self, Bool.not_true, Bool.false_or] at h'
  apply testBit_eq_false_of_and h'
  simp [Nat.testBit_and, hux, hvx]

/-! ## The colour rows -/

theorem rowB_testBit {i j : ℕ} (hj : j < 85) (hij : i ≠ j) :
    (rowB i).testBit j = !(rowR i).testBit j := by
  simp [rowB, Nat.testBit_xor, mask85_testBit j hj, R1212.Search.testBit_two_pow_ne hij]

/-- Off the diagonal, `rowC c` is red for `c = true` and not red for `c = false`. -/
theorem rowC_testBit (c : Bool) {i j : ℕ} (hj : j < 85) (hij : i ≠ j) :
    (rowC c i).testBit j = true ↔ ((rowR i).testBit j = true ↔ c = true) := by
  cases c
  · simp [rowC, rowB_testBit hj hij]
  · simp [rowC]

theorem rowC_irrefl (c : Bool) {i : ℕ} (hi : i < 85) : (rowC c i).testBit i = false := by
  cases c
  · simp [rowC, rowB, Nat.testBit_xor, mask85_testBit i hi, rowR_irrefl i hi]
  · exact rowR_irrefl i hi

theorem rowC_symm (c : Bool) {i j : ℕ} (hi : i < 85) (hj : j < 85) :
    (rowC c i).testBit j = (rowC c j).testBit i := by
  by_cases hij : i = j
  · rw [hij]
  cases c
  · simp only [rowC]
    rw [rowB_testBit hj hij, rowB_testBit hi (Ne.symm hij), rowR_symm i hi j hj]
  · exact rowR_symm i hi j hj

/-- Away from the antipodal pairs, `rowA c` is `rowC c`. -/
theorem rowA_testBit (c : Bool) {i j : ℕ} (hj : j < 85) (ha : (antiRow i).testBit j = false) :
    (rowA c i).testBit j = (rowC c i).testBit j := by
  simp [rowA, Nat.testBit_and, Nat.testBit_xor, mask85_testBit j hj, ha]

theorem sigB_testBit {p q : ℕ} (hq : q < 21) (hpq : p ≠ q) :
    (sigB p).testBit q = !(sigR p).testBit q := by
  simp [sigB, Nat.testBit_xor, mask21_testBit q hq, R1212.Search.testBit_two_pow_ne hpq]

/-- Off the diagonal, `sigC c` is `sigR` for `c = true` and its complement for `c = false`. -/
theorem sigC_testBit (c : Bool) {p q : ℕ} (hq : q < 21) (hpq : p ≠ q) :
    (sigC c p).testBit q = true ↔ ((sigR p).testBit q = true ↔ c = true) := by
  cases c
  · simp [sigC, sigB_testBit hq hpq]
  · simp [sigC]

theorem sigC_irrefl (c : Bool) {p : ℕ} (hp : p < 21) : (sigC c p).testBit p = false := by
  cases c
  · simp [sigC, sigB, Nat.testBit_xor, mask21_testBit p hp, sigR_irrefl p hp]
  · exact sigR_irrefl p hp

end R1661
end RamseyIncrement
