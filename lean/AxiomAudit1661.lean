import RamseyIncrement.R1661.Main

/-!
Axiom audit for `R(12,12) ≥ 1661`: every theorem should depend only on `propext`,
`Classical.choice`, `Quot.sound` (no `sorryAx`, no `Lean.ofReduceBool` from `native_decide`).

Also prints the statement with every implicit argument shown, and restates it in plain Mathlib
terms.
-/

set_option pp.explicit true in
#check @RamseyIncrement.R1661.r1212_lower_bound

#print RamseyIncrement.ramseyNumber
#print RamseyIncrement.ForcesRamsey
#print RamseyIncrement.HasRamseyColoring
#print RamseyIncrement.IsRamseyFree

/-- Plain Mathlib form: some red/blue colouring of the edges of `K₁₆₆₀` (red = edges of `G`,
blue = edges of the complement) has neither a red `K₁₂` nor a blue `K₁₂`. -/
theorem audit_exists_colouring_1660 :
    ∃ G : SimpleGraph (Fin 1660), (∀ s : Finset (Fin 1660), ¬ G.IsNClique 12 s) ∧
      (∀ s : Finset (Fin 1660), ¬ Gᶜ.IsNClique 12 s) := by
  obtain ⟨G, hred, hblue⟩ := RamseyIncrement.R1661.r1212_hasRamseyColoring
  exact ⟨G, hred, hblue⟩

example : 1661 ≤ RamseyIncrement.ramseyNumber 12 12 := RamseyIncrement.R1661.r1212_lower_bound

#print axioms RamseyIncrement.R1661.r1212_lower_bound
#print axioms RamseyIncrement.R1661.r1212_hasRamseyColoring
#print axioms audit_exists_colouring_1660
#print axioms RamseyIncrement.R1661.G1660_isRamseyFree
#print axioms RamseyIncrement.R1661.colG_cliqueFree
#print axioms RamseyIncrement.R1661.mathon_antip
#print axioms RamseyIncrement.R1661.card_W
#print axioms RamseyIncrement.R1661.sigR_spec
#print axioms RamseyIncrement.R1661.antiRow_spec
#print axioms RamseyIncrement.R1661.noK12
#print axioms RamseyIncrement.R1661.checks_ok
#print axioms RamseyIncrement.R1661.badRow_spec
#print axioms RamseyIncrement.R1661.cstMask_spec
#print axioms RamseyIncrement.R1658.defect_le_one
#print axioms RamseyIncrement.R1212.mathon_isRamseyFree
#print axioms RamseyIncrement.R1212.paley_cliqueFree
