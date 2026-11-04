/-
R(12,12) ≥ 1661.
-/
import RamseyIncrement.R1661.Projection
import RamseyIncrement.RamseyNumber

/-!
# `R(12,12) ≥ 1661`

`G1660` (`Graph.lean`) is a red/blue colouring of `K₁₆₆₀`: the Mathon graph `M(797)` without
21 vertices `Σ_V`, and 85 core vertices, each of which copies a vertex of `Σ_V` or is constant
towards the rest of `M(797)`.  `Projection.lean` shows that it has no monochromatic `K₁₂`,
using only that `M(797)` is an `(11,11)`-colouring (`R1212.mathon_isRamseyFree`), that
antipodal vertices of `M(797)` have opposite colours towards all other vertices
(`mathon_antip`), and finite checks on the 85-vertex core (`Checks.lean`, evaluated by the
kernel).
-/

namespace RamseyIncrement
namespace R1661

/-- A `(12,12)`-colouring on `1660` vertices. -/
theorem r1212_hasRamseyColoring : HasRamseyColoring 1660 12 12 :=
  ⟨_, G1660_isRamseyFree.overFin card_W⟩

/-- **`R(12,12) ≥ 1661`.** -/
theorem r1212_lower_bound : 1661 ≤ ramseyNumber 12 12 :=
  ramseyNumber_lower_bound r1212_hasRamseyColoring

end R1661
end RamseyIncrement
