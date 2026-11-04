import RamseyIncrement.R1661.Graph

/-!
# Writing out the 1660-vertex colouring

Not part of the proof.  Evaluates `G1660.Adj` (with Lean's interpreter) in the vertex order of
`b1660_PM2.graph` and writes rows `i:` followed by 1660 characters, `1` for red.
`tools/compare_export_1661.py` compares them with the file.

Only the rows of the 85 core vertices (file vertices `1575–1659`) are written: every pair whose
colour is not simply that of `M(797)` lies in one of these rows, and on `V°` the colouring is
`M(797)` by definition (`adj_inl_inl` is `Iff.rfl`).
-/

open RamseyIncrement R1661 R1212

/-- File numbering of `M(797)`: `A_k`, `B_{k-797}`, `a`, `b`. -/
def mvOf (k : ℕ) : MV :=
  if k < 797 then MV.A (k : ZMod 797)
  else if k < 1594 then MV.B ((k - 797 : ℕ) : ZMod 797)
  else if k = 1594 then MV.a
  else MV.b

/-- `V°` in file order. -/
def v0List : List V0 := (List.range 1596).filterMap fun k ↦
  if h : mvOf k ∈ sigSet then none else some ⟨mvOf k, h⟩

/-- File vertex `n`. -/
def vertexOf (n : ℕ) : Option W :=
  if n < 1575 then (v0List[n]?).map Sum.inl
  else if h : n < 1660 then some (.inr ⟨n - 1575, by omega⟩) else none

def exportRow (i : ℕ) : String :=
  String.mk ((List.range 1660).map fun j ↦
    match vertexOf i, vertexOf j with
    | some x, some y => if decide (G1660.Adj x y) then '1' else '0'
    | _, _ => '?')

#eval show IO Unit from do
  IO.println s!"|V°| = {v0List.length}"
  IO.FS.createDirAll "build/export"
  let h ← IO.FS.Handle.mk "build/export/rows_1661_from_lean.txt" IO.FS.Mode.write
  for i in (List.range 85).map (· + 1575) do
    h.putStr (toString i ++ ":" ++ exportRow i ++ "\n")
    h.flush
  IO.println "wrote build/export/rows_1661_from_lean.txt"
