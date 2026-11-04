/-
R(12,12) ≥ 1661: the projection argument.
-/
import RamseyIncrement.R1661.Graph
import RamseyIncrement.R1658.Defect
import RamseyIncrement.R1212.PaleyClique

/-!
# No monochromatic `K₁₂`

Let `Q` be a clique of colour `c` with `12` vertices.  Its vertices are core vertices (their
core positions form `K`) or vertices of `V°`.

* If `K` contains a vertex that is constant `¬c` towards `V°`, then `Q` has no vertex in `V°`.
  So `K` is a `c`-clique of the core with `12` vertices, which `noK12` excludes.
* If `K` contains two vertices that copy antipodal sigma vertices `g` and `ḡ`, then again `Q`
  has no vertex in `V°`: every vertex of `V°` has opposite colours towards `g` and `ḡ`
  (`mathon_antip`).  `noK12` excludes this too.
* Otherwise `K` is a clique of `rowA c`, and `R1658.defect_le_one` gives `S ⊆ K` with
  `|S| ≥ |K| - 1`, no constant vertex and no conflict.  The sigma vertices `sig (vt j)`
  (`j ∈ S`) are then distinct and form a `c`-clique `T` of `M(797)`.  Each vertex of `Q` in
  `V°` has colour `c` towards each of them (copies copy).  So `T` and the part of `Q` in `V°`
  form a `c`-clique of `M(797)` with at least `|K| - 1 + (12 - |K|) = 11` vertices, which
  `mathon_isRamseyFree` excludes.

Only this last step uses anything about `M(797)` beyond the 21 sigma vertices and the
antipodes.
-/

namespace RamseyIncrement
namespace R1661

open R1212 SimpleGraph

/-- `G` for red (`true`), `Gᶜ` for blue (`false`). -/
def colG {V : Type*} : Bool → SimpleGraph V → SimpleGraph V
  | true, G => G
  | false, G => Gᶜ

theorem colG_adj {V : Type*} (c : Bool) (G : SimpleGraph V) (x y : V) :
    (colG c G).Adj x y ↔ x ≠ y ∧ (G.Adj x y ↔ c = true) := by
  cases c
  · show Gᶜ.Adj x y ↔ _
    rw [compl_adj]
    simp
  · show G.Adj x y ↔ _
    exact ⟨fun h ↦ ⟨G.ne_of_adj h, iff_of_true h rfl⟩, fun h ↦ h.2.2 rfl⟩

theorem mathon_colG_cliqueFree (c : Bool) : (colG c mathon).CliqueFree 11 := by
  have h := mathon_isRamseyFree paley_cliqueFree
  cases c
  · exact h.2
  · exact h.1

/-- The vertex of `M(797)` under a vertex of `W` (`b` for the core vertices; never used). -/
def toMV : W → MV := Sum.elim Subtype.val fun _ ↦ MV.b

/-- **No `c`-clique with `12` vertices.** -/
theorem colG_cliqueFree (c : Bool) : (colG c G1660).CliqueFree 12 := by
  classical
  intro Q hQ
  have hadj : ∀ x ∈ Q, ∀ y ∈ Q, x ≠ y → (G1660.Adj x y ↔ c = true) := fun x hx y hy hxy ↦
    ((colG_adj c G1660 x y).1 (hQ.isClique hx hy hxy)).2
  -- the core part and the `V°` part of `Q`
  obtain ⟨Qc, hQc⟩ : ∃ Qc : Finset W, Qc = Q.filter (fun x ↦ idx x < 85) := ⟨_, rfl⟩
  obtain ⟨Qo, hQo⟩ : ∃ Qo : Finset W, Qo = Q.filter (fun x ↦ ¬idx x < 85) := ⟨_, rfl⟩
  have memQc : ∀ x, x ∈ Qc ↔ x ∈ Q ∧ idx x < 85 := fun x ↦ by rw [hQc, Finset.mem_filter]
  have memQo : ∀ x, x ∈ Qo ↔ x ∈ Q ∧ ¬idx x < 85 := fun x ↦ by rw [hQo, Finset.mem_filter]
  have hsplit : Qc.card + Qo.card = 12 := by
    rw [hQc, hQo, Finset.card_filter_add_card_filter_not, hQ.card_eq]
  have hQo_inl : ∀ y ∈ Qo, ∃ u : V0, y = .inl u := fun y hy ↦ eq_inl_of_idx ((memQo y).1 hy).2
  -- the core positions `K` of `Q`
  obtain ⟨K, hK⟩ : ∃ K : Finset ℕ, K = Qc.image idx := ⟨_, rfl⟩
  have memK : ∀ j, j ∈ K ↔ ∃ x ∈ Qc, idx x = j := fun j ↦ by rw [hK, Finset.mem_image]
  have hKcard : K.card = Qc.card := by
    rw [hK]
    apply Finset.card_image_of_injOn
    intro x hx y hy hxy
    have hx' := ((memQc x).1 hx).2
    have hy' := ((memQc y).1 hy).2
    calc x = coreV (idx x) := (coreV_idx hx').symm
      _ = coreV (idx y) := by rw [hxy]
      _ = y := coreV_idx hy'
  have hKlt : ∀ j ∈ K, j < 85 := by
    intro j hj
    obtain ⟨x, hx, rfl⟩ := (memK j).1 hj
    exact ((memQc x).1 hx).2
  have hKQ : ∀ j ∈ K, coreV j ∈ Q := by
    intro j hj
    obtain ⟨x, hx, rfl⟩ := (memK j).1 hj
    have hx' := (memQc x).1 hx
    rw [coreV_idx hx'.2]
    exact hx'.1
  have hKclique : ∀ i ∈ K, ∀ j ∈ K, i ≠ j → (rowC c i).testBit j = true := by
    intro i hi j hj hij
    have hxy : coreV i ≠ coreV j := by
      rw [coreV_lt (hKlt i hi), coreV_lt (hKlt j hj)]
      intro h
      exact hij (Fin.mk.inj_iff.1 (Sum.inr_injective h))
    rw [rowC_testBit c (hKlt j hj) hij, ← adj_core (hKlt i hi) (hKlt j hj) hij]
    exact hadj _ (hKQ i hi) _ (hKQ j hj) hxy
  -- colours between core positions of `Q` and the part of `Q` in `V°`
  have hout : ∀ j ∈ K, ∀ u : V0, (.inl u : W) ∈ Q → (G1660.Adj (coreV j) (.inl u) ↔ c = true) :=
    fun j hj u hu ↦ hadj _ (hKQ j hj) _ hu (coreV_ne_inl j u)
  -- if `Q` has no vertex in `V°`, `noK12` applies
  have hcore : Qo = ∅ → False := by
    intro hQo0
    rw [hQo0, Finset.card_empty] at hsplit
    have := R1212.Search.noClique_sound (rowC c) 12 mask85 (noK12 c) K hKclique
      (fun j hj ↦ mask85_testBit j (hKlt j hj))
    omega
  by_cases hA : ∃ j ∈ K, vt j = constCode (!c)
  · -- a constant-`¬c` vertex: `Q` lies in the core
    obtain ⟨j, hj, hjc⟩ := hA
    apply hcore
    apply Finset.eq_empty_of_forall_notMem
    intro y hy
    obtain ⟨u, rfl⟩ := hQo_inl y hy
    have h1 := hout j hj u ((memQo _).1 hy).1
    rw [adj_out_const (hKlt j hj) (!c) hjc u] at h1
    cases c <;> simp at h1
  push Not at hA
  by_cases hP : ∃ i ∈ K, ∃ j ∈ K, (antiRow i).testBit j = true
  · -- copies of two antipodal sigma vertices: `Q` lies in the core
    obtain ⟨i, hi, j, hj, hij⟩ := hP
    rw [antiRow_spec i (hKlt i hi) j (hKlt j hj)] at hij
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hij
    obtain ⟨⟨hnci, hncj⟩, hanti⟩ := hij
    have hi21 : vt i < 21 := by simpa [isNC] using hnci
    have hj21 : vt j < 21 := by simpa [isNC] using hncj
    apply hcore
    apply Finset.eq_empty_of_forall_notMem
    intro y hy
    obtain ⟨u, rfl⟩ := hQo_inl y hy
    have huQ := ((memQo _).1 hy).1
    have h1 := hout i hi u huQ
    have h2 := hout j hj u huQ
    rw [adj_out_nc (hKlt i hi) hnci u] at h1
    have hu2 : u.1 ≠ antip (sigN (vt i)) := by
      rw [← hanti]
      exact Ne.symm (sigN_ne hj21 u)
    rw [adj_out_nc (hKlt j hj) hncj u, hanti,
      mathon_antip _ _ (Ne.symm (sigN_ne hi21 u)) hu2] at h2
    tauto
  -- no antipodal pair: `K` is a clique of `rowA c`; delete at most one defect
  push Not at hP
  have hPf : ∀ i ∈ K, ∀ j ∈ K, (antiRow i).testBit j = false := fun i hi j hj ↦ by
    simpa using hP i hi j hj
  have hKcliqueA : ∀ i ∈ K, ∀ j ∈ K, i ≠ j → (rowA c i).testBit j = true := by
    intro i hi j hj hij
    rw [rowA_testBit c (hKlt j hj) (hPf i hi j hj)]
    exact hKclique i hi j hj hij
  obtain ⟨S, hSK, hScard, hScst, hSbad⟩ := R1658.defect_le_one (n := 85)
    (adj := fun u v ↦ (rowA c u).testBit v = true)
    (cst := fun j ↦ (cstMask c).testBit j = true)
    (bad := fun u v ↦ (badRow c u).testBit v = true)
    (fun u hu v hv h ↦ by rw [← badRow_symm c u hu v hv]; exact h)
    (fun f hf g hcf hfg hcg ↦ Bool.false_ne_true ((h1_of hf hcf hfg).symm.trans hcg))
    (fun f hf u hu v hcf hfu hfv hb ↦
      Bool.false_ne_true ((h2_of hf hu hcf hfu hfv).symm.trans hb))
    (fun u hu v hv w huv hvw huw ↦ Bool.false_ne_true ((h3_of hu hv huv hvw).symm.trans huw))
    (fun u hu v hv w hw x huv huw hvw hux hvx hwx ↦
      Bool.false_ne_true ((h4_of hu hv hw huv huw hvw hux hvx).symm.trans hwx))
    K hKlt hKcliqueA
  -- every position in `S` copies a sigma vertex
  have hSnc : ∀ j ∈ S, vt j < 21 := by
    intro j hj
    have hjK := hSK hj
    have hj85 := hKlt j hjK
    have hcst : (cstMask c).testBit j = false := by simpa using hScst j hj
    rw [cstMask_spec c j hj85] at hcst
    have h1 : vt j ≠ constCode c := by simpa using hcst
    have h2 := hA j hjK
    have hvt := vt_lt j hj85
    cases c <;> simp only [constCode, Bool.not_true, Bool.not_false] at h1 h2 <;> omega
  have hSnc' : ∀ j ∈ S, isNC j = true := fun j hj ↦ by simp [isNC, hSnc j hj]
  -- two positions of `S` copy distinct sigma vertices joined in colour `c`
  have hSpair : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      vt i ≠ vt j ∧ (mathon.Adj (sigN (vt i)) (sigN (vt j)) ↔ c = true) := by
    intro i hi j hj hij
    have hi85 := hKlt i (hSK hi)
    have hj85 := hKlt j (hSK hj)
    have hcl := hKclique i (hSK hi) j (hSK hj) hij
    have hb : (badRow c i).testBit j = false := by simpa using hSbad i hi j hj hij
    rw [badRow_spec c i hi85 j hj85] at hb
    have hne : (i != j) = true := bne_iff_ne.2 hij
    have hb' : (sigC c (vt i)).testBit (vt j) = true := by
      simpa [badB, hne, hSnc' i hi, hSnc' j hj, hcl, hPf i (hSK hi) j (hSK hj)] using hb
    have hpi := hSnc i hi
    have hpj := hSnc j hj
    have hne' : vt i ≠ vt j := by
      intro h
      rw [h, sigC_irrefl c hpj] at hb'
      exact Bool.false_ne_true hb'
    refine ⟨hne', ?_⟩
    rw [← decide_eq_true_iff (p := mathon.Adj _ _), ← sigR_spec _ hpi _ hpj]
    exact (sigC_testBit c hpj hne').1 hb'
  -- `T`: those sigma vertices; `U`: the part of `Q` in `V°`
  obtain ⟨T, hT⟩ : ∃ T : Finset MV, T = S.image (fun j ↦ sigN (vt j)) := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U : Finset MV, U = Qo.image toMV := ⟨_, rfl⟩
  have memU : ∀ u ∈ U, ∃ v : V0, v.1 = u ∧ (.inl v : W) ∈ Q := by
    intro u hu
    rw [hU, Finset.mem_image] at hu
    obtain ⟨y, hy, rfl⟩ := hu
    obtain ⟨v, rfl⟩ := hQo_inl y hy
    exact ⟨v, rfl, ((memQo _).1 hy).1⟩
  have hTcard : T.card = S.card := by
    rw [hT]
    apply Finset.card_image_of_injOn
    intro i hi j hj hij
    by_contra hne
    exact (hSpair i hi j hj hne).1 (sigN_inj (hSnc i hi) (hSnc j hj) hij)
  have hUcard : U.card = Qo.card := by
    rw [hU]
    apply Finset.card_image_of_injOn
    intro y₁ hy₁ y₂ hy₂ h
    obtain ⟨u₁, rfl⟩ := hQo_inl y₁ hy₁
    obtain ⟨u₂, rfl⟩ := hQo_inl y₂ hy₂
    exact congrArg Sum.inl (Subtype.ext h)
  have hdisj : Disjoint T U := by
    rw [Finset.disjoint_left]
    intro a haT haU
    rw [hT, Finset.mem_image] at haT
    obtain ⟨i, hi, rfl⟩ := haT
    obtain ⟨v, hv, -⟩ := memU _ haU
    exact sigN_ne (hSnc i hi) v hv.symm
  have hTT : ∀ a ∈ T, ∀ a' ∈ T, a ≠ a' → (colG c mathon).Adj a a' := by
    intro a ha a' ha' haa'
    rw [hT, Finset.mem_image] at ha ha'
    obtain ⟨i, hi, rfl⟩ := ha
    obtain ⟨j, hj, rfl⟩ := ha'
    have hij : i ≠ j := fun h ↦ haa' (by rw [h])
    rw [colG_adj]
    exact ⟨haa', (hSpair i hi j hj hij).2⟩
  have hTU : ∀ a ∈ T, ∀ u ∈ U, (colG c mathon).Adj a u := by
    intro a ha u hu
    rw [hT, Finset.mem_image] at ha
    obtain ⟨j, hj, rfl⟩ := ha
    obtain ⟨v, rfl, hvQ⟩ := memU u hu
    have hjK := hSK hj
    have h1 := hout j hjK v hvQ
    rw [adj_out_nc (hKlt j hjK) (hSnc' j hj) v] at h1
    rw [colG_adj]
    exact ⟨sigN_ne (hSnc j hj) v, h1⟩
  have hUU : ∀ u ∈ U, ∀ u' ∈ U, u ≠ u' → (colG c mathon).Adj u u' := by
    intro u hu u' hu' huu'
    obtain ⟨v, rfl, hvQ⟩ := memU u hu
    obtain ⟨v', rfl, hv'Q⟩ := memU u' hu'
    have h1 := hadj _ hvQ _ hv'Q (fun h ↦ huu' (congrArg Subtype.val (Sum.inl_injective h)))
    rw [colG_adj]
    exact ⟨huu', h1⟩
  -- together: a `c`-clique of `M(797)` with at least `11` vertices
  have hclique : (colG c mathon).IsClique ((T ∪ U : Finset MV) : Set MV) := by
    intro a ha a' ha' haa'
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at ha ha'
    rcases ha with ha | ha <;> rcases ha' with ha' | ha'
    · exact hTT a ha a' ha' haa'
    · exact hTU a ha a' ha'
    · exact (hTU a' ha' a ha).symm
    · exact hUU a ha a' ha' haa'
  have hcard : 11 ≤ (T ∪ U).card := by
    rw [Finset.card_union_of_disjoint hdisj, hTcard, hUcard]
    omega
  obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq hcard
  exact mathon_colG_cliqueFree c t ⟨hclique.subset (Finset.coe_subset.2 hts), htc⟩

/-- **The 1660-vertex colouring has no monochromatic `K₁₂`.** -/
theorem G1660_isRamseyFree : IsRamseyFree G1660 12 12 :=
  ⟨colG_cliqueFree true, colG_cliqueFree false⟩

end R1661
end RamseyIncrement
