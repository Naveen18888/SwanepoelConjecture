module
public import Swanepoel.DefectPortRealization
public import Swanepoel.OuterFace
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

def PennyGraph.ordinaryTrackComponents {n : ℕ} (G : PennyGraph n) :
    Finset (TrackComponent G) :=
  Finset.univ.filter (fun c => ∀ e : OrientedEdge G,
    SpineSource e → edgeComponent e = c →
      ¬ Bornology.IsBounded (G.sourceFace e).val)

def PennyGraph.terminalTrackComponents {n : ℕ} (G : PennyGraph n) :
    Finset (TrackComponent G) :=
  Finset.univ \ G.ordinaryTrackComponents

@[simp] theorem PennyGraph.mem_ordinaryTrackComponents {n : ℕ} (G : PennyGraph n)
    (c : TrackComponent G) : c ∈ G.ordinaryTrackComponents ↔
      ∀ e : OrientedEdge G, SpineSource e → edgeComponent e = c →
        ¬ Bornology.IsBounded (G.sourceFace e).val := by
  simp only [PennyGraph.ordinaryTrackComponents, Finset.mem_filter,
    Finset.mem_univ, true_and]

@[simp] theorem PennyGraph.mem_terminalTrackComponents {n : ℕ} (G : PennyGraph n)
    (c : TrackComponent G) :
    c ∈ G.terminalTrackComponents ↔ c ∉ G.ordinaryTrackComponents := by
  simp only [PennyGraph.terminalTrackComponents, Finset.mem_sdiff,
    Finset.mem_univ, true_and]

theorem PennyGraph.ordinary_terminal_disjoint {n : ℕ} (G : PennyGraph n) :
    Disjoint G.ordinaryTrackComponents G.terminalTrackComponents := by
  apply Finset.disjoint_left.mpr
  intro c hc ht
  exact (G.mem_terminalTrackComponents c).mp ht hc

theorem PennyGraph.ordinary_union_terminal {n : ℕ} (G : PennyGraph n) :
    G.ordinaryTrackComponents ∪ G.terminalTrackComponents = Finset.univ := by
  ext c
  simp only [Finset.mem_union, G.mem_terminalTrackComponents,
    Finset.mem_univ, iff_true]
  exact em _

theorem PennyGraph.track_classification_card {n : ℕ} (G : PennyGraph n) :
    G.ordinaryTrackComponents.card + G.terminalTrackComponents.card =
      Fintype.card (TrackComponent G) := by
  rw [← Finset.card_union_of_disjoint G.ordinary_terminal_disjoint,
    G.ordinary_union_terminal, Finset.card_univ]

theorem PennyGraph.componentSystem_ordinary_count {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (f : ℕ) :
    (componentSystem G ht G.ordinaryTrackComponents f).t =
      G.ordinaryTrackComponents.card := by
  simp only [TrackSystem.t, componentSystem, Finset.card_map]

theorem PennyGraph.componentSystem_terminal_count {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (f : ℕ) :
    (componentSystem G ht G.ordinaryTrackComponents f).p =
      G.terminalTrackComponents.card := by
  change (Finset.univ \ G.ordinaryTrackComponents.map
    (Fintype.equivFin (TrackComponent G)).toEmbedding).card =
      G.terminalTrackComponents.card
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
    PennyGraph.terminalTrackComponents,
    Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simp only [Finset.card_univ, Fintype.card_fin, Finset.card_map]

theorem PennyGraph.componentSystem_K_eq {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (f : ℕ) :
    (componentSystem G ht G.ordinaryTrackComponents f).K =
      (G.terminalTrackComponents.card : ℤ) - 2 * f := by
  rw [TrackSystem.K, G.componentSystem_terminal_count]
  rfl

theorem PennyGraph.terminal_iff_bounded_source {n : ℕ} (G : PennyGraph n)
    (c : TrackComponent G) :
    c ∈ G.terminalTrackComponents ↔ ∃ e : OrientedEdge G,
      SpineSource e ∧ edgeComponent e = c ∧
      Bornology.IsBounded (G.sourceFace e).val := by
  rw [G.mem_terminalTrackComponents, G.mem_ordinaryTrackComponents]
  constructor
  · intro hc
    by_contra hn
    apply hc
    intro e he hec hb
    exact hn ⟨e, he, hec, hb⟩
  · rintro ⟨e, he, hec, hb⟩ ho
    exact ho e he hec hb

theorem PennyGraph.defectPlaneFace_isBounded {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {F : PlaneFace G} (hF : F ∈ G.defectPlaneFaces ht) :
    Bornology.IsBounded F.val := by
  obtain ⟨B, _, hBF⟩ := Finset.mem_image.mp hF
  subst F
  exact B.property.2

theorem PennyGraph.terminal_iff_defect_source {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (c : TrackComponent G) :
    c ∈ G.terminalTrackComponents ↔ ∃ e : OrientedEdge G,
      SpineSource e ∧ edgeComponent e = c ∧
      G.sourceFace e ∈ G.defectPlaneFaces ht := by
  rw [G.terminal_iff_bounded_source]
  constructor
  · rintro ⟨e, he, hec, hb⟩
    exact ⟨e, he, hec, (G.sourceFace_defect_or_unbounded ht e he).resolve_right
      (fun hu => hu hb)⟩
  · rintro ⟨e, he, hec, hdef⟩
    exact ⟨e, he, hec, G.defectPlaneFace_isBounded ht hdef⟩

theorem PennyGraph.ordinary_iff_no_defect_source {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (c : TrackComponent G) :
    c ∈ G.ordinaryTrackComponents ↔ ∀ e : OrientedEdge G,
      SpineSource e → edgeComponent e = c →
      G.sourceFace e ∉ G.defectPlaneFaces ht := by
  constructor
  · intro hc e he hec hdef
    exact (G.mem_ordinaryTrackComponents c).mp hc e he hec
      (G.defectPlaneFace_isBounded ht hdef)
  · intro hn
    apply (G.mem_ordinaryTrackComponents c).mpr
    intro e he hec hb
    exact hn e he hec ((G.sourceFace_defect_or_unbounded ht e he).resolve_right
      (fun hu => hu hb))

theorem PennyGraph.ordinary_iff_two_exterior_ends {n : ℕ} (G : PennyGraph n)
    (c : TrackComponent G) {s t : OrientedEdge G}
    (hall : ∀ e, (SpineSource e ∧ edgeComponent e = c) ↔ e = s ∨ e = t) :
    c ∈ G.ordinaryTrackComponents ↔
      ¬ Bornology.IsBounded (G.sourceFace s).val ∧
      ¬ Bornology.IsBounded (G.sourceFace t).val := by
  rw [G.mem_ordinaryTrackComponents]
  constructor
  · intro hc
    have hs := (hall s).mpr (Or.inl rfl)
    have ht := (hall t).mpr (Or.inr rfl)
    exact ⟨hc s hs.1 hs.2, hc t ht.1 ht.2⟩
  · rintro ⟨hs, ht⟩ e he hec
    rcases (hall e).mp ⟨he, hec⟩ with rfl | rfl
    · exact hs
    · exact ht

theorem PennyGraph.ordinary_iff_sourceFace_eq_outer {n : ℕ} (G : PennyGraph n)
    (c : TrackComponent G) (outer : PlaneFace G)
    (houter : ¬ Bornology.IsBounded outer.val) :
    c ∈ G.ordinaryTrackComponents ↔ ∀ e : OrientedEdge G,
      SpineSource e → edgeComponent e = c → G.sourceFace e = outer := by
  obtain ⟨F, hF, huniq⟩ := G.exists_unique_outer_face
  have hOF : outer = F := huniq outer houter
  constructor
  · intro hc e he hec
    exact (huniq (G.sourceFace e)
      ((G.mem_ordinaryTrackComponents c).mp hc e he hec)).trans hOF.symm
  · intro hc
    apply (G.mem_ordinaryTrackComponents c).mpr
    intro e he hec
    rw [hc e he hec]
    exact houter

theorem PennyGraph.classified_two_source_ends {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (c : TrackComponent G) :
    ∃ s t : OrientedEdge G, s ≠ t ∧
      (∀ e, (SpineSource e ∧ edgeComponent e = c) ↔ e = s ∨ e = t) ∧
      (c ∈ G.ordinaryTrackComponents ↔
        ¬ Bornology.IsBounded (G.sourceFace s).val ∧
        ¬ Bornology.IsBounded (G.sourceFace t).val) := by
  obtain ⟨s, t, hne, hall⟩ := component_sources ht c
  exact ⟨s, t, hne, hall, G.ordinary_iff_two_exterior_ends c hall⟩

theorem PennyGraph.defect_source_port_terminal {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {F : PlaneFace G} (hF : F ∈ G.defectPlaneFaces ht)
    {e : OrientedEdge G} (he : e ∈ G.faceSourcePorts F) :
    edgeComponent e ∈ G.terminalTrackComponents := by
  have hep := (Finset.mem_filter.mp he).2
  apply (G.terminal_iff_defect_source ht (edgeComponent e)).mpr
  exact ⟨e, hep.1, rfl, hep.2 ▸ hF⟩

theorem PennyGraph.defect_family_source_port_terminal {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {e : OrientedEdge G}
    (he : e ∈ G.familySourcePorts (G.defectPlaneFaces ht)) :
    edgeComponent e ∈ G.terminalTrackComponents := by
  have hep := (Finset.mem_filter.mp he).2
  exact (G.terminal_iff_defect_source ht (edgeComponent e)).mpr
    ⟨e, hep.1, rfl, hep.2⟩

theorem PennyGraph.defect_source_ports_card_le_terminal {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) :
    ∑ F ∈ G.defectPlaneFaces ht, (G.faceSourcePorts F).card ≤
      2 * G.terminalTrackComponents.card := by
  let S : Finset (OrientedEdge G) := Finset.univ.filter
    (fun e => SpineSource e ∧ edgeComponent e ∈ G.terminalTrackComponents)
  have hS : S.card = 2 * G.terminalTrackComponents.card := by
    rw [Finset.card_eq_sum_card_fiberwise
      (f := edgeComponent) (s := S) (t := G.terminalTrackComponents)
      (fun e he => (Finset.mem_filter.mp he).2.2)]
    have hsum : (∑ c ∈ G.terminalTrackComponents,
        (S.filter (fun e => edgeComponent e = c)).card) =
        ∑ _ ∈ G.terminalTrackComponents, 2 := by
      apply Finset.sum_congr rfl
      intro c hc
      have hf : S.filter (fun e => edgeComponent e = c) =
          Finset.univ.filter (fun e => SpineSource e ∧ edgeComponent e = c) := by
        ext e
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨⟨he, _⟩, hec⟩
          exact ⟨he, hec⟩
        · rintro ⟨he, hec⟩
          exact ⟨⟨he, hec ▸ hc⟩, hec⟩
      rw [hf, component_source_count ht c]
    rw [hsum]
    simp [Nat.mul_comm]
  rw [← G.familySourcePorts_card]
  calc
    _ ≤ S.card := Finset.card_le_card (by
      intro e he
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp he).2.1, G.defect_family_source_port_terminal ht he⟩)
    _ = _ := hS

theorem PennyGraph.terminal_effective_nonneg_of_defect_source_ports {n : ℕ}
    (G : PennyGraph n) (ht : G.TriangleFree)
    (hports : ∀ F ∈ G.defectPlaneFaces ht, 4 ≤ (G.faceSourcePorts F).card) :
    0 ≤ (G.terminalTrackComponents.card : ℤ) - 2 * G.faceDefectCount ht := by
  have hlo : 4 * (G.defectPlaneFaces ht).card ≤
      ∑ F ∈ G.defectPlaneFaces ht, (G.faceSourcePorts F).card := by
    calc
      _ = ∑ _ ∈ G.defectPlaneFaces ht, 4 := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum hports
  rw [G.defectPlaneFaces_card ht] at hlo
  have hhi := G.defect_source_ports_card_le_terminal ht
  have hnat : 2 * G.faceDefectCount ht ≤ G.terminalTrackComponents.card := by omega
  exact sub_nonneg.mpr (by exact_mod_cast hnat)

end Swanepoel
