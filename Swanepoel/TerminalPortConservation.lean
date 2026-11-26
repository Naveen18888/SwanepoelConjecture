module
public import Swanepoel.FacePortFive
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

def PennyGraph.terminalSourceEnds {n : ℕ} (G : PennyGraph n) : Finset (OrientedEdge G) :=
  Finset.univ.filter (fun e => SpineSource e ∧ edgeComponent e ∈ G.terminalTrackComponents)

def PennyGraph.terminalOuterSourceEnds {n : ℕ} (G : PennyGraph n) : Finset (OrientedEdge G) :=
  G.terminalSourceEnds.filter (fun e => ¬ Bornology.IsBounded (G.sourceFace e).val)

def PennyGraph.terminalBoundaryEndCount {n : ℕ} (G : PennyGraph n) : ℕ :=
  G.terminalOuterSourceEnds.card

theorem PennyGraph.terminalSourceEnds_count {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) : G.terminalSourceEnds.card = 2*G.terminalTrackComponents.card := by
  rw [Finset.card_eq_sum_card_fiberwise
    (f := edgeComponent) (s := G.terminalSourceEnds) (t := G.terminalTrackComponents)
    (fun e he => (Finset.mem_filter.mp he).2.2)]
  have hsum : (∑ c ∈ G.terminalTrackComponents,
      (G.terminalSourceEnds.filter (fun e => edgeComponent e = c)).card) =
      ∑ _ ∈ G.terminalTrackComponents, 2 := by
    apply Finset.sum_congr rfl
    intro c hc
    have hf : G.terminalSourceEnds.filter (fun e => edgeComponent e = c) =
        Finset.univ.filter (fun e => SpineSource e ∧ edgeComponent e = c) := by
      ext e
      simp only [PennyGraph.terminalSourceEnds, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨he, _⟩, hec⟩
        exact ⟨he, hec⟩
      · rintro ⟨he, hec⟩
        exact ⟨⟨he, hec ▸ hc⟩, hec⟩
    rw [hf, component_source_count ht c]
  rw [hsum]
  simp [Nat.mul_comm]

theorem PennyGraph.terminalSourceEnds_partition {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) :
    G.terminalSourceEnds = G.terminalOuterSourceEnds ∪
      G.familySourcePorts (G.defectPlaneFaces ht) := by
  ext e
  constructor
  · intro he
    have hes := (Finset.mem_filter.mp he).2.1
    rcases G.sourceFace_defect_or_unbounded ht e hes with hdef | hout
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hes, hdef⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he, hout⟩)
  · intro he
    rcases Finset.mem_union.mp he with hout | hdef
    · exact (Finset.mem_filter.mp hout).1
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hdef).2.1,
        G.defect_family_source_port_terminal ht hdef⟩

theorem PennyGraph.terminalSourceEnds_partition_disjoint {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) :
    Disjoint G.terminalOuterSourceEnds (G.familySourcePorts (G.defectPlaneFaces ht)) := by
  apply Finset.disjoint_left.mpr
  intro e hout hdef
  exact (Finset.mem_filter.mp hout).2
    (G.defectPlaneFace_isBounded ht (Finset.mem_filter.mp hdef).2.2)

theorem PennyGraph.terminal_endpoint_conservation {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) :
    2*G.terminalTrackComponents.card = G.terminalBoundaryEndCount +
      ∑ F ∈ G.defectPlaneFaces ht, (G.faceSourcePorts F).card := by
  rw [← G.terminalSourceEnds_count ht, G.terminalSourceEnds_partition ht,
    Finset.card_union_of_disjoint (G.terminalSourceEnds_partition_disjoint ht),
    G.familySourcePorts_card]
  rfl

def PennyGraph.defectPortExcess {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree) : ℤ :=
  (G.defectPlaneFaces ht).sum (fun F => ((G.faceSourcePorts F).card : ℤ)-4)

theorem PennyGraph.defectPortExcess_eq {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree) :
    G.defectPortExcess ht =
      (∑ F ∈ G.defectPlaneFaces ht, ((G.faceSourcePorts F).card : ℤ)) -
        4*G.faceDefectCount ht := by
  rw [PennyGraph.defectPortExcess, Finset.sum_sub_distrib]
  simp [G.defectPlaneFaces_card ht, mul_comm]

theorem PennyGraph.canonical_K_port_conservation {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) :
    2*(componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).K =
      (G.terminalBoundaryEndCount : ℤ)+G.defectPortExcess ht := by
  have hnat := G.terminal_endpoint_conservation ht
  have hint : 2*(G.terminalTrackComponents.card : ℤ) =
      (G.terminalBoundaryEndCount : ℤ) +
        ∑ F ∈ G.defectPlaneFaces ht, ((G.faceSourcePorts F).card : ℤ) := by
    exact_mod_cast hnat
  rw [G.componentSystem_K_eq, G.defectPortExcess_eq]
  omega

theorem PennyGraph.defects_le_defectPortExcess {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) : (G.faceDefectCount ht : ℤ) ≤ G.defectPortExcess ht := by
  change (G.faceDefectCount ht : ℤ) ≤
    (G.defectPlaneFaces ht).sum (fun F => ((G.faceSourcePorts F).card : ℤ)-4)
  calc
    _ = ∑ _ ∈ G.defectPlaneFaces ht, (1 : ℤ) := by simp [G.defectPlaneFaces_card ht]
    _ ≤ _ := Finset.sum_le_sum (by
      intro F hF
      have hn := G.defect_source_ports_five_le ht F hF
      have hi : (5 : ℤ) ≤ (G.faceSourcePorts F).card := by exact_mod_cast hn
      linarith)

theorem PennyGraph.boundary_ends_add_defects_le_twice_K {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) :
    (G.terminalBoundaryEndCount : ℤ)+G.faceDefectCount ht ≤
      2*(componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).K := by
  rw [G.canonical_K_port_conservation ht]
  have h := G.defects_le_defectPortExcess ht
  omega

theorem PennyGraph.terminalOuterSourceEnds_component_injOn {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) :
    Set.InjOn edgeComponent (G.terminalOuterSourceEnds : Set (OrientedEdge G)) := by
  intro e he f hf hcomp
  by_contra hne
  have hedata := (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2
  have hfdata := (Finset.mem_filter.mp (Finset.mem_filter.mp hf).1).2
  let E : Finset (OrientedEdge G) := Finset.univ.filter
    (fun g => SpineSource g ∧ edgeComponent g = edgeComponent e)
  have heE : e ∈ E := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hedata.1, rfl⟩
  have hfE : f ∈ E := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfdata.1, hcomp.symm⟩
  have hcard : E.card = 2 := component_source_count ht (edgeComponent e)
  have hpairs : ({e,f} : Finset (OrientedEdge G)) ⊆ E := by
    intro g hg
    simp only [Finset.mem_insert, Finset.mem_singleton] at hg
    rcases hg with rfl | rfl
    · exact heE
    · exact hfE
  have hE : E = {e,f} := (Finset.eq_of_subset_of_card_le hpairs (by
    rw [hcard, Finset.card_pair hne])).symm
  have hord : edgeComponent e ∈ G.ordinaryTrackComponents := by
    apply (G.mem_ordinaryTrackComponents _).mpr
    intro g hgs hgc
    have hgE : g ∈ E := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgs, hgc⟩
    rw [hE] at hgE
    simp only [Finset.mem_insert, Finset.mem_singleton] at hgE
    rcases hgE with rfl | rfl
    · exact (Finset.mem_filter.mp he).2
    · exact (Finset.mem_filter.mp hf).2
  exact (G.mem_terminalTrackComponents _).mp hedata.2 hord

def PennyGraph.terminalBoundaryTrackComponents {n : ℕ} (G : PennyGraph n) : Finset (TrackComponent G) :=
  G.terminalOuterSourceEnds.image edgeComponent

def PennyGraph.terminalJoinTrackComponents {n : ℕ} (G : PennyGraph n) : Finset (TrackComponent G) :=
  G.terminalTrackComponents \ G.terminalBoundaryTrackComponents

def PennyGraph.terminalJoinCount {n : ℕ} (G : PennyGraph n) : ℕ :=
  G.terminalJoinTrackComponents.card

theorem PennyGraph.terminalBoundaryTrackComponents_subset {n : ℕ} (G : PennyGraph n) :
    G.terminalBoundaryTrackComponents ⊆ G.terminalTrackComponents := by
  intro c hc
  obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hc
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2.2

theorem PennyGraph.terminalBoundaryTrackComponents_count {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) :
    G.terminalBoundaryTrackComponents.card = G.terminalBoundaryEndCount :=
  Finset.card_image_of_injOn (G.terminalOuterSourceEnds_component_injOn ht)

theorem PennyGraph.terminal_tracks_boundary_add_joins {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) :
    G.terminalTrackComponents.card = G.terminalBoundaryEndCount+G.terminalJoinCount := by
  have hc := Finset.card_sdiff_add_card_eq_card G.terminalBoundaryTrackComponents_subset
  change G.terminalJoinCount + G.terminalBoundaryTrackComponents.card =
    G.terminalTrackComponents.card at hc
  rw [G.terminalBoundaryTrackComponents_count ht] at hc
  omega

theorem PennyGraph.terminalJoin_iff_all_ends_defect {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (c : TrackComponent G) :
    c ∈ G.terminalJoinTrackComponents ↔ c ∈ G.terminalTrackComponents ∧
      ∀ e : OrientedEdge G, SpineSource e → edgeComponent e = c →
        G.sourceFace e ∈ G.defectPlaneFaces ht := by
  change c ∈ G.terminalTrackComponents \ G.terminalBoundaryTrackComponents ↔ _
  rw [Finset.mem_sdiff]
  constructor
  · rintro ⟨hc,hnot⟩
    refine ⟨hc,?_⟩
    intro e hes hec
    rcases G.sourceFace_defect_or_unbounded ht e hes with hdef | hout
    · exact hdef
    · exfalso
      apply hnot
      apply Finset.mem_image.mpr
      refine ⟨e,?_,hec⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,hes,hec ▸ hc⟩,hout⟩
  · rintro ⟨hc,hall⟩
    refine ⟨hc,?_⟩
    intro hbound
    obtain ⟨e,he,hec⟩ := Finset.mem_image.mp hbound
    have hes := (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2.1
    exact (Finset.mem_filter.mp he).2 (G.defectPlaneFace_isBounded ht (hall e hes hec))

theorem PennyGraph.defect_ports_boundary_add_twice_joins {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) :
    (∑ F ∈ G.defectPlaneFaces ht, (G.faceSourcePorts F).card) =
      G.terminalBoundaryEndCount+2*G.terminalJoinCount := by
  have he := G.terminal_endpoint_conservation ht
  have ht' := G.terminal_tracks_boundary_add_joins ht
  omega

theorem PennyGraph.five_defects_le_boundary_add_twice_joins {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) :
    5*G.faceDefectCount ht ≤ G.terminalBoundaryEndCount+2*G.terminalJoinCount := by
  have hlo : 5*(G.defectPlaneFaces ht).card ≤
      ∑ F ∈ G.defectPlaneFaces ht, (G.faceSourcePorts F).card := by
    calc
      _ = ∑ _ ∈ G.defectPlaneFaces ht, 5 := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum (G.defect_source_ports_five_le ht)
  rwa [G.defectPlaneFaces_card ht, G.defect_ports_boundary_add_twice_joins ht] at hlo

theorem PennyGraph.three_boundary_plus_joins_le_five_K {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) :
    3*(G.terminalBoundaryEndCount : ℤ)+G.terminalJoinCount ≤
      5*(componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).K := by
  have htracks : (G.terminalTrackComponents.card : ℤ) =
      (G.terminalBoundaryEndCount : ℤ)+G.terminalJoinCount := by
    exact_mod_cast G.terminal_tracks_boundary_add_joins ht
  have hports : 5*(G.faceDefectCount ht : ℤ) ≤
      (G.terminalBoundaryEndCount : ℤ)+2*G.terminalJoinCount := by
    exact_mod_cast G.five_defects_le_boundary_add_twice_joins ht
  rw [G.componentSystem_K_eq]
  omega

theorem PennyGraph.three_boundary_ends_le_five_K {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) :
    3*(G.terminalBoundaryEndCount : ℤ) ≤
      5*(componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).K := by
  have h := G.three_boundary_plus_joins_le_five_K ht
  have hJ : (0 : ℤ) ≤ G.terminalJoinCount := Nat.cast_nonneg _
  omega

end Swanepoel
