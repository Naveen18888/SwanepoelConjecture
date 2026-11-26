module
public import Swanepoel.JoinClosedFamilies
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

theorem PennyGraph.familyTrackComponents_mono {n : ℕ} (G : PennyGraph n)
    {Y Z : Finset (PlaneFace G)} (hYZ : Y ⊆ Z) :
    G.familyTrackComponents Y ⊆ G.familyTrackComponents Z := by
  intro c hc
  obtain ⟨e,he,hec⟩ := Finset.mem_image.mp hc
  exact Finset.mem_image.mpr ⟨e,Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,(Finset.mem_filter.mp he).2.1,hYZ (Finset.mem_filter.mp he).2.2⟩,hec⟩

theorem PennyGraph.familySourcePorts_union {n : ℕ} (G : PennyGraph n)
    (Y Z : Finset (PlaneFace G)) :
    G.familySourcePorts (Y ∪ Z) = G.familySourcePorts Y ∪ G.familySourcePorts Z := by
  ext e
  simp only [PennyGraph.familySourcePorts, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_union]
  tauto

theorem PennyGraph.familyTrackComponents_union {n : ℕ} (G : PennyGraph n)
    (Y Z : Finset (PlaneFace G)) :
    G.familyTrackComponents (Y ∪ Z) = G.familyTrackComponents Y ∪ G.familyTrackComponents Z := by
  simp only [PennyGraph.familyTrackComponents, G.familySourcePorts_union, Finset.image_union]

theorem PennyGraph.familyTrackComponents_contains_face_edge {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y)
    (e : OrientedEdge G) (he : G.sourceFace e ∈ Y) :
    edgeComponent e ∈ G.familyTrackComponents Y := by
  have hes := G.spineSource_of_sourceFace_mem_defects ht e (hY.subset_defects he)
  exact Finset.mem_image.mpr ⟨e,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hes,he⟩,rfl⟩

theorem PennyGraph.familyJoin_iff_all_ends_in_family {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y)
    (c : TrackComponent G) :
    c ∈ G.familyJoinTrackComponents Y ↔ c ∈ G.familyTrackComponents Y ∧
      ∀ e : OrientedEdge G, SpineSource e → edgeComponent e = c → G.sourceFace e ∈ Y := by
  change c ∈ G.familyTrackComponents Y \ G.familyBoundaryTrackComponents Y ↔ _
  rw [Finset.mem_sdiff]
  constructor
  · rintro ⟨hc,hnot⟩
    refine ⟨hc,?_⟩
    intro e hes hec
    have heends : e ∈ G.familySourceEnds Y := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,hes,hec ▸ hc⟩
    rw [G.familySourceEnds_partition ht hY] at heends
    rcases Finset.mem_union.mp heends with hout | hport
    · exfalso
      exact hnot (Finset.mem_image.mpr ⟨e,hout,hec⟩)
    · exact (Finset.mem_filter.mp hport).2.2
  · rintro ⟨hc,hall⟩
    refine ⟨hc,?_⟩
    intro hbound
    obtain ⟨e,he,hec⟩ := Finset.mem_image.mp hbound
    have hes := (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2.1
    exact (Finset.mem_filter.mp he).2
      (G.defectPlaneFace_isBounded ht (hY.subset_defects (hall e hes hec)))

theorem PennyGraph.familyTrackComponents_disjoint {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y Z : Finset (PlaneFace G)}
    (hY : G.IsJoinClosed ht Y) (hZ : G.IsJoinClosed ht Z) (hYZ : Disjoint Y Z) :
    Disjoint (G.familyTrackComponents Y) (G.familyTrackComponents Z) := by
  apply Finset.disjoint_left.mpr
  intro c hcY hcZ
  obtain ⟨e,he,hec⟩ := Finset.mem_image.mp hcY
  obtain ⟨f,hf,hfc⟩ := Finset.mem_image.mp hcZ
  have hep := (Finset.mem_filter.mp he).2
  have hfp := (Finset.mem_filter.mp hf).2
  have hfY := hY.other_bounded_end e f hep.1 hfp.1 (hec.trans hfc.symm)
    hep.2 (hZ.subset_defects hfp.2)
  exact Finset.disjoint_left.mp hYZ hfY hfp.2

theorem PennyGraph.familyK_union {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y Z : Finset (PlaneFace G)}
    (hY : G.IsJoinClosed ht Y) (hZ : G.IsJoinClosed ht Z) (hYZ : Disjoint Y Z) :
    G.familyK (Y ∪ Z) = G.familyK Y+G.familyK Z := by
  unfold PennyGraph.familyK
  rw [G.familyTrackComponents_union,
    Finset.card_union_of_disjoint (G.familyTrackComponents_disjoint ht hY hZ hYZ),
    Finset.card_union_of_disjoint hYZ]
  push_cast
  ring

theorem PennyGraph.familyPortExcess_union {n : ℕ} (G : PennyGraph n)
    {Y Z : Finset (PlaneFace G)} (hYZ : Disjoint Y Z) :
    G.familyPortExcess (Y ∪ Z) = G.familyPortExcess Y+G.familyPortExcess Z := by
  exact Finset.sum_union hYZ

theorem PennyGraph.familyBoundaryEndCount_union {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y Z : Finset (PlaneFace G)}
    (hY : G.IsJoinClosed ht Y) (hZ : G.IsJoinClosed ht Z) (hYZ : Disjoint Y Z) :
    G.familyBoundaryEndCount (Y ∪ Z) = G.familyBoundaryEndCount Y+G.familyBoundaryEndCount Z := by
  have hU := G.family_K_port_conservation ht (hY.union hZ)
  have hYL := G.family_K_port_conservation ht hY
  have hZL := G.family_K_port_conservation ht hZ
  rw [G.familyK_union ht hY hZ hYZ, G.familyPortExcess_union hYZ] at hU
  omega

theorem PennyGraph.familyJoinCount_union {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y Z : Finset (PlaneFace G)}
    (hY : G.IsJoinClosed ht Y) (hZ : G.IsJoinClosed ht Z) (hYZ : Disjoint Y Z) :
    G.familyJoinCount (Y ∪ Z) = G.familyJoinCount Y+G.familyJoinCount Z := by
  have hU := G.family_tracks_boundary_add_joins ht (hY.union hZ)
  have hYL := G.family_tracks_boundary_add_joins ht hY
  have hZL := G.family_tracks_boundary_add_joins ht hZ
  rw [G.familyTrackComponents_union,
    Finset.card_union_of_disjoint (G.familyTrackComponents_disjoint ht hY hZ hYZ),
    G.familyBoundaryEndCount_union ht hY hZ hYZ] at hU
  omega

theorem PennyGraph.IsJoinClosed.complement {n : ℕ} {G : PennyGraph n}
    {ht : G.TriangleFree} {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y) :
    G.IsJoinClosed ht (G.defectPlaneFaces ht \ Y) :=
  (G.joinClosed_all_defects ht).sdiff hY

theorem PennyGraph.canonical_K_joinClosed_decomposition {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y) :
    (componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).K =
      G.familyK Y+G.familyK (G.defectPlaneFaces ht \ Y) := by
  have hunion : Y ∪ (G.defectPlaneFaces ht \ Y) = G.defectPlaneFaces ht :=
    Finset.union_sdiff_of_subset hY.subset_defects
  have hdis : Disjoint Y (G.defectPlaneFaces ht \ Y) := Finset.disjoint_left.mpr (by
    intro F hFY hFrest
    exact (Finset.mem_sdiff.mp hFrest).2 hFY)
  calc
    _ = G.familyK (G.defectPlaneFaces ht) := (G.familyK_all_defects ht).symm
    _ = G.familyK (Y ∪ (G.defectPlaneFaces ht \ Y)) := congrArg (G.familyK) hunion.symm
    _ = _ := G.familyK_union ht hY hY.complement hdis

theorem PennyGraph.familyK_le_canonical_K {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y) :
    G.familyK Y ≤ (componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).K := by
  rw [G.canonical_K_joinClosed_decomposition ht hY]
  have hnonneg := G.family_K_nonneg ht hY.complement
  omega

end Swanepoel
