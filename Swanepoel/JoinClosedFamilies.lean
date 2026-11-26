module
public import Swanepoel.TerminalPortConservation
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

structure PennyGraph.IsJoinClosed {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree)
    (Y : Finset (PlaneFace G)) : Prop where
  subset_defects : Y ⊆ G.defectPlaneFaces ht
  other_bounded_end : ∀ e f : OrientedEdge G, SpineSource e → SpineSource f →
    edgeComponent e = edgeComponent f → G.sourceFace e ∈ Y →
      G.sourceFace f ∈ G.defectPlaneFaces ht → G.sourceFace f ∈ Y

theorem PennyGraph.joinClosed_empty {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree) :
    G.IsJoinClosed ht ∅ := by
  refine ⟨Finset.empty_subset _, ?_⟩
  intro e f he hf hc hy hdef
  exact False.elim (Finset.notMem_empty _ hy)

theorem PennyGraph.joinClosed_all_defects {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree) :
    G.IsJoinClosed ht (G.defectPlaneFaces ht) :=
  ⟨Finset.Subset.refl _, fun _ _ _ _ _ _ hdef => hdef⟩

theorem PennyGraph.IsJoinClosed.union {n : ℕ} {G : PennyGraph n} {ht : G.TriangleFree}
    {Y Z : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y) (hZ : G.IsJoinClosed ht Z) :
    G.IsJoinClosed ht (Y ∪ Z) := by
  refine ⟨Finset.union_subset hY.subset_defects hZ.subset_defects, ?_⟩
  intro e f he hf hc hy hdef
  rcases Finset.mem_union.mp hy with hy | hz
  · exact Finset.mem_union_left _ (hY.other_bounded_end e f he hf hc hy hdef)
  · exact Finset.mem_union_right _ (hZ.other_bounded_end e f he hf hc hz hdef)

theorem PennyGraph.IsJoinClosed.inter {n : ℕ} {G : PennyGraph n} {ht : G.TriangleFree}
    {Y Z : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y) (hZ : G.IsJoinClosed ht Z) :
    G.IsJoinClosed ht (Y ∩ Z) := by
  refine ⟨(Finset.inter_subset_left).trans hY.subset_defects, ?_⟩
  intro e f he hf hc hy hdef
  exact Finset.mem_inter.mpr
    ⟨hY.other_bounded_end e f he hf hc (Finset.mem_inter.mp hy).1 hdef,
      hZ.other_bounded_end e f he hf hc (Finset.mem_inter.mp hy).2 hdef⟩

theorem PennyGraph.IsJoinClosed.sdiff {n : ℕ} {G : PennyGraph n} {ht : G.TriangleFree}
    {Y Z : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y) (hZ : G.IsJoinClosed ht Z) :
    G.IsJoinClosed ht (Y \ Z) := by
  refine ⟨(Finset.sdiff_subset).trans hY.subset_defects, ?_⟩
  intro e f he hf hc hy hdef
  have heY := (Finset.mem_sdiff.mp hy).1
  have heZ := (Finset.mem_sdiff.mp hy).2
  refine Finset.mem_sdiff.mpr ⟨hY.other_bounded_end e f he hf hc heY hdef, ?_⟩
  intro hfZ
  exact heZ (hZ.other_bounded_end f e hf he hc.symm hfZ (hY.subset_defects heY))

def PennyGraph.familyTrackComponents {n : ℕ} (G : PennyGraph n) (Y : Finset (PlaneFace G)) :
    Finset (TrackComponent G) := (G.familySourcePorts Y).image edgeComponent

def PennyGraph.familySourceEnds {n : ℕ} (G : PennyGraph n) (Y : Finset (PlaneFace G)) :
    Finset (OrientedEdge G) :=
  Finset.univ.filter (fun e => SpineSource e ∧ edgeComponent e ∈ G.familyTrackComponents Y)

def PennyGraph.familyOuterSourceEnds {n : ℕ} (G : PennyGraph n) (Y : Finset (PlaneFace G)) :
    Finset (OrientedEdge G) :=
  (G.familySourceEnds Y).filter (fun e => ¬ Bornology.IsBounded (G.sourceFace e).val)

def PennyGraph.familyBoundaryEndCount {n : ℕ} (G : PennyGraph n) (Y : Finset (PlaneFace G)) : ℕ :=
  (G.familyOuterSourceEnds Y).card

def PennyGraph.familyBoundaryTrackComponents {n : ℕ} (G : PennyGraph n) (Y : Finset (PlaneFace G)) :
    Finset (TrackComponent G) := (G.familyOuterSourceEnds Y).image edgeComponent

def PennyGraph.familyJoinTrackComponents {n : ℕ} (G : PennyGraph n) (Y : Finset (PlaneFace G)) :
    Finset (TrackComponent G) := G.familyTrackComponents Y \ G.familyBoundaryTrackComponents Y

def PennyGraph.familyJoinCount {n : ℕ} (G : PennyGraph n) (Y : Finset (PlaneFace G)) : ℕ :=
  (G.familyJoinTrackComponents Y).card

def PennyGraph.familyK {n : ℕ} (G : PennyGraph n) (Y : Finset (PlaneFace G)) : ℤ :=
  ((G.familyTrackComponents Y).card : ℤ)-2*Y.card

def PennyGraph.familyPortExcess {n : ℕ} (G : PennyGraph n) (Y : Finset (PlaneFace G)) : ℤ :=
  Y.sum (fun F => ((G.faceSourcePorts F).card : ℤ)-4)

theorem PennyGraph.familyTrackComponents_subset_terminal {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y) :
    G.familyTrackComponents Y ⊆ G.terminalTrackComponents := by
  intro c hc
  obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hc
  have hep := (Finset.mem_filter.mp he).2
  exact (G.terminal_iff_defect_source ht _).mpr
    ⟨e,hep.1,rfl,hY.subset_defects hep.2⟩

theorem PennyGraph.familySourceEnds_count {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (Y : Finset (PlaneFace G)) :
    (G.familySourceEnds Y).card = 2*(G.familyTrackComponents Y).card := by
  rw [Finset.card_eq_sum_card_fiberwise
    (f := edgeComponent) (s := G.familySourceEnds Y) (t := G.familyTrackComponents Y)
    (fun e he => (Finset.mem_filter.mp he).2.2)]
  have hsum : (∑ c ∈ G.familyTrackComponents Y,
      ((G.familySourceEnds Y).filter (fun e => edgeComponent e = c)).card) =
      ∑ _ ∈ G.familyTrackComponents Y, 2 := by
    apply Finset.sum_congr rfl
    intro c hc
    have hf : (G.familySourceEnds Y).filter (fun e => edgeComponent e = c) =
        Finset.univ.filter (fun e => SpineSource e ∧ edgeComponent e = c) := by
      ext e
      simp only [PennyGraph.familySourceEnds, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨he,_⟩,hec⟩
        exact ⟨he,hec⟩
      · rintro ⟨he,hec⟩
        exact ⟨⟨he,hec ▸ hc⟩,hec⟩
    rw [hf, component_source_count ht c]
  rw [hsum]
  simp [Nat.mul_comm]

theorem PennyGraph.familySourceEnds_partition {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y) :
    G.familySourceEnds Y = G.familyOuterSourceEnds Y ∪ G.familySourcePorts Y := by
  ext f
  constructor
  · intro hf
    have hfp := (Finset.mem_filter.mp hf).2
    rcases G.sourceFace_defect_or_unbounded ht f hfp.1 with hdef | hout
    · obtain ⟨e,he,hec⟩ := Finset.mem_image.mp hfp.2
      have hep := (Finset.mem_filter.mp he).2
      exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hfp.1,
        hY.other_bounded_end e f hep.1 hfp.1 hec hep.2 hdef⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hf,hout⟩)
  · intro hf
    rcases Finset.mem_union.mp hf with hout | hport
    · exact (Finset.mem_filter.mp hout).1
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hport).2.1,
        Finset.mem_image.mpr ⟨f,hport,rfl⟩⟩

theorem PennyGraph.familySourceEnds_partition_disjoint {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y) :
    Disjoint (G.familyOuterSourceEnds Y) (G.familySourcePorts Y) := by
  apply Finset.disjoint_left.mpr
  intro e hout hport
  exact (Finset.mem_filter.mp hout).2 (G.defectPlaneFace_isBounded ht
    (hY.subset_defects (Finset.mem_filter.mp hport).2.2))

theorem PennyGraph.family_endpoint_conservation {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y) :
    2*(G.familyTrackComponents Y).card = G.familyBoundaryEndCount Y +
      ∑ F ∈ Y, (G.faceSourcePorts F).card := by
  rw [← G.familySourceEnds_count ht Y, G.familySourceEnds_partition ht hY,
    Finset.card_union_of_disjoint (G.familySourceEnds_partition_disjoint ht hY),
    G.familySourcePorts_card]
  rfl

theorem PennyGraph.familyPortExcess_eq {n : ℕ} (G : PennyGraph n) (Y : Finset (PlaneFace G)) :
    G.familyPortExcess Y = (∑ F ∈ Y, ((G.faceSourcePorts F).card : ℤ))-4*Y.card := by
  rw [PennyGraph.familyPortExcess, Finset.sum_sub_distrib]
  simp [mul_comm]

theorem PennyGraph.family_K_port_conservation {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y) :
    2*G.familyK Y = (G.familyBoundaryEndCount Y : ℤ)+G.familyPortExcess Y := by
  have hint : 2*((G.familyTrackComponents Y).card : ℤ) =
      (G.familyBoundaryEndCount Y : ℤ)+∑ F ∈ Y, ((G.faceSourcePorts F).card : ℤ) := by
    exact_mod_cast G.family_endpoint_conservation ht hY
  rw [PennyGraph.familyK, G.familyPortExcess_eq]
  omega

theorem PennyGraph.family_card_le_portExcess {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y) :
    (Y.card : ℤ) ≤ G.familyPortExcess Y := by
  change (Y.card : ℤ) ≤ Y.sum (fun F => ((G.faceSourcePorts F).card : ℤ)-4)
  calc
    _ = ∑ _ ∈ Y, (1 : ℤ) := by simp
    _ ≤ _ := Finset.sum_le_sum (by
      intro F hF
      have hn := G.defect_source_ports_five_le ht F (hY.subset_defects hF)
      have hi : (5 : ℤ) ≤ (G.faceSourcePorts F).card := by exact_mod_cast hn
      linarith)

theorem PennyGraph.family_boundary_add_card_le_twice_K {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y) :
    (G.familyBoundaryEndCount Y : ℤ)+Y.card ≤ 2*G.familyK Y := by
  rw [G.family_K_port_conservation ht hY]
  have h := G.family_card_le_portExcess ht hY
  omega

theorem PennyGraph.family_K_nonneg {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y) :
    0 ≤ G.familyK Y := by
  have h := G.family_boundary_add_card_le_twice_K ht hY
  have hB : (0 : ℤ) ≤ G.familyBoundaryEndCount Y := Nat.cast_nonneg _
  have hcard : (0 : ℤ) ≤ Y.card := Nat.cast_nonneg _
  omega

theorem PennyGraph.family_K_pos {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y)
    (hne : Y.Nonempty) : 0 < G.familyK Y := by
  have h := G.family_boundary_add_card_le_twice_K ht hY
  have hB : (0 : ℤ) ≤ G.familyBoundaryEndCount Y := Nat.cast_nonneg _
  have hcard : (0 : ℤ) < Y.card := by exact_mod_cast hne.card_pos
  omega

theorem PennyGraph.familyOuterSourceEnds_subset_terminal {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y) :
    G.familyOuterSourceEnds Y ⊆ G.terminalOuterSourceEnds := by
  intro e he
  have heouter := (Finset.mem_filter.mp he).2
  have hep := (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hep.1,
    G.familyTrackComponents_subset_terminal ht hY hep.2⟩,heouter⟩

theorem PennyGraph.familyBoundaryTrackComponents_count {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y) :
    (G.familyBoundaryTrackComponents Y).card = G.familyBoundaryEndCount Y :=
  Finset.card_image_of_injOn ((G.terminalOuterSourceEnds_component_injOn ht).mono
    (G.familyOuterSourceEnds_subset_terminal ht hY))

theorem PennyGraph.family_tracks_boundary_add_joins {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y) :
    (G.familyTrackComponents Y).card = G.familyBoundaryEndCount Y+G.familyJoinCount Y := by
  have hsub : G.familyBoundaryTrackComponents Y ⊆ G.familyTrackComponents Y := by
    intro c hc
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hc
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2.2
  have hc := Finset.card_sdiff_add_card_eq_card hsub
  change G.familyJoinCount Y+(G.familyBoundaryTrackComponents Y).card =
    (G.familyTrackComponents Y).card at hc
  rw [G.familyBoundaryTrackComponents_count ht hY] at hc
  omega

theorem PennyGraph.family_ports_boundary_add_twice_joins {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y) :
    (∑ F ∈ Y, (G.faceSourcePorts F).card) = G.familyBoundaryEndCount Y+2*G.familyJoinCount Y := by
  have he := G.family_endpoint_conservation ht hY
  have hp := G.family_tracks_boundary_add_joins ht hY
  omega

theorem PennyGraph.family_three_boundary_plus_joins_le_five_K {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {Y : Finset (PlaneFace G)} (hY : G.IsJoinClosed ht Y) :
    3*(G.familyBoundaryEndCount Y : ℤ)+G.familyJoinCount Y ≤ 5*G.familyK Y := by
  have hlo : 5*Y.card ≤ ∑ F ∈ Y, (G.faceSourcePorts F).card := by
    calc
      _ = ∑ _ ∈ Y, 5 := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun F hF => G.defect_source_ports_five_le ht F (hY.subset_defects hF))
  rw [G.family_ports_boundary_add_twice_joins ht hY] at hlo
  have hports : 5*(Y.card : ℤ) ≤ (G.familyBoundaryEndCount Y : ℤ)+2*G.familyJoinCount Y := by
    exact_mod_cast hlo
  have htracks : ((G.familyTrackComponents Y).card : ℤ) =
      (G.familyBoundaryEndCount Y : ℤ)+G.familyJoinCount Y := by
    exact_mod_cast G.family_tracks_boundary_add_joins ht hY
  rw [PennyGraph.familyK]
  omega

theorem PennyGraph.familyTrackComponents_all_defects {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) :
    G.familyTrackComponents (G.defectPlaneFaces ht) = G.terminalTrackComponents := by
  apply Finset.Subset.antisymm (G.familyTrackComponents_subset_terminal ht (G.joinClosed_all_defects ht))
  intro c hc
  obtain ⟨e,hes,hec,hedef⟩ := (G.terminal_iff_defect_source ht c).mp hc
  exact Finset.mem_image.mpr ⟨e,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hes,hedef⟩,hec⟩

theorem PennyGraph.familyK_all_defects {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree) :
    G.familyK (G.defectPlaneFaces ht) =
      (componentSystem G ht G.ordinaryTrackComponents (G.faceDefectCount ht)).K := by
  rw [PennyGraph.familyK, G.familyTrackComponents_all_defects ht, G.defectPlaneFaces_card ht,
    G.componentSystem_K_eq]

end Swanepoel
