module
public import Swanepoel.DefectBoundary
public import Swanepoel.ContactFaces
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

def ContactEdge.forwardEdge {n : ℕ} {G : PennyGraph n} (e : ContactEdge G) : OrientedEdge G :=
  ⟨e.val, e.property.2⟩

theorem physicalEdge_forwardEdge {n : ℕ} {G : PennyGraph n} (e : ContactEdge G) :
    physicalEdge e.forwardEdge = e := by
  apply Subtype.ext
  simp [physicalEdge, ContactEdge.forwardEdge, e.property.1]

theorem physicalEdge_reverse_forwardEdge {n : ℕ} {G : PennyGraph n} (e : ContactEdge G) :
    physicalEdge (reverseEdge e.forwardEdge) = e := by
  apply Subtype.ext
  simp [physicalEdge, reverseEdge, ContactEdge.forwardEdge, not_lt_of_ge e.property.1.le]

theorem PennyGraph.contact_right_component_eq_sourceFace {n : ℕ} (G : PennyGraph n)
    (e : ContactEdge G) :
    connectedComponentIn G.drawingᶜ
      (G.edgeSidePoint (Finset.univ.erase e) e false (1/2)) = (G.sourceFace e.forwardEdge).val := by
  simp only [PennyGraph.sourceFace, PennyGraph.sourceProbe, PennyGraph.sourceProbeDrawing,
    physicalEdge_forwardEdge]
  simp only [sourceProbeSide, ContactEdge.forwardEdge,
    not_lt_of_ge e.property.1.le, decide_false]

theorem PennyGraph.contact_left_component_eq_sourceFace {n : ℕ} (G : PennyGraph n)
    (e : ContactEdge G) :
    connectedComponentIn G.drawingᶜ
      (G.edgeSidePoint (Finset.univ.erase e) e true (1/2)) =
        (G.sourceFace (reverseEdge e.forwardEdge)).val := by
  simp only [PennyGraph.sourceFace, PennyGraph.sourceProbe, PennyGraph.sourceProbeDrawing,
    physicalEdge_reverse_forwardEdge]
  simp only [sourceProbeSide, ContactEdge.forwardEdge, reverseEdge, e.property.1, decide_true]

theorem PennyGraph.face_subset_complement {n : ℕ} (G : PennyGraph n) (F : PlaneFace G) :
    F.val ⊆ G.drawingᶜ := by
  obtain ⟨x, _, hx⟩ := F.property
  rw [hx]
  exact connectedComponentIn_subset _ _

theorem PennyGraph.face_preconnected {n : ℕ} (G : PennyGraph n) (F : PlaneFace G) :
    IsPreconnected F.val := by
  obtain ⟨x, _, hx⟩ := F.property
  rw [hx]
  exact isPreconnected_connectedComponentIn

private theorem component_closure_within_ambient (U : Set Plane) {p z : Plane}
    (hp : p ∈ U) (hz : z ∈ closure (connectedComponentIn U p)) (hzU : z ∈ U) :
    z ∈ connectedComponentIn U p := by
  rw [connectedComponentIn_eq_image hp] at hz ⊢
  have hc := (Topology.IsInducing.subtypeVal (t := U)).closure_eq_preimage_closure_image
    (connectedComponent (⟨p,hp⟩ : U))
  have hz' : (⟨z,hzU⟩ : U) ∈ closure (connectedComponent (⟨p,hp⟩ : U)) := by
    rw [hc]
    exact hz
  exact ⟨⟨z,hzU⟩, isClosed_connectedComponent.closure_subset hz', rfl⟩

theorem PennyGraph.face_frontier_subset_drawing {n : ℕ} (G : PennyGraph n) (F : PlaneFace G) :
    frontier F.val ⊆ G.drawing := by
  intro z hz
  rw [frontier, F.property.isOpen.interior_eq] at hz
  by_contra hzd
  obtain ⟨x,hx,hF⟩ := F.property
  have hzcl : z ∈ closure (connectedComponentIn G.drawingᶜ x) := by
    rw [← hF]
    exact hz.1
  have hzF := component_closure_within_ambient G.drawingᶜ hx hzcl hzd
  rw [← hF] at hzF
  exact hz.2 hzF

theorem PennyGraph.face_incident_to_open_edge {n : ℕ} (G : PennyGraph n)
    (F : PlaneFace G) (e : ContactEdge G) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hcl : G.edgePoint e.val.1 e.val.2 t ∈ closure F.val) :
    G.sourceFace e.forwardEdge = F ∨ G.sourceFace (reverseEdge e.forwardEdge) = F := by
  let S : Finset (ContactEdge G) := Finset.univ.erase e
  have he : e ∉ S := Finset.notMem_erase _ _
  have hdrawing : G.subdrawing (insert e S) = G.drawing := by
    simp only [S, Finset.insert_erase (Finset.mem_univ _), G.subdrawing_univ]
  have hd := (G.edgeClearance_spec S e he ht0 ht1).1
  have hlocal := G.edgeClearance_ball_complement S e he ht0 ht1
  have hsides := G.edge_sides_in_fixed_components S e he ht0 ht1
  rw [hdrawing] at hlocal hsides
  obtain ⟨y,hyBall,hyF⟩ := mem_closure_iff.mp hcl
    (Metric.ball (G.edgePoint e.val.1 e.val.2 t) (2*G.edgeClearance S e t))
    Metric.isOpen_ball (Metric.mem_ball_self (by linarith))
  have hysides : y ∈
      leftHalfBall (G.point e.val.2-G.point e.val.1) (G.edgePoint e.val.1 e.val.2 t)
        (2*G.edgeClearance S e t) ∪
      rightHalfBall (G.point e.val.2-G.point e.val.1) (G.edgePoint e.val.1 e.val.2 t)
        (2*G.edgeClearance S e t) := by
    rw [← hlocal]
    exact ⟨hyBall, G.face_subset_complement F hyF⟩
  rcases hysides with hyL | hyR
  · right
    apply Subtype.ext
    exact (G.contact_left_component_eq_sourceFace e).symm.trans
      ((connectedComponentIn_eq (hsides.1 hyL)).trans (F.property.eq_component hyF).symm)
  · left
    apply Subtype.ext
    exact (G.contact_right_component_eq_sourceFace e).symm.trans
      ((connectedComponentIn_eq (hsides.2 hyR)).trans (F.property.eq_component hyF).symm)

def PennyGraph.facePortEdges {n : ℕ} (G : PennyGraph n) (F : PlaneFace G) : Finset (ContactEdge G) :=
  (G.faceSourcePorts F).image physicalEdge

theorem PennyGraph.facePortEdges_card_le {n : ℕ} (G : PennyGraph n) (F : PlaneFace G) :
    (G.facePortEdges F).card ≤ (G.faceSourcePorts F).card :=
  Finset.card_image_le

theorem PennyGraph.defect_frontier_subset_port_subdrawing {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (F : PlaneFace G) (hF : F ∈ G.defectPlaneFaces ht) :
    frontier F.val ⊆ G.subdrawing (G.facePortEdges F) := by
  intro z hz
  have hzdraw : z ∈ G.subdrawing Finset.univ := by
    rw [G.subdrawing_univ]
    exact G.face_frontier_subset_drawing F hz
  rcases hzdraw with hzpoint | hzedge
  · exact Or.inl hzpoint
  · obtain ⟨e,he⟩ := Set.mem_iUnion.mp hzedge
    obtain ⟨_,t,⟨ht0,ht1⟩,hparam⟩ := Set.mem_iUnion.mp he
    by_cases htzero : t = 0
    · exact Or.inl ⟨e.val.1, by simpa [PennyGraph.edgePoint, htzero] using hparam⟩
    by_cases htone : t = 1
    · exact Or.inl ⟨e.val.2, by simpa [PennyGraph.edgePoint, htone] using hparam⟩
    have ht0' : 0 < t := lt_of_le_of_ne ht0 (Ne.symm htzero)
    have ht1' : t < 1 := lt_of_le_of_ne ht1 htone
    have hcl : G.edgePoint e.val.1 e.val.2 t ∈ closure F.val := hparam.symm ▸ hz.1
    have heport : e ∈ G.facePortEdges F := by
      rcases G.face_incident_to_open_edge F e ht0' ht1' hcl with hright | hleft
      · have hdef : G.sourceFace e.forwardEdge ∈ G.defectPlaneFaces ht := by rwa [hright]
        apply Finset.mem_image.mpr
        refine ⟨e.forwardEdge, ?_, physicalEdge_forwardEdge e⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          G.spineSource_of_sourceFace_mem_defects ht _ hdef, hright⟩
      · have hdef : G.sourceFace (reverseEdge e.forwardEdge) ∈ G.defectPlaneFaces ht := by rwa [hleft]
        apply Finset.mem_image.mpr
        refine ⟨reverseEdge e.forwardEdge, ?_, physicalEdge_reverse_forwardEdge e⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          G.spineSource_of_sourceFace_mem_defects ht _ hdef, hleft⟩
    exact Or.inr (Set.mem_iUnion.mpr ⟨e, Set.mem_iUnion.mpr ⟨heport, t, ⟨ht0,ht1⟩, hparam⟩⟩)

theorem PennyGraph.face_retained_of_frontier_subset {n : ℕ} (G : PennyGraph n)
    (F : PlaneFace G) (S : Finset (ContactEdge G))
    (hfront : frontier F.val ⊆ G.subdrawing S) : G.IsSubFace S F.val := by
  obtain ⟨x,hx⟩ := F.property.nonempty
  have hFcompl : F.val ⊆ (G.subdrawing S)ᶜ := by
    intro z hz hdraw
    exact G.face_subset_complement F hz (G.subdrawing_subset_drawing S hdraw)
  have hxcompl := hFcompl hx
  let C := connectedComponentIn (G.subdrawing S)ᶜ x
  have hFC : F.val ⊆ C := (G.face_preconnected F).subset_connectedComponentIn hx hFcompl
  have hCF : C ⊆ F.val := by
    apply isPreconnected_connectedComponentIn.subset_of_closure_inter_subset F.property.isOpen
      ⟨x, mem_connectedComponentIn hxcompl, hx⟩
    intro z hz
    by_contra hzF
    have hzfront : z ∈ frontier F.val := by
      rw [frontier, F.property.isOpen.interior_eq]
      exact ⟨hz.1, hzF⟩
    exact (connectedComponentIn_subset _ _ hz.2) (hfront hzfront)
  exact ⟨x, hxcompl, Set.Subset.antisymm hFC hCF⟩

theorem PennyGraph.defect_face_retained_by_source_edges {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (F : PlaneFace G) (hF : F ∈ G.defectPlaneFaces ht) :
    G.IsSubFace (G.facePortEdges F) F.val :=
  G.face_retained_of_frontier_subset F (G.facePortEdges F)
    (G.defect_frontier_subset_port_subdrawing ht F hF)

end Swanepoel
