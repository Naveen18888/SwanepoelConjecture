module
public import Swanepoel.L38HalfGraph
public import Swanepoel.FacePortIncidence
@[expose] public section

noncomputable section
namespace Swanepoel
open Set
attribute [local instance] Classical.propDecidable
namespace OrdinaryCutBanks
variable {n : ℕ} {G : PennyGraph n} {cut : TrackComponent G} (B : OrdinaryCutBanks G cut)

theorem point_not_mem_halfGraph (side : Bool) (v : Fin n) (hv : v∉B.bankVertices side) :
    G.point v∉(B.halfGraph side).drawing := by
  rintro (⟨i,hi⟩ | hz)
  · change G.point (B.halfVertex side i)=G.point v at hi
    exact hv ((G.point_injective hi) ▸ B.halfVertex_mem side i)
  · obtain ⟨e,t,ht,heq⟩ := Set.mem_iUnion.mp hz
    change G.edgePoint (B.halfEdge side e).val.1 (B.halfEdge side e).val.2 t=G.point v at heq
    by_cases h0 : t=0
    · simp only [h0,PennyGraph.edgePoint,sub_zero,one_smul,zero_smul,add_zero] at heq
      exact hv ((G.point_injective heq) ▸ B.halfVertex_mem side e.val.1)
    by_cases h1 : t=1
    · simp only [h1,PennyGraph.edgePoint,sub_self,zero_smul,one_smul,zero_add] at heq
      exact hv ((G.point_injective heq) ▸ B.halfVertex_mem side e.val.2)
    exact G.edgePoint_ne_vertex _ _ v (B.halfEdge side e).property
      (lt_of_le_of_ne ht.1 (Ne.symm h0)) (lt_of_le_of_ne ht.2 h1) heq

theorem omitted_edge_prefix_off_half (side : Bool) (e : OrientedEdge G)
    (ha : e.val.1∉B.bankVertices side) {t : ℝ} (ht0 : 0≤t) (ht1 : t<1) :
    G.edgePoint e.val.1 e.val.2 t∉(B.halfGraph side).drawing := by
  by_cases h0 : t=0
  · simpa only [h0,PennyGraph.edgePoint,sub_zero,one_smul,zero_smul,add_zero] using
      B.point_not_mem_halfGraph side e.val.1 ha
  have ht : 0<t := lt_of_le_of_ne ht0 (Ne.symm h0)
  rintro (⟨i,hi⟩ | hz)
  · exact G.edgePoint_ne_vertex _ _ (B.halfVertex side i) e.property ht ht1 hi.symm
  · obtain ⟨f,r,hr,heq⟩ := Set.mem_iUnion.mp hz
    change G.edgePoint (B.halfEdge side f).val.1 (B.halfEdge side f).val.2 r=
      G.edgePoint e.val.1 e.val.2 t at heq
    have hp := G.interior_edge_intersection _ _ _ _ e.property (B.halfEdge side f).property
      ht ht1 hr.1 hr.2 heq.symm
    rcases Sym2.eq_iff.mp hp with hp | hp
    · apply ha
      rw [hp.1]
      exact B.halfVertex_mem side f.val.1
    · apply ha
      rw [hp.1]
      exact B.halfVertex_mem side f.val.2

theorem omitted_edge_initial_segment (side : Bool) (e : OrientedEdge G)
    (ha : e.val.1∉B.bankVertices side) {r : ℝ} (hr0 : 0≤r) (hr1 : r<1) :
    segment ℝ (G.point e.val.1) (G.edgePoint e.val.1 e.val.2 r)⊆(B.halfGraph side).drawingᶜ := by
  intro z hz
  rw [segment_eq_image] at hz
  obtain ⟨u,hu,rfl⟩ := hz
  have heq : (1-u) • G.point e.val.1+u • G.edgePoint e.val.1 e.val.2 r=
      G.edgePoint e.val.1 e.val.2 (u*r) := by unfold PennyGraph.edgePoint; module
  change (1-u) • G.point e.val.1+u • G.edgePoint e.val.1 e.val.2 r∈(B.halfGraph side).drawingᶜ
  rw [heq]
  exact B.omitted_edge_prefix_off_half side e ha (mul_nonneg hu.1 hr0)
    ((mul_le_of_le_one_left hr0 hu.2).trans_lt hr1)

theorem deleted_edgeTrace_subset_complement (side : Bool) (e : OrientedEdge G)
    (ha : e.val.1∉B.bankVertices side) (hb : e.val.2∉B.bankVertices side) :
    G.edgeTrace e.val.1 e.val.2⊆(B.halfGraph side).drawingᶜ := by
  rintro z ⟨r,hr,rfl⟩
  by_cases h1 : r=1
  · change G.edgePoint e.val.1 e.val.2 r∉(B.halfGraph side).drawing
    simpa only [h1,PennyGraph.edgePoint,sub_self,zero_smul,one_smul,zero_add] using
      B.point_not_mem_halfGraph side e.val.2 hb
  · exact B.omitted_edge_prefix_off_half side e ha hr.1 (lt_of_le_of_ne hr.2 h1)

theorem cut_spine_subset_half_complement (ht : G.TriangleFree) (side : Bool) :
    trackSpineTrace cut⊆(B.halfGraph side).drawingᶜ := by
  intro z hz hdraw
  rcases hdraw with ⟨i,rfl⟩ | hdraw
  · exact G.vertex_not_on_track_spine ht cut (B.halfVertex side i) hz
  · obtain ⟨e,he⟩ := Set.mem_iUnion.mp hdraw
    exact Set.disjoint_left.mp (edgeTrace_disjoint_other_spine ht (B.halfEdge side e) cut
      (B.halfEdge_ne_cut ht side e)) he hz

theorem cut_spine_component_unbounded (ht : G.TriangleFree)
    (hcut : cut∈G.ordinaryTrackComponents) (side : Bool) {z : Plane} (hz : z∈trackSpineTrace cut) :
    ¬Bornology.IsBounded (connectedComponentIn (B.halfGraph side).drawingᶜ z) := by
  have htrace : B.spine.toPlane.trace=trackSpineTrace cut := by
    rw [B.spine.complete_trace ht B.source B.sink,B.component]
  have hpre : IsPreconnected (trackSpineTrace cut) := htrace ▸ B.spine.toPlane.trace_preconnected
  have hcenter : edgeCenter B.start∈trackSpineTrace cut := Or.inl ⟨B.start,B.component,rfl⟩
  have hface := ((G.ordinary_iff_sourceFace_eq_outer cut B.outer B.outer_unbounded).mp hcut)
    B.start B.source B.component
  have hprobe : G.sourceProbe B.start∈B.outer.val := by
    rw [← hface]
    exact G.sourceProbe_mem_sourceFace B.start
  have hout : B.outer.val⊆(B.halfGraph side).drawingᶜ := by
    intro w hw hd
    exact G.face_subset_complement B.outer hw (B.halfGraph_drawing_subset side hd)
  have hseg : segment ℝ (edgeCenter B.start) (G.sourceProbe B.start)⊆(B.halfGraph side).drawingᶜ := by
    intro w hw
    rcases G.source_probe_connector_subset B.start hw with hw | hw
    · exact B.cut_spine_subset_half_complement ht side (Set.mem_singleton_iff.mp hw ▸ hcenter)
    · exact hout (hface ▸ hw)
  have hpre1 : IsPreconnected (trackSpineTrace cut∪segment ℝ (edgeCenter B.start) (G.sourceProbe B.start)) :=
    hpre.union' ⟨edgeCenter B.start,hcenter,left_mem_segment ℝ _ _⟩
    (convex_segment (𝕜 := ℝ) _ _).isPreconnected
  have hpre2 : IsPreconnected ((trackSpineTrace cut∪segment ℝ (edgeCenter B.start) (G.sourceProbe B.start))∪B.outer.val) :=
    hpre1.union' ⟨G.sourceProbe B.start,Or.inr (right_mem_segment ℝ _ _),hprobe⟩
    (G.face_preconnected B.outer)
  have hsub : (trackSpineTrace cut∪segment ℝ (edgeCenter B.start) (G.sourceProbe B.start))∪
      B.outer.val⊆(B.halfGraph side).drawingᶜ :=
    Set.union_subset (Set.union_subset (B.cut_spine_subset_half_complement ht side) hseg) hout
  intro hbounded
  apply B.outer_unbounded
  exact hbounded.subset (fun w hw => hpre2.subset_connectedComponentIn
    (Or.inl (Or.inl hz)) hsub (Or.inr hw))

theorem deleted_cut_endpoint_unbounded (ht : G.TriangleFree)
    (hcut : cut∈G.ordinaryTrackComponents) (side : Bool) (e : OrientedEdge G)
    (he : edgeComponent e=cut) (ha : e.val.1∉B.bankVertices side) :
    ¬Bornology.IsBounded (connectedComponentIn (B.halfGraph side).drawingᶜ (G.point e.val.1)) := by
  have hseg := B.omitted_edge_initial_segment side e ha (r := 1/2) (by norm_num) (by norm_num)
  rw [← edgeCenter_eq_midpoint] at hseg
  have hsame := ((convex_segment (𝕜 := ℝ) (G.point e.val.1) (edgeCenter e)).isPreconnected).subset_connectedComponentIn
    (right_mem_segment ℝ _ _) hseg (left_mem_segment ℝ _ _)
  rw [← connectedComponentIn_eq hsame]
  exact B.cut_spine_component_unbounded ht hcut side (Or.inl ⟨e,he,rfl⟩)

theorem bankVertices_nonempty (ht : G.TriangleFree) (side : Bool) : (B.bankVertices side).Nonempty := by
  have hne := B.cut_vertexBankCode_ne ht B.start B.component
  by_cases ha : B.vertexBankCode B.start.val.1=side
  · exact ⟨B.start.val.1,(B.mem_bankVertices side _).mpr ha⟩
  · refine ⟨B.start.val.2,(B.mem_bankVertices side _).mpr ?_⟩
    cases ha' : B.vertexBankCode B.start.val.1 <;>
      cases hb' : B.vertexBankCode B.start.val.2 <;> cases side <;> simp_all

theorem deleted_vertex_component_unbounded (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hcut : cut∈G.ordinaryTrackComponents) (side : Bool) (v : Fin n)
    (hv : v∉B.bankVertices side) :
    ¬Bornology.IsBounded (connectedComponentIn (B.halfGraph side).drawingᶜ (G.point v)) := by
  have hwalk : ∀ {a b : Fin n},G.graph.Walk a b → b∈B.bankVertices side → a∉B.bankVertices side →
      ¬Bornology.IsBounded (connectedComponentIn (B.halfGraph side).drawingᶜ (G.point a)) := by
    intro a b p
    induction p with
    | nil => exact fun ha hn => False.elim (hn ha)
    | @cons a b c hab p ih =>
      intro hc ha
      let e : OrientedEdge G := ⟨(a,b),hab⟩
      by_cases hb : b∈B.bankVertices side
      · have he : edgeComponent e=cut := by
          by_contra hne
          have hsame := B.noncut_vertexBankCode_eq ht e hne
          exact ha ((B.mem_bankVertices side a).mpr
            (hsame.trans ((B.mem_bankVertices side b).mp hb)))
        exact B.deleted_cut_endpoint_unbounded ht hcut side e he ha
      · have hsub := B.deleted_edgeTrace_subset_complement side e ha hb
        have hpre : IsPreconnected (G.edgeTrace a b) :=
          isPreconnected_Icc.image (G.edgePoint a b) (G.continuous_edgePoint a b).continuousOn
        have haE : G.point a∈G.edgeTrace a b := ⟨0,⟨by norm_num,by norm_num⟩,by simp [PennyGraph.edgePoint]⟩
        have hbE : G.point b∈G.edgeTrace a b := ⟨1,⟨by norm_num,by norm_num⟩,by simp [PennyGraph.edgePoint]⟩
        have heq := connectedComponentIn_eq (hpre.subset_connectedComponentIn haE hsub hbE)
        rw [heq]
        exact ih hc hb
  obtain ⟨w,hw⟩ := B.bankVertices_nonempty ht side
  obtain ⟨p⟩ := hc.preconnected v w
  exact hwalk p hw hv

theorem deleted_drawing_component_unbounded (ht : G.TriangleFree) (hc : G.graph.Connected)
    (hcut : cut∈G.ordinaryTrackComponents) (side : Bool) (z : Plane)
    (hz : z∈G.drawing) (hzH : z∉(B.halfGraph side).drawing) :
    ¬Bornology.IsBounded (connectedComponentIn (B.halfGraph side).drawingᶜ z) := by
  rcases hz with ⟨v,rfl⟩ | hz
  · exact B.deleted_vertex_component_unbounded ht hc hcut side v
      (fun hv => hzH (B.halfGraph_vertex_mem side v hv))
  · obtain ⟨e,r,hr,rfl⟩ := Set.mem_iUnion.mp hz
    have helper (e : OrientedEdge G) {r : ℝ} (hr0 : 0≤r) (hr1 : r≤1)
        (ha : e.val.1∉B.bankVertices side)
        (hzoff : G.edgePoint e.val.1 e.val.2 r∉(B.halfGraph side).drawing) :
        ¬Bornology.IsBounded (connectedComponentIn (B.halfGraph side).drawingᶜ
          (G.edgePoint e.val.1 e.val.2 r)) := by
      by_cases h1 : r=1
      · simp only [h1,PennyGraph.edgePoint,sub_self,zero_smul,one_smul,zero_add] at hzoff ⊢
        exact B.deleted_vertex_component_unbounded ht hc hcut side e.val.2
          (fun hb => hzoff (B.halfGraph_vertex_mem side _ hb))
      · have hseg := B.omitted_edge_initial_segment side e ha hr0 (lt_of_le_of_ne hr1 h1)
        have heq := connectedComponentIn_eq
          ((convex_segment (𝕜 := ℝ) _ _).isPreconnected.subset_connectedComponentIn
            (left_mem_segment ℝ _ _) hseg (right_mem_segment ℝ _ _))
        rw [← heq]
        exact B.deleted_vertex_component_unbounded ht hc hcut side _ ha
    by_cases ha : e.val.1∈B.bankVertices side
    · have hb : e.val.2∉B.bankVertices side := fun hb =>
        hzH (B.halfGraph_edgeTrace_subset side e ha hb ⟨r,hr,rfl⟩)
      have hrev := G.edgePoint_reverse e.val.1 e.val.2 r
      rw [← hrev] at hzH ⊢
      exact helper (reverseEdge e) (by linarith only [hr.2]) (by linarith only [hr.1]) hb hzH
    · exact helper e hr.1 hr.2 ha hzH

end OrdinaryCutBanks
end Swanepoel
