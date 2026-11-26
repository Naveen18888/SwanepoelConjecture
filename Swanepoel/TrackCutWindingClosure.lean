module
public import Swanepoel.TrackCutWindingPolyline
@[expose] public section

noncomputable section
namespace Swanepoel

private theorem segment_center_leftHalfBall (u p z : Plane) {r : ℝ} (hr : 0<r)
    (hz : z∈leftHalfBall u p r) :
    segment ℝ p z⊆{p}∪leftHalfBall u p r := by
  intro w hw
  have hball := ((convex_ball p r).segment_subset (Metric.mem_ball_self hr) hz.1) hw
  rw [segment_eq_image] at hw
  obtain ⟨t,⟨ht0,ht1⟩,rfl⟩ := hw
  by_cases ht : t=0
  · left
    simp [ht]
  · right
    refine ⟨hball,?_⟩
    have hs := hz.2
    simp only [Set.mem_ofPred_eq] at hs ⊢
    rw [cross2_add_right,cross2_smul_right,cross2_smul_right]
    nlinarith [mul_pos (lt_of_le_of_ne ht0 (Ne.symm ht)) (sub_pos.mpr hs)]

private theorem segment_center_rightHalfBall (u p z : Plane) {r : ℝ} (hr : 0<r)
    (hz : z∈rightHalfBall u p r) :
    segment ℝ p z⊆{p}∪rightHalfBall u p r := by
  intro w hw
  have hball := ((convex_ball p r).segment_subset (Metric.mem_ball_self hr) hz.1) hw
  rw [segment_eq_image] at hw
  obtain ⟨t,⟨ht0,ht1⟩,rfl⟩ := hw
  by_cases ht : t=0
  · left
    simp [ht]
  · right
    refine ⟨hball,?_⟩
    have hs := hz.2
    simp only [Set.mem_ofPred_eq] at hs ⊢
    rw [cross2_add_right,cross2_smul_right,cross2_smul_right]
    nlinarith [mul_pos (lt_of_le_of_ne ht0 (Ne.symm ht)) (sub_pos.mpr hs)]

theorem PennyGraph.midpoint_probe_segment_subset {n : ℕ} (G : PennyGraph n)
    (S : Finset (ContactEdge G)) (e : ContactEdge G) (he : e∉S) (left : Bool) :
    segment ℝ (G.edgePoint e.val.1 e.val.2 (1/2)) (G.edgeSidePoint S e left (1/2))⊆
      {G.edgePoint e.val.1 e.val.2 (1/2)}∪
        connectedComponentIn (G.subdrawing (insert e S))ᶜ (G.edgeSidePoint S e left (1/2)) := by
  let m := G.edgePoint e.val.1 e.val.2 (1/2)
  let d := G.edgeClearance S e (1/2)
  have hd : 0<d := (G.edgeClearance_spec S e he (t := 1/2) (by norm_num) (by norm_num)).1
  have hu : ‖G.point e.val.2-G.point e.val.1‖=1 := by
    simpa only [← dist_eq_norm] using e.property.2.symm.2
  have hm := normal_offset_mem_halfBalls _ m hu hd
  have hf := G.edge_sides_in_fixed_components S e he (t := 1/2) (by norm_num) (by norm_num)
  cases left
  · exact (segment_center_rightHalfBall _ _ _ (by positivity : 0<2*d) hm.2).trans
      (Set.union_subset_union_right _ hf.2)
  · exact (segment_center_leftHalfBall _ _ _ (by positivity : 0<2*d) hm.1).trans
      (Set.union_subset_union_right _ hf.1)

theorem edgeCenter_eq_midpoint {n : ℕ} {G : PennyGraph n} (e : OrientedEdge G) :
    edgeCenter e=G.edgePoint e.val.1 e.val.2 (1/2) := by
  dsimp [edgeCenter,RhombusCell.midpoint2,PennyGraph.edgePoint]
  module

theorem PennyGraph.source_probe_connector_subset {n : ℕ} (G : PennyGraph n)
    (e : OrientedEdge G) :
    segment ℝ (edgeCenter e) (G.sourceProbe e)⊆{edgeCenter e}∪(G.sourceFace e).val := by
  have h := G.midpoint_probe_segment_subset (G.sourceProbeDrawing e) (physicalEdge e)
    (by simp [PennyGraph.sourceProbeDrawing]) (sourceProbeSide e)
  simpa only [PennyGraph.sourceProbeDrawing,Finset.insert_erase (Finset.mem_univ _),
    G.subdrawing_univ,physicalEdge_midpoint,PennyGraph.sourceFace,PennyGraph.sourceProbe,
    edgeCenter_eq_midpoint] using h

theorem positive_spine_planeChain {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    {s t : OrientedEdge G}
    (hst : Relation.ReflTransGen PositiveCellStep s t) :
    ∃ p : PlaneChain (edgeCenter s) (edgeCenter t),
      p.trace={edgeCenter s}∪positiveSpineTrace s t := by
  induction hst with
  | refl => exact ⟨.nil _,by simp [PlaneChain.trace,positiveSpineTrace_refl]⟩
  | @tail e f hse hef ih =>
    obtain ⟨p,hp⟩ := ih
    refine ⟨p.append (PlaneChain.single (edgeCenter e) (edgeCenter f)),?_⟩
    rw [PlaneChain.trace_append,PlaneChain.trace_single,hp,
      positiveSpineTrace_tail ht hse hef,Set.union_assoc]

theorem complete_spine_trace_with_start {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    {s t : OrientedEdge G} (hs : ¬∃g, PositiveCellStep g s)
    (htop : ¬∃g, PositiveCellStep t g) (hst : Relation.ReflTransGen PositiveCellStep s t) :
    trackSpineTrace (edgeComponent s)={edgeCenter s}∪positiveSpineTrace s t := by
  have hall : ∀ e, edgeComponent e=edgeComponent s ↔ OnUnorientedSpine s t e := by
    intro e
    constructor
    · intro he
      exact (unoriented_track_iff ht hs htop (Quotient.exact he)).mpr
        (Or.inl ⟨Relation.ReflTransGen.refl,hst⟩)
    · exact onUnorientedSpine_component ⟨Relation.ReflTransGen.refl,hst⟩
  by_cases heq : s=t
  · subst t
    have hcenters (e : OrientedEdge G) (he : edgeComponent e=edgeComponent s) :
        edgeCenter e=edgeCenter s := by
      rcases (hall e).mp he with h | h
      · rw [onSpine_refl_eq h]
      · have hh := congrArg edgeCenter (onSpine_refl_eq (onSpine_reverse_iff.mp h))
        simpa only [edgeCenter_reverse] using hh
    rw [positiveSpineTrace_refl,Set.union_empty]
    ext z
    constructor
    · rintro (⟨e,he,rfl⟩ | ⟨a,b,ha,hab,hz⟩)
      · exact hcenters e he
      · have hb : edgeComponent b=edgeComponent s :=
          (positive_path_component (Relation.ReflTransGen.single hab)).symm.trans ha
        simpa only [hcenters a ha,hcenters b hb,segment_same,Set.mem_singleton_iff] using hz
    · intro hz
      exact Or.inl ⟨s,rfl,hz⟩
  · have htrans : Relation.TransGen PositiveCellStep s t := by
      rcases Relation.reflTransGen_iff_eq_or_transGen.mp hst with h | h
      · exact False.elim (heq h.symm)
      · exact h
    rw [complete_spine_trace ht hs htop htrans hall]
    exact (Set.union_eq_right.mpr (Set.singleton_subset_iff.mpr
      (onSpine_center_mem_trace htrans ⟨Relation.ReflTransGen.refl,hst⟩))).symm

theorem PennyGraph.ordinary_spine_closed_chain {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree)
    {s t : OrientedEdge G} (hs : ¬∃g, PositiveCellStep g s)
    (htop : ¬∃g, PositiveCellStep t g) (hst : Relation.ReflTransGen PositiveCellStep s t)
    (hord : edgeComponent s∈G.ordinaryTrackComponents) :
    ∃ outer : PlaneFace G, ¬Bornology.IsBounded outer.val ∧
      ∃ p : PlaneChain (edgeCenter s) (edgeCenter s),
        trackSpineTrace (edgeComponent s)⊆p.trace ∧
        p.trace⊆trackSpineTrace (edgeComponent s)∪outer.val := by
  have hrt : SpineSource (reverseEdge t) := by
    rintro ⟨g,hg⟩
    have hh := hg.reverse
    simp only [reverseEdge_involutive] at hh
    exact htop ⟨reverseEdge g,hh⟩
  have hrtc : edgeComponent (reverseEdge t)=edgeComponent s :=
    (reverse_component t).symm.trans (positive_path_component hst).symm
  obtain ⟨outer,houter,_⟩ := G.exists_unique_outer_face
  have hfaces := (G.ordinary_iff_sourceFace_eq_outer (edgeComponent s) outer houter).mp hord
  have hsF := hfaces s hs rfl
  have htF := hfaces (reverseEdge t) hrt hrtc
  have hsp : G.sourceProbe s∈outer.val := by rw [← hsF]; exact G.sourceProbe_mem_sourceFace s
  have htp : G.sourceProbe (reverseEdge t)∈outer.val := by rw [← htF]; exact G.sourceProbe_mem_sourceFace _
  obtain ⟨ext,hext⟩ := planeChain_of_segment_reachable htp (G.face_segment_reachable outer htp hsp)
  obtain ⟨spine,hspine⟩ := positive_spine_planeChain ht hst
  have hfull : spine.trace=trackSpineTrace (edgeComponent s) :=
    hspine.trans (complete_spine_trace_with_start ht hs htop hst).symm
  let finish := PlaneChain.single (edgeCenter t) (G.sourceProbe (reverseEdge t))
  let start := PlaneChain.single (G.sourceProbe s) (edgeCenter s)
  let p := ((spine.append finish).append ext).append start
  refine ⟨outer,houter,p,?_,?_⟩
  · rw [← hfull]
    simp only [p,PlaneChain.trace_append]
    exact Set.subset_union_left.trans (Set.subset_union_left.trans Set.subset_union_left)
  · have hsConn := G.source_probe_connector_subset s
    have htConn := G.source_probe_connector_subset (reverseEdge t)
    rw [hsF] at hsConn
    rw [htF,edgeCenter_reverse] at htConn
    have hsCenter : edgeCenter s∈trackSpineTrace (edgeComponent s) := Or.inl ⟨s,rfl,rfl⟩
    have htCenter : edgeCenter t∈trackSpineTrace (edgeComponent s) :=
      Or.inl ⟨t,(positive_path_component hst).symm,rfl⟩
    simp only [p,PlaneChain.trace_append,finish,start,PlaneChain.trace_single]
    refine Set.union_subset (Set.union_subset (Set.union_subset
      (hfull.subset.trans Set.subset_union_left) ?_) (hext.trans Set.subset_union_right)) ?_
    · exact htConn.trans (Set.union_subset (Set.singleton_subset_iff.mpr (Or.inl htCenter)) Set.subset_union_right)
    · rw [segment_symm]
      exact hsConn.trans (Set.union_subset (Set.singleton_subset_iff.mpr (Or.inl hsCenter)) Set.subset_union_right)

end Swanepoel
