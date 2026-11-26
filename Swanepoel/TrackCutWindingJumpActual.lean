module
public import Swanepoel.TrackCutWindingJumpLabels
@[expose] public section

noncomputable section
namespace Swanepoel

theorem positive_path_height_le {n : ℕ} {G : PennyGraph n} {a b : OrientedEdge G}
    (hab : Relation.ReflTransGen PositiveCellStep a b) : edgeHeight a≤edgeHeight b := by
  induction hab with
  | refl => exact le_rfl
  | tail _ h ih => exact ih.trans h.height_lt.le

theorem spine_chain_height_bounds {n : ℕ} {G : PennyGraph n} {s t : OrientedEdge G}
    (hst : Relation.ReflTransGen PositiveCellStep s t) {z : Plane}
    (hz : z∈{edgeCenter s}∪positiveSpineTrace s t) :
    edgeHeight s≤cross2 (carriedVector s) z ∧ cross2 (carriedVector s) z≤edgeHeight t := by
  rcases hz with hz | ⟨a,b,hsa,hab,hbt,hz⟩
  · rw [Set.mem_singleton_iff.mp hz]
    exact ⟨le_rfl,positive_path_height_le hst⟩
  · have hva := positive_path_vector_eq hsa
    have hvb := hva.trans hab.to_cellStep.vector_eq
    have ha : edgeCenter a∈{w : Plane | edgeHeight s≤cross2 (carriedVector s) w ∧
        cross2 (carriedVector s) w≤edgeHeight t} := by
      rw [hva]
      exact ⟨positive_path_height_le hsa,positive_path_height_le ((Relation.ReflTransGen.single hab).trans hbt)⟩
    have hb : edgeCenter b∈{w : Plane | edgeHeight s≤cross2 (carriedVector s) w ∧
        cross2 (carriedVector s) w≤edgeHeight t} := by
      rw [hvb]
      exact ⟨positive_path_height_le (hsa.tail hab),positive_path_height_le hbt⟩
    have hc : Convex ℝ {w : Plane | edgeHeight s≤cross2 (carriedVector s) w ∧
        cross2 (carriedVector s) w≤edgeHeight t} :=
      (convex_Icc _ _).linear_preimage (crossLinear (carriedVector s))
    exact hc.segment_subset ha hb hz

theorem PositiveCellStep.midpoint_height_between {n : ℕ} {G : PennyGraph n}
    {a b : OrientedEdge G} (hab : PositiveCellStep a b) :
    edgeHeight a<cross2 (carriedVector a) (stepCenter a b) ∧
      cross2 (carriedVector a) (stepCenter a b)<edgeHeight b := by
  have heq : cross2 (carriedVector a) (stepCenter a b)=(edgeHeight a+edgeHeight b)/2 := by
    dsimp [stepCenter,RhombusCell.midpoint2,edgeHeight]
    rw [cross2_smul_right,cross2_add_right,← hab.to_cellStep.vector_eq]
    ring
  rw [heq]
  constructor <;> linarith [hab.height_lt]

theorem PennyGraph.ordinary_spine_segment_loop {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree)
    {s t a b : OrientedEdge G} (hs : ¬∃g, PositiveCellStep g s)
    (htop : ¬∃g, PositiveCellStep t g)
    (hsa : Relation.ReflTransGen PositiveCellStep s a) (hab : PositiveCellStep a b)
    (hbt : Relation.ReflTransGen PositiveCellStep b t)
    (hord : edgeComponent s∈G.ordinaryTrackComponents) :
    ∃ outer : PlaneFace G, ¬Bornology.IsBounded outer.val ∧
      ∃ rest : PlaneChain (edgeCenter b) (edgeCenter a),
        stepCenter a b∉rest.trace ∧
        ((PlaneChain.single (edgeCenter a) (edgeCenter b)).append rest).trace⊆
          trackSpineTrace (edgeComponent s)∪outer.val := by
  have hst := (hsa.tail hab).trans hbt
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
  obtain ⟨beforeChain,hprefix⟩ := positive_spine_planeChain ht hsa
  obtain ⟨suffix,hsuffix⟩ := positive_spine_planeChain ht hbt
  let finish := PlaneChain.single (edgeCenter t) (G.sourceProbe (reverseEdge t))
  let start := PlaneChain.single (G.sourceProbe s) (edgeCenter s)
  let rest := (((suffix.append finish).append ext).append start).append beforeChain
  have hmid := hab.midpoint_height_between
  have hbefore : stepCenter a b∉beforeChain.trace := by
    intro hm
    rw [hprefix] at hm
    have hh := (spine_chain_height_bounds hsa hm).2
    rw [positive_path_vector_eq hsa] at hh
    linarith
  have hafter : stepCenter a b∉suffix.trace := by
    intro hm
    rw [hsuffix] at hm
    have hh := (spine_chain_height_bounds hbt hm).1
    rw [← hab.to_cellStep.vector_eq] at hh
    linarith
  have habPos := hab
  obtain ⟨C,he,hf,_⟩ := hab
  have heq : a=C.edgeAB := Subtype.ext he
  have hfq : b=C.edgeDC := Subtype.ext hf
  have hcenter : stepCenter a b=C.center := by rw [heq,hfq,C.stepCenter_eq]
  have hmem : stepCenter a b∈C.openRegion := by
    rw [hcenter,← C.cellPoint_half_eq_center]
    exact C.cellPoint_mem_openRegion ht (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnotDrawing : stepCenter a b∉G.drawing := C.openRegion_subset_complement ht hmem
  have hnotOuter : stepCenter a b∉outer.val := by
    intro ho
    have hface := outer.property.eq_component ho
    have hcell := (C.isBoundedFace ht).1.eq_component hmem
    have heq : outer.val=C.openRegion := hface.trans hcell.symm
    apply houter
    rw [heq]
    exact (C.isBoundedFace ht).2
  have hnotExt : stepCenter a b∉ext.trace := fun hm => hnotOuter (hext hm)
  have hsConn := G.source_probe_connector_subset s
  have htConn := G.source_probe_connector_subset (reverseEdge t)
  rw [hsF] at hsConn
  rw [htF,edgeCenter_reverse] at htConn
  have hnotFinish : stepCenter a b∉finish.trace := by
    rw [PlaneChain.trace_single]
    intro hz
    rcases htConn hz with hz | hz
    · exact hnotDrawing ((Set.mem_singleton_iff.mp hz).symm ▸ G.edgeCenter_mem_drawing t)
    · exact hnotOuter hz
  have hnotStart : stepCenter a b∉start.trace := by
    rw [PlaneChain.trace_single,segment_symm]
    intro hz
    rcases hsConn hz with hz | hz
    · exact hnotDrawing ((Set.mem_singleton_iff.mp hz).symm ▸ G.edgeCenter_mem_drawing s)
    · exact hnotOuter hz
  have hsubPrefix : beforeChain.trace⊆trackSpineTrace (edgeComponent s) := by
    rw [hprefix]
    intro z hz
    rcases hz with hz | ⟨e,f,hse,hef,hfa,hz⟩
    · exact Or.inl ⟨s,rfl,hz⟩
    · exact Or.inr ⟨e,f,(positive_path_component hse).symm,hef,hz⟩
  have hsubSuffix : suffix.trace⊆trackSpineTrace (edgeComponent s) := by
    rw [hsuffix]
    intro z hz
    rcases hz with hz | ⟨e,f,hbe,hef,hft,hz⟩
    · exact Or.inl ⟨b,(positive_path_component (hsa.tail habPos)).symm,hz⟩
    · exact Or.inr ⟨e,f,(positive_path_component ((hsa.tail habPos).trans hbe)).symm,hef,hz⟩
  have hsCenter : edgeCenter s∈trackSpineTrace (edgeComponent s) := Or.inl ⟨s,rfl,rfl⟩
  have htCenter : edgeCenter t∈trackSpineTrace (edgeComponent s) :=
    Or.inl ⟨t,(positive_path_component hst).symm,rfl⟩
  have hsubFinish : finish.trace⊆trackSpineTrace (edgeComponent s)∪outer.val := by
    rw [PlaneChain.trace_single]
    exact htConn.trans (Set.union_subset (Set.singleton_subset_iff.mpr (Or.inl htCenter)) Set.subset_union_right)
  have hsubStart : start.trace⊆trackSpineTrace (edgeComponent s)∪outer.val := by
    rw [PlaneChain.trace_single,segment_symm]
    exact hsConn.trans (Set.union_subset (Set.singleton_subset_iff.mpr (Or.inl hsCenter)) Set.subset_union_right)
  refine ⟨outer,houter,rest,?_,?_⟩
  · simp only [rest,PlaneChain.trace_append,Set.mem_union]
    tauto
  · rw [PlaneChain.trace_append,PlaneChain.trace_single]
    refine Set.union_subset ?_ ?_
    · intro z hz
      exact Or.inl (Or.inr ⟨a,b,(positive_path_component hsa).symm,habPos,hz⟩)
    · simp only [rest,PlaneChain.trace_append]
      exact Set.union_subset (Set.union_subset (Set.union_subset (Set.union_subset
        (hsubSuffix.trans Set.subset_union_left) hsubFinish) (hext.trans Set.subset_union_right))
        hsubStart) (hsubPrefix.trans Set.subset_union_left)

end Swanepoel
