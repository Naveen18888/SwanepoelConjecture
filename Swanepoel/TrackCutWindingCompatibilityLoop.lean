module
public import Swanepoel.TrackCutWindingCompatibilitySpine
@[expose] public section

noncomputable section
namespace Swanepoel

theorem PennyGraph.ordinary_spine_fixed_exterior {n : ℕ} (G : PennyGraph n)
    {s t : OrientedEdge G} (hs : ¬∃g, PositiveCellStep g s)
    (htop : ¬∃g, PositiveCellStep t g) (hst : Relation.ReflTransGen PositiveCellStep s t)
    (hord : edgeComponent s∈G.ordinaryTrackComponents) :
    ∃ outer : PlaneFace G, ¬Bornology.IsBounded outer.val ∧
      ∃ close : PlaneChain (edgeCenter t) (edgeCenter s),
        close.trace⊆({edgeCenter s,edgeCenter t} : Set Plane)∪outer.val := by
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
  let finish := PlaneChain.single (edgeCenter t) (G.sourceProbe (reverseEdge t))
  let start := PlaneChain.single (G.sourceProbe s) (edgeCenter s)
  let close := (finish.append ext).append start
  have hsConn := G.source_probe_connector_subset s
  have htConn := G.source_probe_connector_subset (reverseEdge t)
  rw [hsF] at hsConn
  rw [htF,edgeCenter_reverse] at htConn
  refine ⟨outer,houter,close,?_⟩
  simp only [close,PlaneChain.trace_append,finish,start,PlaneChain.trace_single]
  refine Set.union_subset (Set.union_subset ?_ (hext.trans Set.subset_union_right)) ?_
  · exact htConn.trans (Set.union_subset (by intro z hz; exact Or.inl (Or.inr hz)) Set.subset_union_right)
  · rw [segment_symm]
    exact hsConn.trans (Set.union_subset (by intro z hz; exact Or.inl (Or.inl (Set.mem_singleton_iff.mp hz)))
      Set.subset_union_right)

theorem PositiveCellStep.midpoint_not_exterior_closing {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) {a b s t : OrientedEdge G} (hab : PositiveCellStep a b)
    (outer : PlaneFace G) (houter : ¬Bornology.IsBounded outer.val)
    (close : PlaneChain (edgeCenter t) (edgeCenter s))
    (hclose : close.trace⊆({edgeCenter s,edgeCenter t} : Set Plane)∪outer.val) :
    stepCenter a b∉close.trace := by
  obtain ⟨C,he,hf,_⟩ := hab
  have heq : a=C.edgeAB := Subtype.ext he
  have hfq : b=C.edgeDC := Subtype.ext hf
  have hcenter : stepCenter a b=C.center := by rw [heq,hfq,C.stepCenter_eq]
  have hm : stepCenter a b∈C.openRegion := by
    rw [hcenter,← C.cellPoint_half_eq_center]
    exact C.cellPoint_mem_openRegion ht (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnotDrawing : stepCenter a b∉G.drawing := C.openRegion_subset_complement ht hm
  intro hmem
  rcases hclose hmem with hend | hout
  · rcases hend with hs | ht
    · exact hnotDrawing (hs.symm ▸ G.edgeCenter_mem_drawing s)
    · exact hnotDrawing ((Set.mem_singleton_iff.mp ht).symm ▸ G.edgeCenter_mem_drawing t)
  · have heq : outer.val=C.openRegion :=
      (outer.property.eq_component hout).trans ((C.isBoundedFace ht).1.eq_component hm).symm
    apply houter
    rw [heq]
    exact (C.isBoundedFace ht).2

theorem PositiveSpineChain.rebased_remainder_avoids_midpoint {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) {s t e f : OrientedEdge G}
    (before : PositiveSpineChain G s e) (after : PositiveSpineChain G f t)
    (hef : PositiveCellStep e f) (outer : PlaneFace G) (houter : ¬Bornology.IsBounded outer.val)
    (close : PlaneChain (edgeCenter t) (edgeCenter s))
    (hclose : close.trace⊆({edgeCenter s,edgeCenter t} : Set Plane)∪outer.val) :
    stepCenter e f∉((after.toPlane.append close).append before.toPlane).trace := by
  have hm := hef.midpoint_height_between
  have hb : stepCenter e f∉before.toPlane.trace := by
    intro hz
    have hh := (before.height_bounds hz).2
    rw [positive_path_vector_eq before.reach] at hh
    linarith
  have ha : stepCenter e f∉after.toPlane.trace := by
    intro hz
    have hh := (after.height_bounds hz).1
    rw [← hef.to_cellStep.vector_eq] at hh
    linarith
  have hc := hef.midpoint_not_exterior_closing ht outer houter close hclose
  simp only [PlaneChain.trace_append,Set.mem_union]
  tauto

theorem PennyGraph.ordinary_spine_single_loop_winding_jumps {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {s t : OrientedEdge G} (hs : ¬∃g, PositiveCellStep g s)
    (htop : ¬∃g, PositiveCellStep t g) (hst : Relation.ReflTransGen PositiveCellStep s t)
    (hord : edgeComponent s∈G.ordinaryTrackComponents) :
    ∃ outer : PlaneFace G, ¬Bornology.IsBounded outer.val ∧
      ∃ loop : PlaneChain (edgeCenter s) (edgeCenter s),
        trackSpineTrace (edgeComponent s)⊆loop.trace ∧
        loop.trace⊆trackSpineTrace (edgeComponent s)∪outer.val ∧
        ∀ e f : OrientedEdge G, OnSpine s t e → PositiveCellStep e f →
          ∃ ε : ℝ, 0<ε ∧ ∀ r : ℝ, 0<r → r<ε →
            windingNormalProbe (edgeCenter e) (edgeCenter f) r∉loop.trace ∧
            windingNormalProbe (edgeCenter e) (edgeCenter f) (-r)∉loop.trace ∧
            loop.windingIndex (windingNormalProbe (edgeCenter e) (edgeCenter f) (-r))=
              loop.windingIndex (windingNormalProbe (edgeCenter e) (edgeCenter f) r)+1 ∧
            loop.windingIndex (windingNormalProbe (edgeCenter e) (edgeCenter f) r)%2≠
              loop.windingIndex (windingNormalProbe (edgeCenter e) (edgeCenter f) (-r))%2 := by
  obtain ⟨spine⟩ := PositiveSpineChain.exists_of_reach hst
  obtain ⟨outer,houter,close,hclose⟩ := G.ordinary_spine_fixed_exterior hs htop hst hord
  let loop := spine.toPlane.append close
  have hfull := spine.complete_trace ht hs htop
  have hsCenter : edgeCenter s∈trackSpineTrace (edgeComponent s) := Or.inl ⟨s,rfl,rfl⟩
  have htCenter : edgeCenter t∈trackSpineTrace (edgeComponent s) :=
    Or.inl ⟨t,(positive_path_component hst).symm,rfl⟩
  refine ⟨outer,houter,loop,?_,?_,?_⟩
  · rw [← hfull]
    dsimp only [loop]
    rw [PlaneChain.trace_append]
    exact Set.subset_union_left
  · rw [PlaneChain.trace_append,hfull]
    apply Set.union_subset Set.subset_union_left
    apply hclose.trans
    apply Set.union_subset ?_ Set.subset_union_right
    intro z hz
    rcases hz with hs | ht
    · exact Or.inl (hs.symm ▸ hsCenter)
    · exact Or.inl ((Set.mem_singleton_iff.mp ht).symm ▸ htCenter)
  · intro e f he hef
    obtain ⟨before,after,hparts⟩ := spine.decompose ht htop he hef
    let rest := (after.toPlane.append close).append before.toPlane
    let rebased := (PlaneChain.single (edgeCenter e) (edgeCenter f)).append rest
    have hm : (1/2 : ℝ) • (edgeCenter e+edgeCenter f)∉rest.trace :=
      before.rebased_remainder_avoids_midpoint ht after hef outer houter close hclose
    have hne : edgeCenter e≠edgeCenter f := by
      intro hcentres
      have hh : edgeHeight e=edgeHeight f := by unfold edgeHeight; rw [hef.to_cellStep.vector_eq,hcentres]
      exact (ne_of_lt hef.height_lt) hh
    have hplane : spine.toPlane=
        (before.toPlane.append (PlaneChain.single (edgeCenter e) (edgeCenter f))).append after.toPlane := by
      rw [hparts,PositiveSpineChain.toPlane_append,PositiveSpineChain.toPlane_append,
        PositiveSpineChain.toPlane_single]
    have htrace : loop.trace=rebased.trace := by
      simp only [loop,rebased,rest,hplane,PlaneChain.trace_append]
      ext z
      simp only [Set.mem_union]
      tauto
    have hangle (z : Plane) : loop.angle z=rebased.angle z := by
      simp only [loop,rebased,rest,hplane,PlaneChain.angle_append]
      ring
    have hindex (z : Plane) : loop.windingIndex z=rebased.windingIndex z := by
      unfold PlaneChain.windingIndex
      rw [hangle]
    obtain ⟨ε,hε,hjump⟩ := PlaneChain.segment_loop_winding_jump hne rest hm
    refine ⟨ε,hε,?_⟩
    intro r hr hrε
    have hj := hjump r hr hrε
    dsimp only [rebased] at htrace hindex
    simpa only [← htrace,← hindex] using hj

end Swanepoel
