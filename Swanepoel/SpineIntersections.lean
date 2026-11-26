module
public import Swanepoel.TrackCutWindingDefects
public import Swanepoel.CrossingPortCones
@[expose] public section

noncomputable section
namespace Swanepoel
open Set

theorem edgeCenter_component_eq {n : ℕ} {G : PennyGraph n} (e f : OrientedEdge G)
    (heq : edgeCenter e=edgeCenter f) : edgeComponent e=edgeComponent f := by
  apply edgeComponent_of_unordered_eq
  apply G.interior_edge_intersection _ _ _ _ e.property f.property
    (t := 1/2) (s := 1/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simpa only [edgeCenter_eq_midpoint] using heq

theorem track_spine_point_cases {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    (c : TrackComponent G) {z : Plane} (hz : z∈trackSpineTrace c) :
    (∃ e : OrientedEdge G, edgeComponent e=c ∧ z=edgeCenter e) ∨
      ∃ C : RhombusCell G, edgeComponent C.edgeAB=c ∧ z∈C.openRegion ∧
        cross2 C.v (z-C.center)=0 := by
  rcases hz with hz | ⟨e,f,he,hef,hz⟩
  · exact Or.inl hz
  obtain ⟨C,hE,hF,_⟩ := hef
  rw [segment_eq_image] at hz
  obtain ⟨r,⟨hr0,hr1⟩,rfl⟩ := hz
  by_cases h0 : r=0
  · left
    exact ⟨e,he,by simp only [h0,sub_zero,one_smul,zero_smul,add_zero]⟩
  by_cases h1 : r=1
  · left
    exact ⟨f,(positive_path_component (Relation.ReflTransGen.single
      (show PositiveCellStep e f from ⟨C,hE,hF,by assumption⟩))).symm.trans he,
      by simp only [h1,sub_self,zero_smul,one_smul,zero_add]⟩
  have hc : G.point C.c=G.point C.b+G.point C.d-G.point C.a :=
    (eq_sub_iff_add_eq).mpr (by simpa [add_comm] using C.parallelogram)
  have hp : (1-r) • edgeCenter e+r • edgeCenter f=C.cellPoint (1/2) r := by
    simp only [edgeCenter,hE,hF,RhombusCell.midpoint2,RhombusCell.cellPoint,
      RhombusCell.u,RhombusCell.v]
    rw [hc]
    module
  have hline : C.cellPoint (1/2) r-C.center=(r-1/2) • C.v := by
    rw [← C.cellPoint_half_eq_center]
    dsimp [RhombusCell.cellPoint]
    module
  right
  refine ⟨C,?_,?_,?_⟩
  · have heq : e=C.edgeAB := Subtype.ext hE
    simpa only [heq] using he
  · change (1-r) • edgeCenter e+r • edgeCenter f∈C.openRegion
    rw [hp]
    exact C.cellPoint_mem_openRegion ht (by norm_num) (by norm_num)
      (lt_of_le_of_ne hr0 (Ne.symm h0)) (lt_of_le_of_ne hr1 h1)
  · change cross2 C.v ((1-r) • edgeCenter e+r • edgeCenter f-C.center)=0
    rw [hp,hline,cross2_smul_right,cross2_self,mul_zero]

theorem PennyGraph.track_spine_disjoint_outer {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (c : TrackComponent G) (outer : PlaneFace G)
    (houter : ¬Bornology.IsBounded outer.val) : Disjoint (trackSpineTrace c) outer.val := by
  apply Set.disjoint_left.mpr
  intro z hz hout
  rcases track_spine_point_cases ht c hz with ⟨e,_,rfl⟩ | ⟨C,_,hC,_⟩
  · exact G.face_subset_complement outer hout (G.edgeCenter_mem_drawing e)
  · have heq : outer.val=C.openRegion :=
      (outer.property.eq_component hout).trans ((C.isBoundedFace ht).1.eq_component hC).symm
    exact houter (heq.symm ▸ (C.isBoundedFace ht).2)

theorem PennyGraph.vertex_not_on_track_spine {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (c : TrackComponent G) (i : Fin n) :
    G.point i∉trackSpineTrace c := by
  intro hz
  rcases track_spine_point_cases ht c hz with ⟨e,_,he⟩ | ⟨C,_,hC,_⟩
  · have hm := G.edgePoint_ne_vertex e.val.1 e.val.2 i e.property
      (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1)
    exact hm (by simpa only [edgeCenter_eq_midpoint] using he.symm)
  · exact C.openRegion_subset_complement ht hC (G.point_mem_drawing i)

theorem track_spine_intersection_rhombus {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) {c d : TrackComponent G} (hne : c≠d) {z : Plane}
    (hc : z∈trackSpineTrace c) (hd : z∈trackSpineTrace d) :
    ∃ C : RhombusCell G, edgeComponent C.edgeAB=c ∧ edgeComponent C.edgeAD=d ∧ z=C.center := by
  rcases track_spine_point_cases ht c hc with ⟨e,he,hze⟩ | ⟨C,hC,hzC,hlineC⟩
  · rcases track_spine_point_cases ht d hd with ⟨f,hf,hzf⟩ | ⟨D,_,hzD,_⟩
    · exact False.elim (hne (he.symm.trans
        ((edgeCenter_component_eq e f (hze.symm.trans hzf)).trans hf)))
    · exact False.elim (D.openRegion_subset_complement ht hzD
        (hze.symm ▸ G.edgeCenter_mem_drawing e))
  rcases track_spine_point_cases ht d hd with ⟨f,hf,hzf⟩ | ⟨D,hD,hzD,hlineD⟩
  · exact False.elim (C.openRegion_subset_complement ht hzC
      (hzf.symm ▸ G.edgeCenter_mem_drawing f))
  have hfaces : C.openRegion=D.openRegion :=
    ((C.isBoundedFace ht).1.eq_component hzC).trans ((D.isBoundedFace ht).1.eq_component hzD).symm
  have hcorners := C.corners_eq_of_openRegion_eq ht D hfaces
  have hpairs := C.trackPair_of_corners ht D hcorners
  change s(edgeComponent C.edgeAB,edgeComponent C.edgeAD)=
    s(edgeComponent D.edgeAB,edgeComponent D.edgeAD) at hpairs
  rw [hC,hD] at hpairs
  have hCAD : edgeComponent C.edgeAD=d := by
    rcases Sym2.eq_iff.mp hpairs with h | h
    · exact False.elim (hne h.1)
    · exact h.2
  have hDAD : edgeComponent D.edgeAD=c := by
    rcases Sym2.eq_iff.mp hpairs with h | h
    · exact False.elim (hne h.1)
    · exact h.1.symm
  have hcross : ComponentCrosses (edgeComponent C.edgeAD) (edgeComponent D.edgeAD) := by
    rw [hCAD,hDAD]
    exact ⟨C,Or.inr ⟨hC,hCAD⟩⟩
  have hsmall := component_crossing_angle ht hcross
  have hsC := component_sameLine C.edgeAD (edgeComponent C.edgeAD) rfl
  have hsD := component_sameLine D.edgeAD (edgeComponent D.edgeAD) rfl
  change SameLine C.v (componentVector (edgeComponent C.edgeAD)) at hsC
  change SameLine D.v (componentVector (edgeComponent D.edgeAD)) at hsD
  have hsmall' : |inner ℝ C.v D.v|<1/2 := by
    rw [hsC.abs_inner_eq hsD]
    exact hsmall
  have hCv : ‖C.v‖=1 := by simpa only [RhombusCell.v,← dist_eq_norm] using C.da.2
  have hDv : ‖D.v‖=1 := by simpa only [RhombusCell.v,← dist_eq_norm] using D.da.2
  have hdet : cross2 C.v D.v≠0 := by
    intro hz
    have hg := cross2_sq_add_inner_sq C.v D.v
    rw [hz,hCv,hDv] at hg
    have hi := abs_lt.mp hsmall'
    nlinarith [mul_pos (by linarith : 0<1/2-inner ℝ C.v D.v)
      (by linarith : 0<1/2+inner ℝ C.v D.v)]
  have hcentres := C.center_of_corners D hcorners
  rw [← hcentres] at hlineD
  have hswap : cross2 (z-C.center) D.v=0 := by
    have hh : cross2 (z-C.center) D.v= -cross2 D.v (z-C.center) := by
      unfold cross2
      ring
    rw [hh,hlineD,neg_zero]
  have hcr := cramer_reconstruct C.v D.v (z-C.center) hdet
  simp only [hswap,hlineC,zero_div,zero_smul,zero_add] at hcr
  exact ⟨C,hC,hCAD,sub_eq_zero.mp hcr.symm⟩

theorem track_spines_disjoint_of_noncrossing {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) {c d : TrackComponent G} (hne : c≠d)
    (hmiss : ¬ComponentCrosses c d) : Disjoint (trackSpineTrace c) (trackSpineTrace d) := by
  apply Set.disjoint_left.mpr
  intro z hc hd
  obtain ⟨C,hC,hD,_⟩ := track_spine_intersection_rhombus ht hne hc hd
  exact hmiss ⟨C,Or.inl ⟨hC,hD⟩⟩

theorem track_spine_intersection_eq_center {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) {c d : TrackComponent G} (hne : c≠d)
    (C : RhombusCell G)
    (hC : (edgeComponent C.edgeAB=c ∧ edgeComponent C.edgeAD=d) ∨
      (edgeComponent C.edgeAB=d ∧ edgeComponent C.edgeAD=c))
    {z : Plane} (hc : z∈trackSpineTrace c) (hd : z∈trackSpineTrace d) : z=C.center := by
  obtain ⟨D,hD,hE,hz⟩ := track_spine_intersection_rhombus ht hne hc hd
  exact hz.trans (D.center_of_corners C (rhombi_single_crossing ht D C c d (Or.inl ⟨hD,hE⟩) hC))

end Swanepoel
