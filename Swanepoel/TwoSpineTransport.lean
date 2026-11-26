module
public import Swanepoel.HalfLocalBanks
@[expose] public section

noncomputable section
namespace Swanepoel
open Set

theorem PennyGraph.vertex_not_on_two_spine_loop {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (u v : TrackComponent G) (outer : PlaneFace G)
    {a : Plane} (loop : PlaneChain a a)
    (hloop : loop.trace⊆(trackSpineTrace u∪trackSpineTrace v)∪outer.val) (i : Fin n) :
    G.point i∉loop.trace := by
  intro hz
  rcases hloop hz with (hu | hv) | ho
  · exact G.vertex_not_on_track_spine ht u i hu
  · exact G.vertex_not_on_track_spine ht v i hv
  · exact G.face_subset_complement outer ho (G.point_mem_drawing i)

theorem PennyGraph.defect_vertex_two_spine_label {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (u v : TrackComponent G) (outer : PlaneFace G)
    (houter : ¬Bornology.IsBounded outer.val) {a : Plane} (loop : PlaneChain a a)
    (hloop : loop.trace⊆(trackSpineTrace u∪trackSpineTrace v)∪outer.val)
    (F : PlaneFace G) (hF : F∈G.defectPlaneFaces ht) (i : Fin n)
    (hi : G.point i∈closure F.val) : loop.windingIndex (G.point i)=G.faceWindingLabel loop F := by
  have hne : F≠outer := by
    intro he
    exact houter (he ▸ G.defectPlaneFace_isBounded ht hF)
  have hdis : Disjoint F.val loop.trace :=
    (((G.defectFace_disjoint_trackSpine ht F hF u).union_right
      (G.defectFace_disjoint_trackSpine ht F hF v)).union_right
      (G.faces_disjoint_of_ne F outer hne)).mono_right hloop
  exact loop.windingIndex_eq_of_mem_closure (G.face_preconnected F) hdis
    F.property.nonempty.choose_spec hi (G.vertex_not_on_two_spine_loop ht u v outer loop hloop i)

theorem PennyGraph.noncut_edge_two_spine_winding_equal {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (u v : TrackComponent G) (outer : PlaneFace G)
    {a : Plane} (loop : PlaneChain a a)
    (hloop : loop.trace⊆(trackSpineTrace u∪trackSpineTrace v)∪outer.val)
    (e : OrientedEdge G) (hnu : edgeComponent e≠u) (hnv : edgeComponent e≠v) :
    loop.windingIndex (G.point e.val.1)=loop.windingIndex (G.point e.val.2) := by
  have hpre : IsPreconnected (G.edgeTrace e.val.1 e.val.2) := by
    rw [G.edgeTrace_eq_segment]
    exact (convex_segment (𝕜 := ℝ) _ _).isPreconnected
  have hdis : Disjoint (G.edgeTrace e.val.1 e.val.2) loop.trace := by
    apply Set.disjoint_left.mpr
    intro z hz hzloop
    rcases hloop hzloop with (hu | hv) | hout
    · exact Set.disjoint_left.mp (edgeTrace_disjoint_other_spine ht e u hnu) hz hu
    · exact Set.disjoint_left.mp (edgeTrace_disjoint_other_spine ht e v hnv) hz hv
    · exact G.face_subset_complement outer hout (G.edgeTrace_subset_drawing _ _ e.property hz)
  apply loop.windingIndex_constant hpre hdis
  · exact ⟨0,⟨by norm_num,by norm_num⟩,by simp [PennyGraph.edgePoint]⟩
  · exact ⟨1,⟨by norm_num,by norm_num⟩,by simp [PennyGraph.edgePoint]⟩

theorem two_spine_path_start_vertex_winding_eq {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) (u v : TrackComponent G) (outer : PlaneFace G)
    {a : Plane} (loop : PlaneChain a a)
    (hloop : loop.trace⊆(trackSpineTrace u∪trackSpineTrace v)∪outer.val)
    {e f : OrientedEdge G} (hpath : Relation.ReflTransGen PositiveCellStep e f)
    (hsteps : ∀ x y, Relation.ReflTransGen PositiveCellStep e x → PositiveCellStep x y →
      TrackCutStep u x y ∧ TrackCutStep v x y) :
    loop.windingIndex (G.point e.val.1)=loop.windingIndex (G.point f.val.1) := by
  induction hpath with
  | refl => rfl
  | @tail x y hx hxy ih =>
    obtain ⟨hu,hv⟩ := hsteps x y hx hxy
    obtain ⟨C,hX,hY,_⟩ := hxy
    have hneqU := hu.other_component_ne ht C hX hY
    have hneqV := hv.other_component_ne ht C hX hY
    have hh := G.noncut_edge_two_spine_winding_equal ht u v outer loop hloop C.edgeAD hneqU hneqV
    exact ih.trans (by simpa only [hX,hY,RhombusCell.edgeAD] using hh)

theorem PositiveSpineChain.carried_start_label_of_mem {n : ℕ} {G : PennyGraph n}
    {s t : OrientedEdge G} (p : PositiveSpineChain G s t)
    (loop : PlaneChain (edgeCenter s) (edgeCenter s))
    (sign : ℝ) (hdis : Disjoint (p.bankRegion sign) loop.trace)
    (e : OrientedEdge G) (hm : edgeCenter e∈p.toPlane.trace)
    (hv : carriedVector e=(-sign) • carriedVector s) :
    loop.windingIndex (G.point e.val.1)=p.bankLabel loop sign := by
  apply p.bankLabel_constant_of_disjoint loop sign hdis
  refine ⟨edgeCenter e,hm,1/2,⟨by norm_num,le_rfl⟩,?_⟩
  have hh : G.point e.val.1=edgeCenter e-(1/2:ℝ) • carriedVector e := by
    dsimp [edgeCenter,RhombusCell.midpoint2,carriedVector]
    module
  rw [hh,hv]
  module

end Swanepoel
