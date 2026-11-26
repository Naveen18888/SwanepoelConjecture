module
public import Swanepoel.SpineBankGeometry
public import Swanepoel.SpineIntersections
@[expose] public section

noncomputable section
namespace Swanepoel
open Set

theorem PlaneChain.windingIndex_eq_of_mem_closure {a : Plane} (loop : PlaneChain a a)
    {F : Set Plane} (hF : IsPreconnected F) (hdis : Disjoint F loop.trace)
    {x y : Plane} (hx : x∈F) (hy : y∈closure F) (hyoff : y∉loop.trace) :
    loop.windingIndex y=loop.windingIndex x := by
  have hpre : IsPreconnected (insert y F) := hF.subset_closure (subset_insert _ _)
    (insert_subset hy subset_closure)
  have hdi : Disjoint (insert y F) loop.trace := Set.disjoint_left.mpr (by
    intro z hz hzloop
    rcases hz with rfl | hz
    · exact hyoff hzloop
    · exact Set.disjoint_left.mp hdis hz hzloop)
  exact loop.windingIndex_constant hpre hdi (mem_insert _ _) (mem_insert_of_mem _ hx)

theorem edgeTrace_disjoint_other_spine {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) (e : OrientedEdge G) (cut : TrackComponent G)
    (hne : edgeComponent e≠cut) : Disjoint (G.edgeTrace e.val.1 e.val.2) (trackSpineTrace cut) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨r,⟨hr0,hr1⟩,hz⟩ hspine
  rcases track_spine_point_cases ht cut hspine with ⟨f,hf,hzf⟩ | ⟨C,_,hC,_⟩
  · have heq : G.edgePoint f.val.1 f.val.2 (1/2)=G.edgePoint e.val.1 e.val.2 r := by
      simpa only [edgeCenter_eq_midpoint] using hzf.symm.trans hz.symm
    have hphys := G.interior_edge_intersection _ _ _ _ f.property e.property
      (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1) hr0 hr1 heq
    exact hne ((edgeComponent_of_unordered_eq f e hphys).symm.trans hf)
  · exact C.openRegion_subset_complement ht hC
      (G.edgeTrace_subset_drawing _ _ e.property ⟨r,⟨hr0,hr1⟩,hz⟩)

theorem PennyGraph.noncut_edge_winding_equal {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (cut : TrackComponent G) (outer : PlaneFace G)
    {a : Plane} (loop : PlaneChain a a)
    (hloop : loop.trace⊆trackSpineTrace cut∪outer.val)
    (e : OrientedEdge G) (hne : edgeComponent e≠cut) :
    loop.windingIndex (G.point e.val.1)=loop.windingIndex (G.point e.val.2) := by
  have hpre : IsPreconnected (G.edgeTrace e.val.1 e.val.2) := by
    rw [G.edgeTrace_eq_segment]
    exact (convex_segment (𝕜 := ℝ) _ _).isPreconnected
  have hdis : Disjoint (G.edgeTrace e.val.1 e.val.2) loop.trace := by
    apply Set.disjoint_left.mpr
    intro z hz hzloop
    rcases hloop hzloop with hspine | hout
    · exact Set.disjoint_left.mp (edgeTrace_disjoint_other_spine ht e cut hne) hz hspine
    · exact G.face_subset_complement outer hout (G.edgeTrace_subset_drawing _ _ e.property hz)
  apply loop.windingIndex_constant hpre hdis
  · exact ⟨0,⟨by norm_num,by norm_num⟩,by simp [PennyGraph.edgePoint]⟩
  · exact ⟨1,⟨by norm_num,by norm_num⟩,by simp [PennyGraph.edgePoint]⟩

theorem PennyGraph.vertex_not_on_ordinary_loop {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (cut : TrackComponent G) (outer : PlaneFace G)
    {a : Plane} (loop : PlaneChain a a)
    (hloop : loop.trace⊆trackSpineTrace cut∪outer.val) (i : Fin n) :
    G.point i∉loop.trace := by
  intro hz
  rcases hloop hz with hs | ho
  · exact G.vertex_not_on_track_spine ht cut i hs
  · exact G.face_subset_complement outer ho (G.point_mem_drawing i)

theorem PennyGraph.defect_vertex_winding_label {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (cut : TrackComponent G) (outer : PlaneFace G)
    (houter : ¬Bornology.IsBounded outer.val) {a : Plane} (loop : PlaneChain a a)
    (hloop : loop.trace⊆trackSpineTrace cut∪outer.val)
    (F : PlaneFace G) (hF : F∈G.defectPlaneFaces ht) (i : Fin n)
    (hi : G.point i∈closure F.val) : loop.windingIndex (G.point i)=G.faceWindingLabel loop F := by
  have hne : F≠outer := by
    intro he
    exact houter (he ▸ G.defectPlaneFace_isBounded ht hF)
  have hdis : Disjoint F.val loop.trace :=
    ((G.defectFace_disjoint_trackSpine ht F hF cut).union_right
      (G.faces_disjoint_of_ne F outer hne)).mono_right hloop
  exact loop.windingIndex_eq_of_mem_closure (G.face_preconnected F) hdis
    F.property.nonempty.choose_spec hi (G.vertex_not_on_ordinary_loop ht cut outer loop hloop i)

theorem PositiveSpineChain.step_segment_subset {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) {s t e f : OrientedEdge G} (p : PositiveSpineChain G s t)
    (htop : ¬∃g,PositiveCellStep t g) (he : OnSpine s t e) (hef : PositiveCellStep e f) :
    segment ℝ (edgeCenter e) (edgeCenter f)⊆p.toPlane.trace := by
  obtain ⟨before,after,hparts⟩ := p.decompose ht htop he hef
  rw [hparts,PositiveSpineChain.toPlane_append,PositiveSpineChain.toPlane_append,
    PositiveSpineChain.toPlane_single,PlaneChain.trace_append,PlaneChain.trace_append,
    PlaneChain.trace_single]
  exact fun _ hz => Or.inl (Or.inr hz)

theorem PositiveSpineChain.cellPoint_mem_bank {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) {s t e f : OrientedEdge G} (p : PositiveSpineChain G s t)
    (htop : ¬∃g,PositiveCellStep t g) (he : OnSpine s t e)
    (C : RhombusCell G) (hE : e.val=(C.a,C.b)) (hF : f.val=(C.d,C.c))
    (hpos : 0<cross2 C.u C.v) (sign δ r : ℝ) (hδ : δ∈Ioc (0:ℝ) (1/2))
    (hr : r∈Icc (0:ℝ) 1) : C.cellPoint (1/2+sign*δ) r∈p.bankRegion sign := by
  have hef : PositiveCellStep e f := ⟨C,hE,hF,hpos⟩
  have hv : carriedVector s=C.u := by
    rw [positive_path_vector_eq he.1]
    simp only [carriedVector,hE,RhombusCell.u]
  have hcorn : G.point C.c=G.point C.b+G.point C.d-G.point C.a :=
    (eq_sub_iff_add_eq).mpr (by simpa [add_comm] using C.parallelogram)
  have hm : C.cellPoint (1/2) r∈segment ℝ (edgeCenter e) (edgeCenter f) := by
    rw [segment_eq_image]
    refine ⟨r,hr,?_⟩
    simp only [edgeCenter,hE,hF,RhombusCell.midpoint2,RhombusCell.cellPoint,RhombusCell.u,RhombusCell.v]
    rw [hcorn]
    module
  refine ⟨C.cellPoint (1/2) r,p.step_segment_subset ht htop he hef hm,δ,hδ,?_⟩
  rw [hv]
  dsimp [RhombusCell.cellPoint]
  module

def PositiveSpineChain.bankLabel {n : ℕ} {G : PennyGraph n} {s t : OrientedEdge G}
    (_p : PositiveSpineChain G s t) (loop : PlaneChain (edgeCenter s) (edgeCenter s))
    (sign : ℝ) : ℤ := loop.windingIndex (edgeCenter s+(sign/4) • carriedVector s)

theorem PositiveSpineChain.bankLabel_constant {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) {s t : OrientedEdge G} (p : PositiveSpineChain G s t)
    (hs : ¬∃g,PositiveCellStep g s) (htop : ¬∃g,PositiveCellStep t g)
    (outer : PlaneFace G) (houter : ¬Bornology.IsBounded outer.val)
    (loop : PlaneChain (edgeCenter s) (edgeCenter s))
    (hloop : loop.trace⊆trackSpineTrace (edgeComponent s)∪outer.val)
    (sign : ℝ) (hsign : sign=1 ∨ sign= -1) {z : Plane} (hz : z∈p.bankRegion sign) :
    loop.windingIndex z=p.bankLabel loop sign := by
  have hbase : edgeCenter s+(sign/4) • carriedVector s∈p.bankRegion sign := by
    refine ⟨edgeCenter s,p.toPlane.start_mem_trace,1/4,⟨by norm_num,by norm_num⟩,?_⟩
    congr 2
    ring
  exact loop.windingIndex_constant (p.bankRegion_preconnected sign)
    (p.bankRegion_avoids_loop ht hs htop outer houter loop hloop sign hsign) hz hbase

end Swanepoel
