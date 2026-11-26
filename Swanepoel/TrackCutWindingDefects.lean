module
public import Swanepoel.TrackCutWindingClosure
@[expose] public section

noncomputable section
namespace Swanepoel

theorem PennyGraph.faces_disjoint_of_ne {n : ℕ} (G : PennyGraph n) (F H : PlaneFace G)
    (hne : F≠H) : Disjoint F.val H.val := by
  apply Set.disjoint_left.mpr
  intro z hzF hzH
  have heq := F.property.eq_component hzF |>.trans (H.property.eq_component hzH).symm
  exact hne (Subtype.ext heq)

theorem PennyGraph.defectFace_ne_rhombus {n : ℕ} (G : PennyGraph n) (ht : G.TriangleFree)
    (F : PlaneFace G) (hF : F∈G.defectPlaneFaces ht) (C : RhombusCell G) : F.val≠C.openRegion := by
  classical
  obtain ⟨B,hB,hBF⟩ := Finset.mem_image.mp hF
  intro heq
  have hBval : B.val=C.openRegion := (congrArg Subtype.val hBF).trans heq
  let R : RhombusSet G := ⟨C.corners,⟨C,rfl⟩⟩
  have hr : R.representative.openRegion=C.openRegion :=
    R.representative.openRegion_eq_of_corners ht C R.representative_corners
  have hBr : B=rhombusFaceMap G ht R := Subtype.ext (hBval.trans hr.symm)
  have hnot : B∉G.rhombicFaces ht := (Finset.mem_sdiff.mp hB).2
  exact hnot (Finset.mem_image.mpr ⟨R,Finset.mem_univ _,hBr.symm⟩)

theorem PennyGraph.defectFace_disjoint_closedRhombus {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (F : PlaneFace G) (hF : F∈G.defectPlaneFaces ht)
    (C : RhombusCell G) : Disjoint F.val C.closedRegion := by
  have hne : F≠⟨C.openRegion,(C.isBoundedFace ht).1⟩ := by
    intro he
    exact G.defectFace_ne_rhombus ht F hF C (congrArg Subtype.val he)
  have hdis := G.faces_disjoint_of_ne F ⟨C.openRegion,(C.isBoundedFace ht).1⟩ hne
  have hFC : F.val⊆G.drawingᶜ := by
    obtain ⟨x,hx,hcomp⟩ := F.property
    rw [hcomp]
    exact connectedComponentIn_subset _ _
  apply Set.disjoint_left.mpr
  intro z hzF hzC
  rcases C.closedRegion_subset_open_union_boundary ht hzC with hzO | hzB
  · exact Set.disjoint_left.mp hdis hzF hzO
  · exact hFC hzF (C.boundary_subset_drawing hzB)

theorem PositiveCellStep.segment_subset_closedRhombus {n : ℕ} {G : PennyGraph n}
    (ht : G.TriangleFree) {e f : OrientedEdge G} (hef : PositiveCellStep e f) :
    ∃ C : RhombusCell G, segment ℝ (edgeCenter e) (edgeCenter f)⊆C.closedRegion := by
  obtain ⟨C,he,hf,_⟩ := hef
  refine ⟨C,?_⟩
  intro z hz
  rw [segment_eq_image] at hz
  obtain ⟨r,⟨hr0,hr1⟩,rfl⟩ := hz
  have hc : G.point C.c=G.point C.b+G.point C.d-G.point C.a :=
    (eq_sub_iff_add_eq).mpr (by simpa [add_comm] using C.parallelogram)
  have hp : (1-r) • edgeCenter e+r • edgeCenter f=C.cellPoint (1/2) r := by
    simp only [edgeCenter,he,hf,RhombusCell.midpoint2,RhombusCell.cellPoint,
      RhombusCell.u,RhombusCell.v]
    rw [hc]
    module
  change (1-r) • edgeCenter e+r • edgeCenter f∈C.closedRegion
  rw [hp]
  exact ⟨by rw [C.coordU_cellPoint ht]; norm_num,by rw [C.coordU_cellPoint ht]; norm_num,
    by rwa [C.coordV_cellPoint ht],by rwa [C.coordV_cellPoint ht]⟩

theorem PennyGraph.edgeCenter_mem_drawing {n : ℕ} (G : PennyGraph n) (e : OrientedEdge G) :
    edgeCenter e∈G.drawing := by
  rw [edgeCenter_eq_midpoint]
  exact G.edgeTrace_subset_drawing _ _ e.property ⟨1/2,⟨by norm_num,by norm_num⟩,rfl⟩

theorem PennyGraph.defectFace_disjoint_trackSpine {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) (F : PlaneFace G) (hF : F∈G.defectPlaneFaces ht)
    (c : TrackComponent G) : Disjoint F.val (trackSpineTrace c) := by
  have hFC : F.val⊆G.drawingᶜ := by
    obtain ⟨x,hx,hcomp⟩ := F.property
    rw [hcomp]
    exact connectedComponentIn_subset _ _
  apply Set.disjoint_left.mpr
  intro z hzF hzS
  rcases hzS with ⟨e,he,rfl⟩ | ⟨e,f,he,hef,hz⟩
  · exact hFC hzF (G.edgeCenter_mem_drawing e)
  · obtain ⟨C,hC⟩ := hef.segment_subset_closedRhombus ht
    exact Set.disjoint_left.mp (G.defectFace_disjoint_closedRhombus ht F hF C) hzF (hC hz)

def PennyGraph.faceWindingLabel {n : ℕ} (G : PennyGraph n) {a : Plane}
    (p : PlaneChain a a) (F : PlaneFace G) : ℤ :=
  p.windingIndex F.property.nonempty.choose

theorem PennyGraph.ordinary_cut_defect_winding_labels {n : ℕ} (G : PennyGraph n)
    (ht : G.TriangleFree) {s t : OrientedEdge G} (hs : ¬∃g, PositiveCellStep g s)
    (htop : ¬∃g, PositiveCellStep t g) (hst : Relation.ReflTransGen PositiveCellStep s t)
    (hord : edgeComponent s∈G.ordinaryTrackComponents) :
    ∃ outer : PlaneFace G, ¬Bornology.IsBounded outer.val ∧
      ∃ p : PlaneChain (edgeCenter s) (edgeCenter s),
        trackSpineTrace (edgeComponent s)⊆p.trace ∧
        p.trace⊆trackSpineTrace (edgeComponent s)∪outer.val ∧
        ∀ F∈G.defectPlaneFaces ht, Disjoint F.val p.trace ∧
          ∀ z∈F.val, p.windingIndex z=G.faceWindingLabel p F := by
  obtain ⟨outer,houter,p,hspine,htrace⟩ := G.ordinary_spine_closed_chain ht hs htop hst hord
  refine ⟨outer,houter,p,hspine,htrace,?_⟩
  intro F hF
  have hne : F≠outer := by
    intro he
    exact houter (he ▸ G.defectPlaneFace_isBounded ht hF)
  have hdis : Disjoint F.val p.trace :=
    ((G.defectFace_disjoint_trackSpine ht F hF (edgeComponent s)).union_right
      (G.faces_disjoint_of_ne F outer hne)).mono_right htrace
  refine ⟨hdis,?_⟩
  intro z hz
  have hpre : IsPreconnected F.val := by
    obtain ⟨x,hx,hcomp⟩ := F.property
    rw [hcomp]
    exact isPreconnected_connectedComponentIn
  exact p.windingIndex_constant hpre hdis hz F.property.nonempty.choose_spec

end Swanepoel
