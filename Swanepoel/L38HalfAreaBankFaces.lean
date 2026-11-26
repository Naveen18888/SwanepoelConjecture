module
public import Swanepoel.L38HalfAreaFaces
public import Swanepoel.L38HalfGraph
public import Swanepoel.Lemma37
@[expose] public section

noncomputable section
namespace Swanepoel
open Set
attribute [local instance] Classical.propDecidable

namespace OrdinaryCutBanks
variable {n : ℕ} {G : PennyGraph n} {cut : TrackComponent G} (B : OrdinaryCutBanks G cut)

theorem bank_defect_vertex_mem (ht : G.TriangleFree) (side : Bool)
    (F : PlaneFace G) (hF : F∈B.bankDefectFamily ht side)
    (v : Fin n) (hv : G.point v∈closure F.val) : v∈B.bankVertices side := by
  have hdef := (Finset.mem_filter.mp hF).1
  have hl := G.defect_vertex_winding_label ht cut B.outer B.outer_unbounded B.loop B.support F hdef v hv
  change B.vertexLabel v=B.faceLabel F at hl
  apply (B.mem_bankVertices side v).mpr
  change decide (B.vertexLabel v=B.positiveLabel)=side
  rw [hl]
  exact (Finset.mem_filter.mp hF).2

theorem bank_defect_source_vertices (ht : G.TriangleFree) (side : Bool)
    (e : OrientedEdge G) (he : G.sourceFace e∈B.bankDefectFamily ht side) :
    e.val.1∈B.bankVertices side ∧ e.val.2∈B.bankVertices side := by
  have hcl := G.sourceFace_endpoints_mem_closure e
  exact ⟨B.bank_defect_vertex_mem ht side _ he _ hcl.1,
    B.bank_defect_vertex_mem ht side _ he _ hcl.2⟩

theorem bank_defect_frontier_retained (ht : G.TriangleFree) (side : Bool)
    (F : PlaneFace G) (hF : F∈B.bankDefectFamily ht side) :
    frontier F.val⊆(B.halfGraph side).drawing := by
  apply G.face_frontier_retained_of_vertices_and_edges (B.halfGraph side) F
  · intro v hv
    exact B.halfGraph_vertex_mem side v (B.bank_defect_vertex_mem ht side F hF v hv)
  · intro e he
    have heF : G.sourceFace e∈B.bankDefectFamily ht side := he ▸ hF
    have hv := B.bank_defect_source_vertices ht side e heF
    exact B.halfGraph_edgeTrace_subset side e hv.1 hv.2

def bankDefectPlaneFace (ht : G.TriangleFree) (side : Bool)
    (F : PlaneFace G) (hF : F∈B.bankDefectFamily ht side) : PlaneFace (B.halfGraph side) :=
  G.retainedPlaneFace (B.halfGraph side) (B.halfGraph_drawing_subset side) F
    (B.bank_defect_frontier_retained ht side F hF)

@[simp] theorem bankDefectPlaneFace_val (ht : G.TriangleFree) (side : Bool)
    (F : PlaneFace G) (hF : F∈B.bankDefectFamily ht side) :
    (B.bankDefectPlaneFace ht side F hF).val=F.val := rfl

theorem bankDefectPlaneFace_injective (ht : G.TriangleFree) (side : Bool) :
    Function.Injective (fun F : {F : PlaneFace G // F∈B.bankDefectFamily ht side} =>
      B.bankDefectPlaneFace ht side F.val F.property) := by
  intro F K h
  have hval := congrArg (fun L : PlaneFace (B.halfGraph side) => L.val) h
  change F.val.val=K.val.val at hval
  exact Subtype.ext (Subtype.ext hval)

def bankDefectBoundedFace (ht : G.TriangleFree) (side : Bool)
    (F : PlaneFace G) (hF : F∈B.bankDefectFamily ht side) : BoundedFace (B.halfGraph side) :=
  ⟨F.val,(B.bankDefectPlaneFace ht side F hF).property,
    G.defectPlaneFace_isBounded ht (Finset.mem_filter.mp hF).1⟩

theorem bankDefect_sourceFace (ht : G.TriangleFree) (side : Bool)
    (e : OrientedEdge (B.halfGraph side))
    (he : G.sourceFace (B.halfEdge side e)∈B.bankDefectFamily ht side) :
    (B.halfGraph side).sourceFace e=
      B.bankDefectPlaneFace ht side (G.sourceFace (B.halfEdge side e)) he := by
  apply Subtype.ext
  apply G.sourceFace_eq_of_retained_face (B.halfGraph side) (B.halfGraph_drawing_subset side)
    (B.halfEdge side e) e (B.halfEdge_vector side e).symm rfl
  exact (B.bankDefectPlaneFace ht side (G.sourceFace (B.halfEdge side e)) he).property

theorem bankDefect_sourceFace_iff (ht : G.TriangleFree) (side : Bool)
    (F : PlaneFace G) (hF : F∈B.bankDefectFamily ht side)
    (e : OrientedEdge (B.halfGraph side)) :
    (B.halfGraph side).sourceFace e=B.bankDefectPlaneFace ht side F hF ↔
      G.sourceFace (B.halfEdge side e)=F := by
  constructor
  · intro he
    have hs := G.sourceFace_subset_of_drawing_subset (B.halfGraph side) (B.halfGraph_drawing_subset side)
      (B.halfEdge side e) e (B.halfEdge_vector side e).symm rfl
    have hval := congrArg Subtype.val he
    change ((B.halfGraph side).sourceFace e).val=F.val at hval
    rw [hval] at hs
    have hz := G.sourceProbe_mem_sourceFace (B.halfEdge side e)
    apply Subtype.ext
    exact ((G.sourceFace (B.halfEdge side e)).property.eq_component hz).trans
      (F.property.eq_component (hs hz)).symm
  · intro he
    have heF : G.sourceFace (B.halfEdge side e)∈B.bankDefectFamily ht side := he ▸ hF
    have hs := B.bankDefect_sourceFace ht side e heF
    apply Subtype.ext
    simpa only [B.bankDefectPlaneFace_val,he] using congrArg Subtype.val hs

theorem bankDefect_signed_area (ht : G.TriangleFree) (side : Bool)
    (F : PlaneFace G) (hF : F∈B.bankDefectFamily ht side) :
    (B.halfGraph side).faceSignedArea (B.halfGraph side).point (B.bankDefectPlaneFace ht side F hF)=
      G.faceSignedArea G.point F := by
  have hb := G.defectPlaneFace_isBounded ht (Finset.mem_filter.mp hF).1
  rw [(B.halfGraph side).faceSignedArea_eq_measure (B.bankDefectPlaneFace ht side F hF) hb,
    G.faceSignedArea_eq_measure F hb]
  rfl

theorem bankDefect_signed_area_lower (ht : G.TriangleFree) (side : Bool)
    (hdegree : ∀ v a,G.graph.Adj v a → ∃ b,G.graph.Adj v b ∧ b≠a)
    (F : PlaneFace G) (hF : F∈B.bankDefectFamily ht side) :
    Real.sqrt 3/2≤(B.halfGraph side).faceSignedArea (B.halfGraph side).point
      (B.bankDefectPlaneFace ht side F hF) := by
  rw [B.bankDefect_signed_area ht side F hF]
  exact G.defect_area_lower ht hdegree F (Finset.mem_filter.mp hF).1

end OrdinaryCutBanks
end Swanepoel
