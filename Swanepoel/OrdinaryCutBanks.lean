module
public import Swanepoel.SourceBankTransport
@[expose] public section

noncomputable section
namespace Swanepoel
open Set

structure OrdinaryCutBanks {n : ℕ} (G : PennyGraph n) (cut : TrackComponent G) where
  start : OrientedEdge G
  finish : OrientedEdge G
  component : edgeComponent start=cut
  source : SpineSource start
  sink : ¬∃g,PositiveCellStep finish g
  spine : PositiveSpineChain G start finish
  outer : PlaneFace G
  outer_unbounded : ¬Bornology.IsBounded outer.val
  loop : PlaneChain (edgeCenter start) (edgeCenter start)
  support : loop.trace⊆trackSpineTrace cut∪outer.val
  bank_difference : spine.bankLabel loop (-1)=spine.bankLabel loop 1+1

theorem exists_ordinaryCutBanks {n : ℕ} {G : PennyGraph n} (ht : G.TriangleFree)
    (cut other : TrackComponent G) (hcut : cut∈G.ordinaryTrackComponents)
    (hcross : ComponentCrosses cut other) : Nonempty (OrdinaryCutBanks G cut) := by
  obtain ⟨C,hC⟩ := hcross
  have hCt : edgeComponent C.edgeAB=cut ∨ edgeComponent C.edgeAD=cut := by tauto
  obtain ⟨a,b,hab,ha,_,_⟩ := C.spineWitness ht cut hCt
  obtain ⟨s,t,hs,htop,he,_⟩ := component_spine_iff ht a
  have hst := he.1.trans he.2
  have hsc : edgeComponent s=cut := (positive_path_component he.1).trans ha
  have hords : edgeComponent s∈G.ordinaryTrackComponents := hsc ▸ hcut
  obtain ⟨outer,houter,loop,_,hloop,hjumps⟩ :=
    G.ordinary_spine_single_loop_winding_jumps ht hs htop hst hords
  obtain ⟨p⟩ := PositiveSpineChain.exists_of_reach hst
  obtain ⟨ε,hε,hj⟩ := hjumps a b he hab
  have hd := p.bankLabel_difference ht hs htop outer houter loop hloop he hab ε hε
    (fun r hr hre => (hj r hr hre).2.2.1)
  exact ⟨⟨s,t,hsc,hs,htop,p,outer,houter,loop,by simpa only [hsc] using hloop,hd⟩⟩

namespace OrdinaryCutBanks
variable {n : ℕ} {G : PennyGraph n} {cut : TrackComponent G} (B : OrdinaryCutBanks G cut)

def vector : Plane := carriedVector B.start
def positiveLabel : ℤ := B.spine.bankLabel B.loop 1
def negativeLabel : ℤ := B.spine.bankLabel B.loop (-1)
def faceLabel (F : PlaneFace G) : ℤ := G.faceWindingLabel B.loop F
def vertexLabel (v : Fin n) : ℤ := B.loop.windingIndex (G.point v)

theorem vector_norm : ‖B.vector‖=1 := carriedVector_norm B.start

theorem labels_ne : B.positiveLabel≠B.negativeLabel := by
  have hh := B.bank_difference
  change B.negativeLabel=B.positiveLabel+1 at hh
  omega

theorem vector_sameLine (e : OrientedEdge G) (he : edgeComponent e=cut) :
    SameLine (carriedVector e) B.vector :=
  (component_sameLine e cut he).trans (component_sameLine B.start cut B.component).symm

theorem bankLabel_eq {z : Plane} (ht : G.TriangleFree) (sign : ℝ)
    (hsign : sign=1 ∨ sign= -1) (hz : z∈B.spine.bankRegion sign) :
    B.loop.windingIndex z=B.spine.bankLabel B.loop sign := by
  apply B.spine.bankLabel_constant ht B.source B.sink B.outer B.outer_unbounded B.loop
    (by simpa only [B.component] using B.support) sign hsign hz

theorem cut_edge_start_label {e : OrientedEdge G} (ht : G.TriangleFree)
    (he : edgeComponent e=cut) (sign : ℝ) (hsign : sign=1 ∨ sign= -1)
    (hvector : carriedVector e=(-sign) • B.vector) :
    B.vertexLabel e.val.1=B.spine.bankLabel B.loop sign := by
  apply B.bankLabel_eq ht sign hsign
  have hx : edgeCenter e∈B.spine.toPlane.trace := by
    rw [B.spine.complete_trace ht B.source B.sink,B.component]
    exact Or.inl ⟨e,he,rfl⟩
  refine ⟨edgeCenter e,hx,1/2,⟨by norm_num,le_rfl⟩,?_⟩
  change G.point e.val.1=edgeCenter e+(sign*(1/2)) • B.vector
  have hh : G.point e.val.1=edgeCenter e-(1/2:ℝ) • carriedVector e := by
    dsimp [edgeCenter,RhombusCell.midpoint2,carriedVector]
    module
  rw [hh,hvector]
  module

theorem cut_edge_start_label_of_eq {e : OrientedEdge G} (ht : G.TriangleFree)
    (he : edgeComponent e=cut) (hv : carriedVector e=B.vector) :
    B.vertexLabel e.val.1=B.negativeLabel := by
  exact B.cut_edge_start_label ht he (-1) (Or.inr rfl) (by simpa only [neg_neg,one_smul] using hv)

theorem cut_edge_start_label_of_neg {e : OrientedEdge G} (ht : G.TriangleFree)
    (he : edgeComponent e=cut) (hv : carriedVector e= -B.vector) :
    B.vertexLabel e.val.1=B.positiveLabel := by
  exact B.cut_edge_start_label ht he 1 (Or.inl rfl) (by simpa only [neg_one_smul] using hv)

theorem defect_source_vertex_label (ht : G.TriangleFree) (e : OrientedEdge G)
    (heF : G.sourceFace e∈G.defectPlaneFaces ht) :
    B.vertexLabel e.val.1=B.faceLabel (G.sourceFace e) :=
  G.defect_vertex_winding_label ht cut B.outer B.outer_unbounded B.loop B.support
    (G.sourceFace e) heF e.val.1 (G.sourceFace_endpoints_mem_closure e).1

theorem missing_source_face_labels_eq (ht : G.TriangleFree) (e f : OrientedEdge G)
    (he : SpineSource e) (hf : SpineSource f)
    (heF : G.sourceFace e∈G.defectPlaneFaces ht) (hfF : G.sourceFace f∈G.defectPlaneFaces ht)
    (hc : edgeComponent f=edgeComponent e) (hne : edgeComponent e≠cut)
    (hmiss : ¬ComponentCrosses (edgeComponent e) cut) :
    B.faceLabel (G.sourceFace e)=B.faceLabel (G.sourceFace f) :=
  G.noncrossing_defect_source_labels_eq ht cut B.outer B.outer_unbounded B.loop B.support
    e f he hf heF hfF hc hne hmiss

end OrdinaryCutBanks
end Swanepoel
