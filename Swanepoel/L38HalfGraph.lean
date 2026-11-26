module
public import Swanepoel.Restrictions
public import Swanepoel.HalfPieceLocation
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable
namespace OrdinaryCutBanks
variable {n : ℕ} {G : PennyGraph n} {cut : TrackComponent G} (B : OrdinaryCutBanks G cut)

def vertexBankCode (v : Fin n) : Bool := decide (B.vertexLabel v=B.positiveLabel)

def bankVertices (side : Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun v => B.vertexBankCode v=side)

theorem mem_bankVertices (side : Bool) (v : Fin n) :
    v∈B.bankVertices side ↔ B.vertexBankCode v=side := by
  simp only [bankVertices,Finset.mem_filter,Finset.mem_univ,true_and]

def halfGraph (side : Bool) : PennyGraph (B.bankVertices side).card :=
  G.restrict (B.bankVertices side)

def halfVertex (side : Bool) (v : Fin (B.bankVertices side).card) : Fin n :=
  ((B.bankVertices side).equivFin.symm v).val

theorem halfVertex_injective (side : Bool) : Function.Injective (B.halfVertex side) := by
  intro i j h
  exact (B.bankVertices side).equivFin.symm.injective (Subtype.ext h)

theorem halfVertex_mem (side : Bool) (v : Fin (B.bankVertices side).card) :
    B.halfVertex side v∈B.bankVertices side := ((B.bankVertices side).equivFin.symm v).property

def halfVertexIndex (side : Bool) (v : Fin n) (hv : v∈B.bankVertices side) :
    Fin (B.bankVertices side).card := (B.bankVertices side).equivFin ⟨v,hv⟩

@[simp] theorem halfVertex_index (side : Bool) (v : Fin n) (hv : v∈B.bankVertices side) :
    B.halfVertex side (B.halfVertexIndex side v hv)=v := by
  exact congrArg Subtype.val ((B.bankVertices side).equivFin.symm_apply_apply ⟨v,hv⟩)

@[simp] theorem halfGraph_point (side : Bool) (v : Fin (B.bankVertices side).card) :
    (B.halfGraph side).point v=G.point (B.halfVertex side v) := rfl

theorem halfGraph_triangleFree (ht : G.TriangleFree) (side : Bool) :
    (B.halfGraph side).TriangleFree := G.restrict_triangleFree _ ht

theorem halfGraph_adj_iff (side : Bool) (i j : Fin (B.bankVertices side).card) :
    (B.halfGraph side).graph.Adj i j ↔ G.graph.Adj (B.halfVertex side i) (B.halfVertex side j) :=
  (G.restrictIso (B.bankVertices side)).map_rel_iff.symm

def halfEdge (side : Bool) (e : OrientedEdge (B.halfGraph side)) : OrientedEdge G :=
  ⟨(B.halfVertex side e.val.1,B.halfVertex side e.val.2),
    (B.halfGraph_adj_iff side _ _).mp e.property⟩

theorem halfEdge_injective (side : Bool) : Function.Injective (B.halfEdge side) := by
  intro e f h
  apply Subtype.ext
  apply Prod.ext
  · exact B.halfVertex_injective side (congrArg (fun e : OrientedEdge G => e.val.1) h)
  · exact B.halfVertex_injective side (congrArg (fun e : OrientedEdge G => e.val.2) h)

def liftHalfEdge (side : Bool) (e : OrientedEdge G)
    (ha : e.val.1∈B.bankVertices side) (hb : e.val.2∈B.bankVertices side) :
    OrientedEdge (B.halfGraph side) :=
  ⟨(B.halfVertexIndex side e.val.1 ha,B.halfVertexIndex side e.val.2 hb),
    (B.halfGraph_adj_iff side _ _).mpr (by simpa only [B.halfVertex_index] using e.property)⟩

@[simp] theorem halfEdge_lift (side : Bool) (e : OrientedEdge G)
    (ha : e.val.1∈B.bankVertices side) (hb : e.val.2∈B.bankVertices side) :
    B.halfEdge side (B.liftHalfEdge side e ha hb)=e := by
  apply Subtype.ext
  exact Prod.ext (B.halfVertex_index side _ ha) (B.halfVertex_index side _ hb)

@[simp] theorem halfEdge_reverse (side : Bool) (e : OrientedEdge (B.halfGraph side)) :
    B.halfEdge side (reverseEdge e)=reverseEdge (B.halfEdge side e) := rfl

@[simp] theorem halfEdge_vector (side : Bool) (e : OrientedEdge (B.halfGraph side)) :
    carriedVector (B.halfEdge side e)=carriedVector e := rfl

@[simp] theorem halfEdge_center (side : Bool) (e : OrientedEdge (B.halfGraph side)) :
    edgeCenter (B.halfEdge side e)=edgeCenter e := rfl

theorem halfGraph_drawing_subset (side : Bool) : (B.halfGraph side).drawing⊆G.drawing := by
  rintro z (⟨v,rfl⟩ | hz)
  · exact G.point_mem_drawing (B.halfVertex side v)
  · obtain ⟨e,he⟩ := Set.mem_iUnion.mp hz
    exact G.edgeTrace_subset_drawing _ _ (B.halfEdge side e).property he

theorem halfGraph_vertex_mem (side : Bool) (v : Fin n) (hv : v∈B.bankVertices side) :
    G.point v∈(B.halfGraph side).drawing := by
  simpa only [B.halfGraph_point,B.halfVertex_index] using
    (B.halfGraph side).point_mem_drawing (B.halfVertexIndex side v hv)

theorem halfGraph_edgeTrace_subset (side : Bool) (e : OrientedEdge G)
    (ha : e.val.1∈B.bankVertices side) (hb : e.val.2∈B.bankVertices side) :
    G.edgeTrace e.val.1 e.val.2⊆(B.halfGraph side).drawing := by
  have h := (B.halfGraph side).edgeTrace_subset_drawing _ _ (B.liftHalfEdge side e ha hb).property
  change G.edgeTrace (B.halfVertex side (B.halfVertexIndex side e.val.1 ha))
    (B.halfVertex side (B.halfVertexIndex side e.val.2 hb))⊆(B.halfGraph side).drawing at h
  simpa only [B.halfVertex_index] using h

theorem noncut_vertexBankCode_eq (ht : G.TriangleFree) (e : OrientedEdge G)
    (hne : edgeComponent e≠cut) : B.vertexBankCode e.val.1=B.vertexBankCode e.val.2 := by
  exact congrArg (fun z : ℤ => decide (z=B.positiveLabel))
    (G.noncut_edge_winding_equal ht cut B.outer B.loop B.support e hne)

theorem cut_vertexBankCode_ne (ht : G.TriangleFree) (e : OrientedEdge G)
    (he : edgeComponent e=cut) : B.vertexBankCode e.val.1≠B.vertexBankCode e.val.2 := by
  have hr : edgeComponent (reverseEdge e)=cut := (reverse_component e).symm.trans he
  rcases B.vector_sameLine e he with hv | hv
  · have ha := B.cut_edge_start_label_of_eq ht he hv
    have hb := B.cut_edge_start_label_of_neg ht hr (by rw [reverseEdge_vector,hv])
    change decide (B.vertexLabel e.val.1=B.positiveLabel)≠decide (B.vertexLabel e.val.2=B.positiveLabel)
    simp only [ha,show B.vertexLabel e.val.2=B.positiveLabel from hb,
      Ne.symm B.labels_ne,decide_false,decide_true]
    decide
  · have ha := B.cut_edge_start_label_of_neg ht he hv
    have hb := B.cut_edge_start_label_of_eq ht hr (by rw [reverseEdge_vector,hv,neg_neg])
    change decide (B.vertexLabel e.val.1=B.positiveLabel)≠decide (B.vertexLabel e.val.2=B.positiveLabel)
    simp only [ha,show B.vertexLabel e.val.2=B.negativeLabel from hb,
      Ne.symm B.labels_ne,decide_false,decide_true]
    decide

theorem halfEdge_ne_cut (ht : G.TriangleFree) (side : Bool)
    (e : OrientedEdge (B.halfGraph side)) : edgeComponent (B.halfEdge side e)≠cut := by
  intro h
  have hn := B.cut_vertexBankCode_ne ht _ h
  exact hn (((B.mem_bankVertices side _).mp (B.halfVertex_mem side e.val.1)).trans
    ((B.mem_bankVertices side _).mp (B.halfVertex_mem side e.val.2)).symm)

end OrdinaryCutBanks
end Swanepoel
