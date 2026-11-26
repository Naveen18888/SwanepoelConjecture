module
public import Swanepoel.DisplacementPotential
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

theorem linear_trackDisplacement_reverse {n : ℕ} {G : PennyGraph n}
    (w : TrackComponent G → ℝ) (L : Plane →ₗ[ℝ] Plane) (e : OrientedEdge G)
    (he : L (carriedVector e)=trackDisplacement w e) :
    L (carriedVector (reverseEdge e))=trackDisplacement w (reverseEdge e) := by
  rw [reverseEdge_vector,map_neg,trackDisplacement_reverse,he]

theorem linear_trackDisplacement_of_unordered_eq {n : ℕ} {G : PennyGraph n}
    (w : TrackComponent G → ℝ) (L : Plane →ₗ[ℝ] Plane) (e f : OrientedEdge G)
    (hf : L (carriedVector f)=trackDisplacement w f)
    (h : s(e.val.1,e.val.2)=s(f.val.1,f.val.2)) :
    L (carriedVector e)=trackDisplacement w e := by
  rcases Sym2.eq_iff.mp h with h | h
  · have he : e=f := Subtype.ext (Prod.ext h.1 h.2)
    simpa only [he] using hf
  · have he : e=reverseEdge f := Subtype.ext (Prod.ext h.1 h.2)
    rw [he]
    exact linear_trackDisplacement_reverse w L f hf

def RhombusCell.displacementLinear {n : ℕ} {G : PennyGraph n}
    (C : RhombusCell G) (w : TrackComponent G → ℝ) : Plane →ₗ[ℝ] Plane :=
  C.portCoordULinear.smulRight (trackDisplacement w C.edgeAB)+
    C.portCoordVLinear.smulRight (trackDisplacement w C.edgeAD)

theorem RhombusCell.displacementLinear_u {n : ℕ} {G : PennyGraph n}
    (C : RhombusCell G) (ht : G.TriangleFree) (w : TrackComponent G → ℝ) :
    C.displacementLinear w C.u=trackDisplacement w C.edgeAB := by
  simp [RhombusCell.displacementLinear,RhombusCell.portCoordULinear,
    RhombusCell.portCoordVLinear,C.cross_ne_zero ht,cross2_self]

theorem RhombusCell.displacementLinear_v {n : ℕ} {G : PennyGraph n}
    (C : RhombusCell G) (ht : G.TriangleFree) (w : TrackComponent G → ℝ) :
    C.displacementLinear w C.v=trackDisplacement w C.edgeAD := by
  simp [RhombusCell.displacementLinear,RhombusCell.portCoordULinear,
    RhombusCell.portCoordVLinear,C.cross_ne_zero ht,cross2_self]

theorem RhombusCell.displacementLinear_on_inside_edge {n : ℕ} {G : PennyGraph n}
    (C : RhombusCell G) (ht : G.TriangleFree) (w : TrackComponent G → ℝ)
    (e : OrientedEdge G) (ha : e.val.1∈C.corners) (hb : e.val.2∈C.corners) :
    C.displacementLinear w (carriedVector e)=trackDisplacement w e := by
  have hab : C.displacementLinear w (carriedVector C.edgeAB)=trackDisplacement w C.edgeAB :=
    C.displacementLinear_u ht w
  have had : C.displacementLinear w (carriedVector C.edgeAD)=trackDisplacement w C.edgeAD :=
    C.displacementLinear_v ht w
  have hbc : C.displacementLinear w (carriedVector C.edgeBC)=trackDisplacement w C.edgeBC := by
    have hs : CellStep C.edgeAD C.edgeBC := ⟨C.transpose,rfl,rfl⟩
    rw [← hs.vector_eq,← hs.trackDisplacement_eq w]
    exact had
  have hdc : C.displacementLinear w (carriedVector C.edgeDC)=trackDisplacement w C.edgeDC := by
    have hs : CellStep C.edgeAB C.edgeDC := ⟨C,rfl,rfl⟩
    rw [← hs.vector_eq,← hs.trackDisplacement_eq w]
    exact hab
  have hcd : C.displacementLinear w (carriedVector C.edgeCD)=trackDisplacement w C.edgeCD := by
    have he : C.edgeCD=reverseEdge C.edgeDC := by apply Subtype.ext; rfl
    rw [he]
    exact linear_trackDisplacement_reverse w _ _ hdc
  have hda : C.displacementLinear w (carriedVector C.edgeDA)=trackDisplacement w C.edgeDA := by
    have he : C.edgeDA=reverseEdge C.edgeAD := by apply Subtype.ext; rfl
    rw [he]
    exact linear_trackDisplacement_reverse w _ _ had
  rcases C.adj_inside ht _ _ ha hb e.property with h | h | h | h
  · exact linear_trackDisplacement_of_unordered_eq w _ e C.edgeAB hab h
  · exact linear_trackDisplacement_of_unordered_eq w _ e C.edgeBC hbc h
  · exact linear_trackDisplacement_of_unordered_eq w _ e C.edgeCD hcd h
  · exact linear_trackDisplacement_of_unordered_eq w _ e C.edgeDA hda h

def RhombusCell.displacementVertexMap {n : ℕ} {G : PennyGraph n}
    (C : RhombusCell G) (w : TrackComponent G → ℝ) (a : Fin n) : Plane :=
  C.displacementLinear w (G.point a-G.point C.a)

theorem RhombusCell.displacementVertexMap_edge {n : ℕ} {G : PennyGraph n}
    (C : RhombusCell G) (ht : G.TriangleFree) (w : TrackComponent G → ℝ)
    (e : OrientedEdge G) (ha : e.val.1∈C.corners) (hb : e.val.2∈C.corners) :
    C.displacementVertexMap w e.val.2-C.displacementVertexMap w e.val.1=trackDisplacement w e := by
  unfold RhombusCell.displacementVertexMap
  rw [← map_sub]
  have he : (G.point e.val.2-G.point C.a)-(G.point e.val.1-G.point C.a)=carriedVector e := by
    dsimp [carriedVector]
    abel
  rw [he]
  exact C.displacementLinear_on_inside_edge ht w e ha hb

theorem RhombusCell.retained_closed_walk_zero {n : ℕ} {G : PennyGraph n}
    (C : RhombusCell G) (ht : G.TriangleFree) (A : Finset (TrackComponent G))
    (S : Finset (ContactEdge G))
    (hS : ∀ {a b : Fin n}, (G.contactGraph S).Adj a b → a∈C.corners ∧ b∈C.corners)
    {a : Fin n} (p : (G.contactGraph S).Walk a a) :
    G.selectedWalkDisplacement A p=0 := by
  let w (c : TrackComponent G) : ℝ := if c∈A then 1 else 0
  rw [G.selectedWalkDisplacement_eq_potential A S (C.displacementVertexMap w) ?_ p,sub_self]
  intro x y h
  exact C.displacementVertexMap_edge ht w ⟨(x,y),G.contactGraph_le S h⟩ (hS h).1 (hS h).2

end Swanepoel
