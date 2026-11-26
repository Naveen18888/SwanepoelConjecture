module
public import Swanepoel.L38HalfPentagonTracks
@[expose] public section

noncomputable section
namespace Swanepoel
attribute [local instance] Classical.propDecidable

namespace OrdinaryCutBanks
variable {n : ℕ} {G : PennyGraph n} {cut : TrackComponent G} (B : OrdinaryCutBanks G cut)

theorem half_old_cell_vertices_mem (ht : G.TriangleFree) (side : Bool)
    (e : OrientedEdge (B.halfGraph side)) (hs : SpineSource (B.halfEdge side e))
    (hmiss : ¬ComponentCrosses (edgeComponent (B.halfEdge side e)) cut)
    (C : RhombusCell G)
    (hC : edgeComponent C.edgeAB=edgeComponent (B.halfEdge side e) ∨
      edgeComponent C.edgeAD=edgeComponent (B.halfEdge side e)) :
    ∀ v∈C.corners,v∈B.bankVertices side := by
  obtain ⟨a,b,hab,ha,_,hcorners⟩ := C.spineWitness ht _ hC
  obtain ⟨a',ha'⟩ := B.half_full_component_retained ht side e hs hmiss a ha
  have hb : edgeComponent b=edgeComponent (B.halfEdge side e) :=
    (positive_path_component (Relation.ReflTransGen.single hab)).symm.trans ha
  obtain ⟨b',hb'⟩ := B.half_full_component_retained ht side e hs hmiss b hb
  have hva : a.val.1∈B.bankVertices side ∧ a.val.2∈B.bankVertices side := by
    rw [← ha']
    exact ⟨B.halfVertex_mem side a'.val.1,B.halfVertex_mem side a'.val.2⟩
  have hvb : b.val.1∈B.bankVertices side ∧ b.val.2∈B.bankVertices side := by
    rw [← hb']
    exact ⟨B.halfVertex_mem side b'.val.1,B.halfVertex_mem side b'.val.2⟩
  intro v hv
  rw [← hcorners] at hv
  simp only [stepCorners,Finset.mem_insert,Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl | rfl
  · exact hva.1
  · exact hva.2
  · exact hvb.1
  · exact hvb.2

def liftHalfPentagonCell (side : Bool) (C : RhombusCell G)
    (hv : ∀ v∈C.corners,v∈B.bankVertices side) : RhombusCell (B.halfGraph side) := by
  have ha : C.a∈B.bankVertices side := hv C.a (by simp [RhombusCell.corners])
  have hb : C.b∈B.bankVertices side := hv C.b (by simp [RhombusCell.corners])
  have hc : C.c∈B.bankVertices side := hv C.c (by simp [RhombusCell.corners])
  have hd : C.d∈B.bankVertices side := hv C.d (by simp [RhombusCell.corners])
  refine {
    a := B.halfVertexIndex side C.a ha
    b := B.halfVertexIndex side C.b hb
    c := B.halfVertexIndex side C.c hc
    d := B.halfVertexIndex side C.d hd
    ac := ?_
    bd := ?_
    ab := ?_
    bc := ?_
    cd := ?_
    da := ?_
  }
  · intro h
    apply C.ac
    simpa only [B.halfVertex_index] using congrArg (B.halfVertex side) h
  · intro h
    apply C.bd
    simpa only [B.halfVertex_index] using congrArg (B.halfVertex side) h
  · apply (B.halfGraph_adj_iff side _ _).mpr
    simpa only [B.halfVertex_index] using C.ab
  · apply (B.halfGraph_adj_iff side _ _).mpr
    simpa only [B.halfVertex_index] using C.bc
  · apply (B.halfGraph_adj_iff side _ _).mpr
    simpa only [B.halfVertex_index] using C.cd
  · apply (B.halfGraph_adj_iff side _ _).mpr
    simpa only [B.halfVertex_index] using C.da

theorem liftHalfPentagonCell_edgeAB (side : Bool) (C : RhombusCell G)
    (hv : ∀ v∈C.corners,v∈B.bankVertices side) :
    B.halfEdge side (B.liftHalfPentagonCell side C hv).edgeAB=C.edgeAB := by
  apply Subtype.ext
  exact Prod.ext (B.halfVertex_index side _ _) (B.halfVertex_index side _ _)

theorem liftHalfPentagonCell_edgeAD (side : Bool) (C : RhombusCell G)
    (hv : ∀ v∈C.corners,v∈B.bankVertices side) :
    B.halfEdge side (B.liftHalfPentagonCell side C hv).edgeAD=C.edgeAD := by
  apply Subtype.ext
  exact Prod.ext (B.halfVertex_index side _ _) (B.halfVertex_index side _ _)

theorem half_old_source_crossing_iff (ht : G.TriangleFree) (side : Bool)
    (e f : OrientedEdge (B.halfGraph side))
    (he : SpineSource (B.halfEdge side e)) (hf : SpineSource (B.halfEdge side f)) :
    ComponentCrosses (edgeComponent e) (edgeComponent f) ↔
      ComponentCrosses (edgeComponent (B.halfEdge side e)) (edgeComponent (B.halfEdge side f)) := by
  constructor
  · exact B.halfComponentMap_crossing side
  · intro hcross
    have hmiss : ¬ComponentCrosses (edgeComponent (B.halfEdge side e)) cut ∨
        ¬ComponentCrosses (edgeComponent (B.halfEdge side f)) cut := by
      by_cases hx : ComponentCrosses (edgeComponent (B.halfEdge side e)) cut
      · right
        exact componentGraph_noTriple G ht cut (edgeComponent (B.halfEdge side e))
          (edgeComponent (B.halfEdge side f)) ((componentGraph G ht).adj_symm hx) hcross
      · exact Or.inl hx
    obtain ⟨C,hC⟩ := hcross
    have hv : ∀ v∈C.corners,v∈B.bankVertices side := by
      rcases hmiss with hx | hx
      · apply B.half_old_cell_vertices_mem ht side e he hx C
        rcases hC with h | h
        · exact Or.inl h.1
        · exact Or.inr h.2
      · apply B.half_old_cell_vertices_mem ht side f hf hx C
        rcases hC with h | h
        · exact Or.inr h.2
        · exact Or.inl h.1
    let D := B.liftHalfPentagonCell side C hv
    refine ⟨D,?_⟩
    rcases hC with ⟨hc,hd⟩ | ⟨hc,hd⟩
    · left
      constructor
      · exact (B.half_component_eq_of_old_source ht side e D.edgeAB he (by
          rw [B.liftHalfPentagonCell_edgeAB]; exact hc)).symm
      · exact (B.half_component_eq_of_old_source ht side f D.edgeAD hf (by
          rw [B.liftHalfPentagonCell_edgeAD]; exact hd)).symm
    · right
      constructor
      · exact (B.half_component_eq_of_old_source ht side f D.edgeAB hf (by
          rw [B.liftHalfPentagonCell_edgeAB]; exact hc)).symm
      · exact (B.half_component_eq_of_old_source ht side e D.edgeAD he (by
          rw [B.liftHalfPentagonCell_edgeAD]; exact hd)).symm

end OrdinaryCutBanks
end Swanepoel
